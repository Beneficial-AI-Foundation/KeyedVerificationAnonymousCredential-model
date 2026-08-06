#!/usr/bin/env python3
"""Maintain the landing page's progress-over-time history JSON.

``update`` computes today's exact snapshot from the blueprint manifest and
merges three sources into ``<site>/blueprint-progress-history.json``:

    committed seed  ∪  previously deployed history  ∪  exact HEAD snapshot

- The **seed** (``docs/blueprint-progress-seed.json``) is a one-time,
  human-reviewed backfill; all its points carry ``"estimated": true``.
- The **previously deployed history** is fetched from the live site
  (opportunistic recovery only: retries, timeout, no-cache, size cap, schema
  validation). On any failure the merge degrades to seed + HEAD and sets
  ``degradedHistory`` so the dashboard shows a notice — exact points are never
  silently replaced by estimates, and merging never reduces the number of
  exact snapshots relative to what was recovered.
- The **HEAD snapshot** is exact, keyed by commit; an exact snapshot always
  wins over an estimated one for the same commit. Totals mismatches versus
  older snapshots are expected (the registry grows) and are recorded via the
  document's ``historyBasis``, never a reason to reseed.

Requires Python 3.11+. Stdlib only. Counter contracts are imported from
``blueprint_dashboard.py`` so the two scripts can never disagree.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import subprocess
import sys
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

SCHEMA_VERSION = 1
FETCH_TIMEOUT_SECONDS = 10
FETCH_RETRIES = 3
FETCH_MAX_BYTES = 5 * 1024 * 1024

_here = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("blueprint_dashboard", _here / "blueprint_dashboard.py")
_dash = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_dash)


class HistoryError(RuntimeError):
    pass


def git(*args: str) -> str:
    return subprocess.run(["git", *args], capture_output=True, text=True, check=True).stdout.strip()


def head_snapshot(site_dir: Path, commit: str | None, date: str | None) -> dict:
    nodes = _dash.load_nodes(site_dir)
    metrics = _dash.compute_snapshot_metrics(nodes)
    commit = commit or git("rev-parse", "HEAD")
    date = date or git("show", "-s", "--format=%cI", commit)
    snapshot = {
        "commit": commit,
        "shortCommit": commit[:9],
        "date": date,
        "source": "blueprint-manifest",
        "estimated": False,
        **metrics,
    }
    validate_snapshot(snapshot)
    return snapshot


def validate_snapshot(snap: dict) -> None:
    if not snap.get("commit") or not snap.get("date"):
        raise HistoryError(f"snapshot missing commit or date: {snap!r}")
    datetime.fromisoformat(str(snap["date"]).replace("Z", "+00:00"))
    if not isinstance(snap.get("estimated"), bool):
        raise HistoryError(f"snapshot {snap['commit'][:9]}: estimated must be an explicit boolean")
    if not isinstance(snap.get("source"), str) or not snap["source"]:
        raise HistoryError(f"snapshot {snap['commit'][:9]}: source must be a non-empty string")

    def as_count(value, name):
        if isinstance(value, bool) or not isinstance(value, int):
            raise HistoryError(f"snapshot {snap['commit'][:9]}: {name} must be an integer, got {value!r}")
        return value

    for kind in ("definitions", "theorems"):
        metrics = snap.get(kind)
        if not isinstance(metrics, dict):
            raise HistoryError(f"snapshot {snap['commit'][:9]} missing {kind}")
        total = as_count(metrics.get("total"), f"{kind}.total")
        specified = as_count(metrics.get("specified"), f"{kind}.specified")
        verified = as_count(
            metrics.get("verified", specified if kind == "definitions" else None), f"{kind}.verified"
        )
        if not (0 <= verified <= specified <= total):
            raise HistoryError(
                f"snapshot {snap['commit'][:9]} violates verified <= specified <= total for {kind}"
            )


def validate_document(doc: dict, origin: str) -> list[dict]:
    if not isinstance(doc, dict):
        raise HistoryError(f"{origin}: not a JSON object")
    if doc.get("schemaVersion") != SCHEMA_VERSION:
        raise HistoryError(f"{origin}: unsupported schemaVersion {doc.get('schemaVersion')!r}")
    snapshots = doc.get("snapshots")
    if not isinstance(snapshots, list):
        raise HistoryError(f"{origin}: snapshots is not a list")
    commits = set()
    for snap in snapshots:
        validate_snapshot(snap)
        if snap["commit"] in commits:
            raise HistoryError(f"{origin}: duplicate snapshot commit {snap['commit'][:9]}")
        commits.add(snap["commit"])
    return snapshots


def load_seed(seed_path: Path) -> dict:
    if not seed_path.is_file():
        raise HistoryError(f"seed file not found: {seed_path}")
    doc = json.loads(seed_path.read_text(encoding="utf-8"))
    validate_document(doc, str(seed_path))
    return doc


def fetch_previous(url: str) -> tuple[dict | None, bool]:
    """Return (document, degraded=False). A clean HTTP 404 is bootstrap (no
    previous deployment ever served the file). Any other recovery failure
    raises HistoryError and fails the run — by design, so a transient outage
    can never overwrite the live history with a lossy seed+HEAD document.
    Residual risk, documented in BLUEPRINT_MAINTENANCE.md: a post-bootstrap
    HTTP 404 (Pages serving 404 for a file it used to serve) is
    indistinguishable from bootstrap."""
    request = urllib.request.Request(url, headers={"Cache-Control": "no-cache", "Pragma": "no-cache"})
    last_error: Exception | None = None
    for _attempt in range(FETCH_RETRIES):
        try:
            with urllib.request.urlopen(request, timeout=FETCH_TIMEOUT_SECONDS) as response:
                raw = response.read(FETCH_MAX_BYTES + 1)
            if len(raw) > FETCH_MAX_BYTES:
                raise HistoryError(f"previous history exceeds {FETCH_MAX_BYTES} bytes")
            doc = json.loads(raw.decode("utf-8"))
            validate_document(doc, url)
            return doc, False
        except urllib.error.HTTPError as exc:
            if exc.code == 404:
                return None, False
            last_error = exc
        except Exception as exc:  # noqa: BLE001 - retried below
            last_error = exc
    # Anything other than a clean 404 means the live history exists but could
    # not be recovered. Publishing seed+HEAD over it would silently drop the
    # accumulated exact snapshots, so fail the deploy instead (it is retryable).
    raise HistoryError(f"previous history exists but could not be recovered: {last_error}")


def parse_time(raw: str) -> datetime:
    parsed = datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def merge(seed: dict, previous: dict | None, head: dict, degraded: bool) -> dict:
    by_commit: dict[str, dict] = {}

    def add(snap: dict) -> None:
        existing = by_commit.get(snap["commit"])
        if existing is None or (existing.get("estimated") and not snap.get("estimated")):
            by_commit[snap["commit"]] = snap

    for snap in seed.get("snapshots", []):
        add(snap)
    previous_exact = 0
    if previous is not None:
        for snap in previous.get("snapshots", []):
            add(snap)
        previous_exact = sum(1 for s in previous["snapshots"] if not s.get("estimated"))
    # The freshly computed HEAD snapshot always wins for its own commit — a
    # redeploy of the same commit must reflect the current manifest, not a
    # previously published measurement.
    by_commit[head["commit"]] = head

    snapshots = sorted(by_commit.values(), key=lambda s: parse_time(s["date"]))
    merged_exact = sum(1 for s in snapshots if not s.get("estimated"))
    if previous is not None and merged_exact < previous_exact:
        raise HistoryError(
            f"merge would reduce exact snapshots ({merged_exact} < {previous_exact}); refusing"
        )

    # Record registry-basis changes: whenever HEAD's totals differ from the
    # last preceding snapshot's, append a dated record (carried forward from
    # the previous document, deduplicated by date).
    basis_changes = list((previous or {}).get("basisChanges", []))
    older = [s for s in snapshots if s is not head]
    if older:
        last = older[-1]
        before = (last["definitions"]["total"], last["theorems"]["total"])
        after = (head["definitions"]["total"], head["theorems"]["total"])
        if before != after and not any(c.get("date") == head["date"] for c in basis_changes):
            basis_changes.append({
                "date": head["date"],
                "definitionsTotal": {"from": before[0], "to": after[0]},
                "theoremsTotal": {"from": before[1], "to": after[1]},
            })

    return {
        "schemaVersion": SCHEMA_VERSION,
        "historyBasis": seed.get("historyBasis", "unversioned"),
        "basisChanges": basis_changes,
        "projectStart": seed.get("projectStart") or snapshots[0]["date"],
        "updatedAt": head["date"],
        "degradedHistory": degraded,
        "snapshots": snapshots,
    }


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    update = sub.add_parser("update", help="merge seed + previous deployment + exact HEAD snapshot")
    update.add_argument("--site", required=True, type=Path)
    update.add_argument("--seed", type=Path, default=Path("docs/blueprint-progress-seed.json"))
    update.add_argument("--previous-url", help="URL of the previously deployed history JSON")
    update.add_argument("--previous-file", type=Path, help="local file standing in for --previous-url")
    update.add_argument("--output", type=Path)
    update.add_argument("--commit", help="override HEAD commit (e.g. GITHUB_SHA)")
    update.add_argument("--date", help="override snapshot ISO date (defaults to the commit date)")
    args = parser.parse_args(argv)

    output = args.output or args.site / "blueprint-progress-history.json"
    try:
        seed = load_seed(args.seed)
        previous, degraded = None, False
        if args.previous_file:
            if args.previous_file.is_file():
                doc = json.loads(args.previous_file.read_text(encoding="utf-8"))
                validate_document(doc, str(args.previous_file))
                previous = doc
        elif args.previous_url:
            previous, degraded = fetch_previous(args.previous_url)
        head = head_snapshot(args.site, args.commit, args.date)
        document = merge(seed, previous, head, degraded)
        output.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    except HistoryError as exc:
        print(f"blueprint_progress_history: {exc}", file=sys.stderr)
        return 1
    exact = sum(1 for s in document["snapshots"] if not s.get("estimated"))
    estimated = len(document["snapshots"]) - exact
    degraded = " (degraded: previous history unavailable)" if document["degradedHistory"] else ""
    print(f"wrote {output}: {exact} exact + {estimated} estimated snapshots{degraded}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
