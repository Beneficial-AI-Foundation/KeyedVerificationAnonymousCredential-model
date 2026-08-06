#!/usr/bin/env python3
"""Generate the site landing page (index.html) from the blueprint manifest.

Reads the Verso blueprint manifest emitted by the docs build
(``<site>/html-multi/-verso-data/blueprint-manifest.json``) plus the progress
history JSON, and writes a landing page showing the project's formalization
progress directly: overview counters, Definitions/Theorems step charts over
time, and a per-chapter breakdown table. Modeled on the secure-messaging
landing page (Beneficial-AI-Foundation/secure-messaging,
scripts/aggregate-blueprint-status.py), adapted to this repo's single-manual
layout and two-axis node statuses.

Counter contracts (all derived from Verso-computed statuses in
``graphs[0].nodes[]`` — this script never recomputes dependency closures):

- specified       statementStatus in {formalized, mathlib}
- verified        proofStatus in {formalized, formalizedWithAncestors}
- fully closed    proofStatus == formalizedWithAncestors
                  (matches the Blueprint Summary's "completed" / "Fully closed")
- deps pending    proofStatus == formalized
                  (matches the Blueprint Summary's "deps incomplete")
- ready           statementStatus == ready or proofStatus == ready
- sorries         proofStatus == incomplete

The page counts *blueprint registry entries* (paper elements plus milestones
and infrastructure nodes); chapters without registered entries are shown as
"no registry entries yet", never as complete.

Usage:
  blueprint_dashboard.py --site SITE_DIR
      [--history PATH]         default SITE_DIR/blueprint-progress-history.json
      [--output PATH]          default SITE_DIR/index.html
      [--check-links]          fail if an emitted node link has no file target
      [--conformance PATH]     compare counters against a rendered
                               Blueprint-Summary/index.html and fail on mismatch

Requires Python 3.11+. Stdlib only. Deterministic: output depends only on the
manifest and the history file.
"""

from __future__ import annotations

import argparse
import html
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

MANIFEST_RELPATH = Path("html-multi/-verso-data/blueprint-manifest.json")
SUPPORTED_MANIFEST_SCHEMA = 2
SUPPORTED_GRAPH_SCHEMA = 2

STATEMENT_STATUSES = {"blocked", "ready", "formalized", "mathlib"}
PROOF_STATUSES = {"none", "ready", "incomplete", "formalized", "formalizedWithAncestors"}
SPECIFIED_STATEMENT = {"formalized", "mathlib"}
VERIFIED_PROOF = {"formalized", "formalizedWithAncestors"}

DEFINITION_KINDS = {"definition"}
THEOREM_KINDS = {"theorem", "lemma", "proposition", "corollary"}

# Chapter slugs = first path component of node hrefs inside html-multi/.
# Display names/order mirror the manual's table of contents.
CHAPTER_ORDER = [
    "Core",
    "Preliminaries",
    "Proof-systems",
    "Framework-___-abstract-KVAC",
    "___CMZ",
    "___BBS",
    "Concrete-run",
]
CHAPTER_TITLES = {
    "Core": "Core",
    "Preliminaries": "Preliminaries",
    "Proof-systems": "Proof systems",
    "Framework-___-abstract-KVAC": "Framework — abstract KVAC",
    "___CMZ": "μCMZ",
    "___BBS": "μBBS",
    "Concrete-run": "Concrete run",
}

REPO_URL = "https://github.com/Beneficial-AI-Foundation/KeyedVerificationAnonymousCredential-model"
PAGE_TITLE = "KVAC — Lean Formalization"
PAGE_SUBTITLE = (
    "Machine-checked formalization of keyed-verification anonymous credentials, "
    "after Orrù (IACR ePrint 2024/1552)."
)

CHART_WIDTH = 1153
CHART_HEIGHT = 546
CHART_PAD_LEFT = 64
CHART_PAD_RIGHT = 28
CHART_PAD_TOP = 32
CHART_PAD_BOTTOM = 56


class DashboardError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# Manifest loading


class Node:
    __slots__ = ("label", "title", "kind", "href", "statement_status", "proof_status")

    def __init__(self, label, title, kind, href, statement_status, proof_status):
        self.label = label
        self.title = title
        self.kind = kind
        self.href = href
        self.statement_status = statement_status
        self.proof_status = proof_status

    @property
    def is_definition(self) -> bool:
        return self.kind in DEFINITION_KINDS

    @property
    def is_theorem_like(self) -> bool:
        return self.kind in THEOREM_KINDS

    @property
    def specified(self) -> bool:
        return self.statement_status in SPECIFIED_STATEMENT

    @property
    def verified(self) -> bool:
        return self.proof_status in VERIFIED_PROOF

    @property
    def fully_closed(self) -> bool:
        return self.proof_status == "formalizedWithAncestors"

    @property
    def deps_pending(self) -> bool:
        return self.proof_status == "formalized"

    @property
    def ready(self) -> bool:
        return self.statement_status == "ready" or self.proof_status == "ready"

    @property
    def has_sorries(self) -> bool:
        return self.proof_status == "incomplete"

    @property
    def chapter(self) -> str:
        return self.href.split("/", 1)[0]


def load_nodes(site_dir: Path) -> list[Node]:
    manifest_path = site_dir / MANIFEST_RELPATH
    if not manifest_path.is_file():
        raise DashboardError(f"manifest not found: {manifest_path}")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

    schema = manifest.get("vbpInternalSchemaVersion")
    if schema != SUPPORTED_MANIFEST_SCHEMA:
        raise DashboardError(f"unsupported manifest schema {schema!r}, expected {SUPPORTED_MANIFEST_SCHEMA}")
    graphs = manifest.get("graphs") or []
    if len(graphs) != 1:
        raise DashboardError(f"expected exactly one graph in the manifest, found {len(graphs)}")
    graph = graphs[0]
    if graph.get("schemaVersion") != SUPPORTED_GRAPH_SCHEMA:
        raise DashboardError(f"unsupported graph schema {graph.get('schemaVersion')!r}")

    previews_by_key: dict[str, dict] = {}
    for entry in manifest.get("previews", []):
        key = entry.get("key")
        if key is not None:
            if key in previews_by_key:
                raise DashboardError(f"duplicate preview key {key!r}")
            previews_by_key[key] = entry

    nodes: list[Node] = []
    seen_labels: set[str] = set()
    for raw in graph.get("nodes", []):
        label = raw.get("label")
        if not label:
            raise DashboardError(f"graph node without label: {raw!r}")
        if label in seen_labels:
            raise DashboardError(f"duplicate graph node label {label!r}")
        seen_labels.add(label)

        kind = raw.get("kind")
        if kind not in DEFINITION_KINDS | THEOREM_KINDS:
            raise DashboardError(f"node {label!r} has unsupported kind {kind!r}")
        href = raw.get("href")
        if not href:
            raise DashboardError(f"node {label!r} has no href")
        statement_status = raw.get("statementStatus")
        if statement_status not in STATEMENT_STATUSES:
            raise DashboardError(f"node {label!r} has unknown statementStatus {statement_status!r}")
        proof_status = raw.get("proofStatus")
        if proof_status not in PROOF_STATUSES:
            raise DashboardError(f"node {label!r} has unknown proofStatus {proof_status!r}")

        preview_key = raw.get("previewKey")
        if not preview_key:
            raise DashboardError(f"node {label!r} has no previewKey")
        preview = previews_by_key.get(preview_key)
        if preview is None:
            raise DashboardError(f"node {label!r} previewKey {preview_key!r} has no matching preview")
        title = preview.get("title") or raw.get("title") or label

        node = Node(label, title, kind, href, statement_status, proof_status)
        if node.chapter not in CHAPTER_TITLES:
            raise DashboardError(
                f"node {label!r} maps to unknown chapter slug {node.chapter!r}; "
                f"update CHAPTER_ORDER/CHAPTER_TITLES"
            )
        nodes.append(node)

    if not nodes:
        raise DashboardError("manifest contains no graph nodes")
    return nodes


# ---------------------------------------------------------------------------
# History loading


def load_history(history_path: Path) -> dict:
    if not history_path.is_file():
        raise DashboardError(f"history file not found: {history_path}")
    doc = json.loads(history_path.read_text(encoding="utf-8"))
    snapshots = doc.get("snapshots")
    if not isinstance(snapshots, list) or not snapshots:
        raise DashboardError("history has no snapshots")
    seen_commits: set[str] = set()
    for snap in snapshots:
        commit = snap.get("commit")
        if not commit:
            raise DashboardError(f"snapshot without commit: {snap!r}")
        if commit in seen_commits:
            raise DashboardError(f"duplicate snapshot commit {commit!r}")
        seen_commits.add(commit)
        snapshot_time(snap)  # validates the date
        for kind in ("definitions", "theorems"):
            metrics = snap.get(kind) or {}
            total = metrics.get("total", 0)
            specified = metrics.get("specified", 0)
            verified = metrics.get("verified", specified if kind == "definitions" else 0)
            if not (0 <= verified <= specified <= total):
                raise DashboardError(
                    f"snapshot {commit[:9]} violates verified <= specified <= total for {kind}: {metrics!r}"
                )
    doc["snapshots"] = sorted(snapshots, key=lambda s: snapshot_time(s))
    return doc


def parse_iso_utc(raw) -> datetime:
    try:
        parsed = datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
    except ValueError as exc:
        raise DashboardError(f"unparsable date {raw!r}") from exc
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def snapshot_time(snap: dict) -> datetime:
    return parse_iso_utc(snap.get("date"))


def metric_value(snap: dict, kind: str, metric: str) -> int:
    return int((snap.get(kind) or {}).get(metric, 0))


# ---------------------------------------------------------------------------
# Charts (step charts; estimated segments dashed, exact points filled)


def chart_window(doc: dict, snapshots: list[dict]) -> tuple[datetime, datetime]:
    start_raw = doc.get("projectStart")
    start = parse_iso_utc(start_raw) if start_raw else snapshot_time(snapshots[0])
    end = snapshot_time(snapshots[-1])
    updated = doc.get("updatedAt")
    if updated:
        end = max(end, parse_iso_utc(updated))
    if end <= start:
        end = start
    return start, end


def x_position(time: datetime, window: tuple[datetime, datetime]) -> float:
    start, end = window
    span = max((end - start).total_seconds(), 1.0)
    frac = min(max((time - start).total_seconds() / span, 0.0), 1.0)
    return CHART_PAD_LEFT + frac * (CHART_WIDTH - CHART_PAD_LEFT - CHART_PAD_RIGHT)


def y_position(value: int, max_value: int) -> float:
    plot = CHART_HEIGHT - CHART_PAD_TOP - CHART_PAD_BOTTOM
    return CHART_PAD_TOP + plot * (1 - value / max_value)


def chart_max_value(value: int) -> int:
    return max(5, ((value + 4) // 5) * 5)


def step_path(points: list[tuple[float, float]]) -> str:
    if not points:
        return ""
    parts = [f"M {points[0][0]:.1f} {points[0][1]:.1f}"]
    for (x0, y0), (x1, y1) in zip(points, points[1:]):
        parts.append(f"H {x1:.1f}")
        if y1 != y0:
            parts.append(f"V {y1:.1f}")
    return " ".join(parts)


def chart_gridlines(max_value: int) -> str:
    step = 5 if max_value <= 30 else 10
    lines = []
    for value in range(step, max_value + 1, step):
        y = y_position(value, max_value)
        lines.append(
            f'<g class="grid"><line x1="{CHART_PAD_LEFT}" y1="{y:.1f}" '
            f'x2="{CHART_WIDTH - CHART_PAD_RIGHT}" y2="{y:.1f}"/>'
            f'<text x="{CHART_PAD_LEFT - 8}" y="{y + 4:.1f}">{value}</text></g>'
        )
    return "".join(lines)


def chart_month_ticks(window: tuple[datetime, datetime]) -> str:
    start, end = window
    ticks = []
    year, month = start.year, start.month
    while True:
        month += 1
        if month == 13:
            month, year = 1, year + 1
        tick = datetime(year, month, 1, tzinfo=timezone.utc)
        if tick > end:
            break
        x = x_position(tick, window)
        label = tick.strftime("%b")
        ticks.append(
            f'<g class="tick"><line x1="{x:.1f}" y1="{CHART_HEIGHT - CHART_PAD_BOTTOM}" '
            f'x2="{x:.1f}" y2="{CHART_HEIGHT - CHART_PAD_BOTTOM + 6}"/>'
            f'<text x="{x:.1f}" y="{CHART_HEIGHT - CHART_PAD_BOTTOM + 24}">{label}</text></g>'
        )
    return "".join(ticks)


def metric_markup(snapshots: list[dict], kind: str, metric: str, css: str,
                  max_value: int, window: tuple[datetime, datetime]) -> str:
    pts = [(x_position(snapshot_time(s), window), y_position(metric_value(s, kind, metric), max_value), s)
           for s in snapshots]
    parts = []
    # Split into runs by estimated flag so estimated segments render dashed.
    for i in range(len(pts) - 1):
        (x0, y0, s0), (x1, y1, _s1) = pts[i], pts[i + 1]
        estimated = bool(s0.get("estimated"))
        cls = f"line {css}" + (" estimated" if estimated else "")
        seg = step_path([(x0, y0), (x1, y1)])
        parts.append(f'<path class="{cls}" d="{html.escape(seg, quote=True)}"/>')
    for x, y, s in pts:
        estimated = bool(s.get("estimated"))
        cls = f"pt {css}" + (" estimated" if estimated else "")
        date_text = snapshot_time(s).strftime("%Y-%m-%d")
        value = metric_value(s, kind, metric)
        source = s.get("source", "exact")
        flag = "estimated" if estimated else "exact"
        tooltip = html.escape(f"{date_text} · {metric} {value} · {flag} ({source})")
        parts.append(f'<circle class="{cls}" cx="{x:.1f}" cy="{y:.1f}" r="4"><title>{tooltip}</title></circle>')
    return "".join(parts)


def progress_chart(title: str, kind: str, metrics: list[tuple[str, str]],
                   snapshots: list[dict], window: tuple[datetime, datetime], max_value: int) -> str:
    latest = snapshots[-1]
    legend = [f'<span><i class="swatch total"></i>Total {metric_value(latest, kind, "total")}</span>']
    body = [metric_markup(snapshots, kind, "total", "total", max_value, window)]
    for metric, css in metrics:
        body.append(metric_markup(snapshots, kind, metric, css, max_value, window))
        legend.append(f'<span><i class="swatch {css}"></i>{metric.title()} {metric_value(latest, kind, metric)}</span>')
    start, end = window
    legend.append(f'<span class="timeframe">{start.strftime("%-d %b")} – {end.strftime("%-d %b %Y")}</span>')
    return f"""
      <article class="chart-card">
        <h3>{html.escape(title)}</h3>
        <svg viewBox="0 0 {CHART_WIDTH} {CHART_HEIGHT}" role="img" aria-label="{html.escape(title)} progress over time">
          <line class="axis" x1="{CHART_PAD_LEFT}" y1="{CHART_HEIGHT - CHART_PAD_BOTTOM}" x2="{CHART_WIDTH - CHART_PAD_RIGHT}" y2="{CHART_HEIGHT - CHART_PAD_BOTTOM}"/>
          <line class="axis" x1="{CHART_PAD_LEFT}" y1="{CHART_PAD_TOP}" x2="{CHART_PAD_LEFT}" y2="{CHART_HEIGHT - CHART_PAD_BOTTOM}"/>
          {chart_gridlines(max_value)}
          {chart_month_ticks(window)}
          {''.join(body)}
        </svg>
        <div class="legend">{''.join(legend)}</div>
      </article>"""


def charts_section(history: dict) -> str:
    snapshots = history["snapshots"]
    window = chart_window(history, snapshots)
    max_value = chart_max_value(max(
        metric_value(s, kind, "total") for s in snapshots for kind in ("definitions", "theorems")
    ))
    caption = ("Dashed segments and hollow markers are estimates reconstructed from git history, "
               "measured against today's registry as a fixed basis (the registry itself is newer "
               "than the project); solid segments are exact per-deployment measurements.")
    degraded = ('<p class="degraded">Live history could not be recovered for this build; '
                'the chart shows the committed seed plus the current exact snapshot.</p>'
                if history.get("degradedHistory") else "")
    return f"""
    <section class="charts" aria-label="Progress over time">
      <div class="chart-grid">
        {progress_chart("Definitions", "definitions", [("specified", "specified")], snapshots, window, max_value)}
        {progress_chart("Theorems", "theorems", [("specified", "specified"), ("verified", "verified")], snapshots, window, max_value)}
      </div>
      <p class="chart-note">{caption}</p>
      {degraded}
    </section>"""


# ---------------------------------------------------------------------------
# Counters and chapter table


def count(nodes: list[Node], pred) -> list[Node]:
    return [n for n in nodes if pred(n)]


def counters_section(nodes: list[Node]) -> str:
    fully_closed = count(nodes, lambda n: n.fully_closed)
    ready = count(nodes, lambda n: n.ready)
    sorries = count(nodes, lambda n: n.has_sorries)
    cards = [
        ("Registry entries", len(nodes), "paper elements, milestones, and infrastructure nodes"),
        ("Fully closed", len(fully_closed), "formalized with the whole dependency closure complete"),
        ("Ready to start", len(ready), "statement or proof work currently unblocked"),
    ]
    if sorries:
        cards.append(("With sorries", len(sorries), "Lean code present but incomplete"))
    rendered = "".join(
        f'<div class="counter"><span class="num">{value}</span>'
        f'<span class="name">{html.escape(name)}</span>'
        f'<span class="hint">{html.escape(hint)}</span></div>'
        for name, value, hint in cards
    )
    return f'<section class="counters" aria-label="Overview">{rendered}</section>'


def node_link(node: Node) -> str:
    return f'<a href="html-multi/{html.escape(node.href, quote=True)}">{html.escape(node.title)}</a>'


def cell(nodes: list[Node], cell_id: str) -> str:
    if not nodes:
        return '<td class="zero">0</td>'
    items = "".join(f"<li>{node_link(n)}</li>" for n in sorted(nodes, key=lambda n: n.title))
    return (
        f'<td class="has-pop"><span class="cellnum" tabindex="0">{len(nodes)}</span>'
        f'<div class="pop" role="tooltip" id="pop-{cell_id}"><ul>{items}</ul></div></td>'
    )


def chapter_table(nodes: list[Node]) -> str:
    rows = []
    for i, slug in enumerate(CHAPTER_ORDER):
        chapter_nodes = [n for n in nodes if n.chapter == slug]
        title = html.escape(CHAPTER_TITLES[slug])
        link = f'<a href="html-multi/{html.escape(slug, quote=True)}/">{title}</a>'
        if not chapter_nodes:
            rows.append(
                f'<tr><th scope="row">{link}</th>'
                f'<td class="empty-chapter" colspan="7">no registry entries yet</td></tr>'
            )
            continue
        defs = [n for n in chapter_nodes if n.is_definition]
        thms = [n for n in chapter_nodes if n.is_theorem_like]
        cells = [
            cell(defs, f"{i}d"),
            cell([n for n in defs if n.specified], f"{i}ds"),
            cell([n for n in defs if n.ready], f"{i}dr"),
            cell(thms, f"{i}t"),
            cell([n for n in thms if n.specified], f"{i}ts"),
            cell([n for n in thms if n.verified], f"{i}tv"),
            cell([n for n in thms if n.ready], f"{i}tr"),
        ]
        rows.append(f'<tr><th scope="row">{link}</th>{"".join(cells)}</tr>')
    return f"""
    <section class="chapters-section" aria-label="Per-chapter breakdown">
      <h2>By chapter</h2>
      <div class="table-scroll"><table class="chapters">
        <thead>
          <tr><th rowspan="2">Chapter</th><th colspan="3">Definitions</th><th colspan="4">Theorems</th></tr>
          <tr><th>Total</th><th>Specified</th><th>Ready next</th>
              <th>Total</th><th>Specified</th><th>Verified</th><th>Ready next</th></tr>
        </thead>
        <tbody>{''.join(rows)}</tbody>
      </table></div>
      <p class="scope-note">Counts are blueprint registry entries: the paper elements in the committed
      formalization scope plus internal milestones and infrastructure. Chapters marked
      “no registry entries yet” have planned work that is not yet registered — the absence of
      numbers means unregistered, not complete.</p>
    </section>"""


def links_section() -> str:
    cards = [
        ("html-multi/", "Documentation",
         "Framework, μCMZ, and μBBS specifications, chapter by chapter."),
        ("html-multi/Dependency-Graph/", "Dependency graph",
         "The paper's elements and their dependencies, with live formalization status."),
        ("html-multi/Blueprint-Summary/", "Blueprint summary",
         "Progress counts, blockers, and the next ready work items."),
        (REPO_URL, "Source on GitHub",
         "Lean sources, issues, and pull requests."),
    ]
    rendered = "".join(
        f'<a class="linkcard" href="{html.escape(href, quote=True)}">'
        f'<span class="linkname">{html.escape(name)}</span>'
        f'<span class="linkdesc">{html.escape(desc)}</span></a>'
        for href, name, desc in cards
    )
    return f'<section class="links" aria-label="Site sections">{rendered}</section>'


# ---------------------------------------------------------------------------
# Page assembly

CSS = """
:root { --fg: #1f2937; --muted: #6b7280; --line: #e5e7eb; --accent: #0f766e;
        --total: #9ca3af; --specified: #0ea5e9; --verified: #16a34a; --bg: #ffffff; }
* { box-sizing: border-box; }
body { margin: 0; font: 16px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif;
       color: var(--fg); background: var(--bg); }
main { max-width: 1180px; margin: 0 auto; padding: 2.5rem 1.25rem 4rem; }
header h1 { margin: 0 0 .25rem; font-size: 1.9rem; }
header p.sub { margin: 0 0 2rem; color: var(--muted); }
.counters { display: flex; flex-wrap: wrap; gap: 1rem; margin-bottom: 2rem; }
.counter { flex: 1 1 10rem; border: 1px solid var(--line); border-radius: .6rem; padding: .9rem 1rem; }
.counter .num { display: block; font-size: 1.8rem; font-weight: 650; }
.counter .name { display: block; font-weight: 600; margin-top: .1rem; }
.counter .hint { display: block; color: var(--muted); font-size: .82rem; margin-top: .15rem; }
.chart-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(24rem, 1fr)); gap: 1.25rem; }
.chart-card { border: 1px solid var(--line); border-radius: .6rem; padding: 1rem; }
.chart-card h3 { margin: 0 0 .5rem; }
.chart-card svg { width: 100%; height: auto; }
svg .axis { stroke: var(--fg); stroke-width: 1.5; }
svg .grid line { stroke: var(--line); }
svg .grid text, svg .tick text { fill: var(--muted); font-size: 20px; text-anchor: end; }
svg .tick text { text-anchor: middle; }
svg .tick line { stroke: var(--muted); }
svg .line { fill: none; stroke-width: 3.5; }
svg .line.total { stroke: var(--total); }
svg .line.specified { stroke: var(--specified); }
svg .line.verified { stroke: var(--verified); }
svg .line.estimated { stroke-dasharray: 7 6; }
svg .pt { stroke-width: 2.5; }
svg .pt.total { fill: var(--total); stroke: var(--total); }
svg .pt.specified { fill: var(--specified); stroke: var(--specified); }
svg .pt.verified { fill: var(--verified); stroke: var(--verified); }
svg .pt.estimated { fill: var(--bg); }
.legend { display: flex; flex-wrap: wrap; gap: 1rem; margin-top: .5rem; font-size: .9rem; }
.legend .swatch { display: inline-block; width: .85rem; height: .3rem; border-radius: .15rem;
                  margin-right: .4rem; vertical-align: middle; }
.legend .swatch.total { background: var(--total); }
.legend .swatch.specified { background: var(--specified); }
.legend .swatch.verified { background: var(--verified); }
.legend .timeframe { margin-left: auto; color: var(--muted); }
.chart-note, .scope-note { color: var(--muted); font-size: .85rem; }
.degraded { color: #b45309; font-size: .85rem; }
.chapters-section h2 { margin: 2.2rem 0 .8rem; font-size: 1.25rem; }
.table-scroll { overflow-x: auto; }
table.chapters { border-collapse: collapse; width: 100%; }
table.chapters th, table.chapters td { border: 1px solid var(--line); padding: .45rem .7rem; text-align: center; }
table.chapters thead th { background: #f9fafb; }
table.chapters tbody th { text-align: left; white-space: nowrap; }
td.zero { color: var(--muted); }
td.empty-chapter { color: var(--muted); font-style: italic; text-align: left; }
td.has-pop { position: relative; }
td.has-pop .cellnum { cursor: default; border-bottom: 1px dotted var(--muted); }
td.has-pop .pop { display: none; position: absolute; z-index: 5; left: 50%; transform: translateX(-50%);
  top: calc(100% + 4px); background: var(--bg); border: 1px solid var(--line); border-radius: .5rem;
  box-shadow: 0 8px 22px rgba(0,0,0,.12); padding: .5rem .8rem; min-width: 16rem; text-align: left; }
td.has-pop:hover .pop, td.has-pop:focus-within .pop { display: block; }
td.has-pop .pop ul { margin: 0; padding-left: 1.1rem; }
a { color: var(--accent); }
.links { display: grid; grid-template-columns: repeat(auto-fit, minmax(15rem, 1fr)); gap: 1rem; margin-top: 2.4rem; }
.linkcard { display: block; border: 1px solid var(--line); border-radius: .6rem; padding: 1rem;
            text-decoration: none; color: var(--fg); }
.linkcard:hover { border-color: var(--accent); }
.linkcard .linkname { display: block; font-weight: 650; color: var(--accent); }
.linkcard .linkdesc { display: block; color: var(--muted); font-size: .88rem; margin-top: .2rem; }
footer { margin-top: 3rem; color: var(--muted); font-size: .85rem; }
"""


def render_page(nodes: list[Node], history: dict) -> str:
    updated = history.get("updatedAt", "")
    updated_line = (
        f'<footer>Data from the blueprint manifest at deployment time · history updated {html.escape(str(updated)[:10])} · '
        f'<a href="blueprint-progress-history.json">progress history JSON</a></footer>'
        if updated else "<footer></footer>"
    )
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{html.escape(PAGE_TITLE)}</title>
<style>{CSS}</style>
</head>
<body>
<main>
  <header>
    <h1>{html.escape(PAGE_TITLE)}</h1>
    <p class="sub">{html.escape(PAGE_SUBTITLE)}</p>
  </header>
  {counters_section(nodes)}
  {charts_section(history)}
  {chapter_table(nodes)}
  {links_section()}
  {updated_line}
</main>
</body>
</html>
"""


# ---------------------------------------------------------------------------
# CI helpers


def check_links(nodes: list[Node], site_dir: Path) -> None:
    missing = []
    root = (site_dir / "html-multi").resolve()
    for node in nodes:
        target = node.href.split("#", 1)[0]
        path = (root / target).resolve()
        if not path.is_relative_to(root):
            missing.append(f"{node.label}: escapes html-multi/: {node.href}")
            continue
        candidate = path if path.suffix else path / "index.html"
        if not candidate.exists():
            missing.append(f"{node.label}: html-multi/{node.href}")
    static_targets = ["", "Dependency-Graph", "Blueprint-Summary", *CHAPTER_ORDER]
    for slug in static_targets:
        if not (root / slug / "index.html").exists():
            missing.append(f"section: html-multi/{slug}/")
    if missing:
        raise DashboardError("broken landing links:\n  " + "\n  ".join(missing))


def check_conformance(nodes: list[Node], summary_html_path: Path) -> None:
    """Compare our counters against the rendered Blueprint-Summary page.

    Compared: total entries, completed (= our fully closed), deps incomplete,
    sorries — the metrics with identical semantics on both pages. Deliberately
    NOT compared: the Summary's "Ready now" (actionable-stage gated) versus
    our "Ready to start" (either axis `ready`; matches the table's Ready-next
    columns), and "no proof" (counts theorem-like stubs only, while our
    per-axis statuses cover definitions too). Both exclusions are documented
    in BLUEPRINT_MAINTENANCE.md."""
    text = summary_html_path.read_text(encoding="utf-8")
    match = re.search(
        r"completed:\s*(\d+);\s*deps incomplete:\s*(\d+);\s*sorries:\s*(\d+);\s*no proof:\s*(\d+)", text
    )
    if not match:
        raise DashboardError(f"could not find status counts line in {summary_html_path}")
    total_match = re.search(r"Total entries</span>\s*<span[^>]*>(\d+)", text) or re.search(
        r"Total entries.{0,120}?(\d+)", text, re.DOTALL
    )
    if not total_match:
        raise DashboardError(f"could not find Total entries in {summary_html_path}")
    ours = {
        "total entries": len(nodes),
        "completed": len(count(nodes, lambda n: n.fully_closed)),
        "deps incomplete": len(count(nodes, lambda n: n.deps_pending)),
        "sorries": len(count(nodes, lambda n: n.has_sorries)),
    }
    theirs = {
        "total entries": int(total_match.group(1)),
        "completed": int(match.group(1)),
        "deps incomplete": int(match.group(2)),
        "sorries": int(match.group(3)),
    }
    if ours != theirs:
        raise DashboardError(f"counter conformance failed: dashboard {ours} vs Blueprint Summary {theirs}")


def compute_snapshot_metrics(nodes: list[Node]) -> dict:
    """Shared with blueprint_progress_history.py: today's exact metrics."""
    defs = [n for n in nodes if n.is_definition]
    thms = [n for n in nodes if n.is_theorem_like]
    return {
        "definitions": {
            "total": len(defs),
            "specified": len([n for n in defs if n.specified]),
        },
        "theorems": {
            "total": len(thms),
            "specified": len([n for n in thms if n.specified]),
            "verified": len([n for n in thms if n.verified]),
        },
    }


# ---------------------------------------------------------------------------


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", required=True, type=Path)
    parser.add_argument("--history", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-links", action="store_true")
    parser.add_argument("--conformance", type=Path)
    args = parser.parse_args(argv)

    site_dir: Path = args.site
    history_path = args.history or site_dir / "blueprint-progress-history.json"
    output_path = args.output or site_dir / "index.html"

    try:
        nodes = load_nodes(site_dir)
        history = load_history(history_path)
        if args.check_links:
            check_links(nodes, site_dir)
        if args.conformance:
            check_conformance(nodes, args.conformance)
        output_path.write_text(render_page(nodes, history), encoding="utf-8")
    except DashboardError as exc:
        print(f"blueprint_dashboard: {exc}", file=sys.stderr)
        return 1
    print(f"wrote {output_path} ({len(nodes)} registry entries)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
