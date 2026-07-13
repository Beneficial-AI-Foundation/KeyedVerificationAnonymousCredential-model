#!/usr/bin/env python3
"""Map a paper's elements to Lean declarations and emit a progress table.

The script is parameterized by a **source of truth**: the paper whose
definitions, lemmas, theorems and figures the Lean code formalises. The Lean
sources cite that paper with a fixed tag (``O24`` for Orrù 2024) inside
docstrings and module docs, e.g.:

    Definition 3.1 | Theorem 5.1 | Lemma 5.4 | Figure 5 | §5.1 | §3 ...

This script:

1. Extracts the paper element universe (numbered environments, figure captions,
   TOC sections) from the committed text extraction of the source PDF (see
   ``extract`` below).
2. Extracts Lean declarations (def/structure/abbrev/class/instance/lemma/
   theorem/inductive) and the citation references attached to each, both at the
   declaration level (preceding ``/-- -/`` docstring + signature) and the file
   level (module ``/-! -/`` doc).
3. Joins them on a canonical reference key and writes a Markdown progress table
   plus a JSON intermediate.

The source of truth is resolved from (lowest to highest precedence): the
built-in :data:`DEFAULT_SOURCE`, an optional TOML config file (``--config``),
then individual CLI flags. This keeps zero-argument runs and CI working while
letting the same tool target a different paper.

It is dependency-free (standard library only; ``tomllib`` ships with Python
3.11+) so it can run in CI. ``report`` and ``--check`` read the **committed**
text extraction of the paper (the ``text`` source field), so they never run
``pdftotext`` and are deterministic across machines. The ``pdftotext`` binary
(poppler-utils) is needed only for ``extract`` and ``init``, which run once
per paper.

Usage (run from the repository root):
    P=docs/formalization-progress/formalization_progress.py

    # Generate the source-of-truth TOML from a paper file and its URL:
    python3 $P init --pdf docs/Orru_2024.pdf --url https://eprint.iacr.org/2024/1552

    # Extract the paper text once and commit it (requires pdftotext):
    python3 $P extract --config s.toml

    # Generate the progress table (`report` is the default subcommand):
    python3 $P                  # built-in default source
    python3 $P --config s.toml  # a configured source
    python3 $P --check          # non-zero exit if stale
"""
from __future__ import annotations

import argparse
import functools
import json
import os
import re
import subprocess
import sys
import tomllib
import urllib.error
import urllib.request
from dataclasses import dataclass, field, asdict, replace
from pathlib import Path

def _find_repo_root(start: Path) -> Path:
    """Walk up from ``start`` to the repository root.

    Prefer the ``.git`` marker (only the checkout root has it); the ``docs/``
    Verso project carries its own ``lakefile.toml``, so that marker alone would
    stop too early. Fall back to the nearest lakefile.toml, then to ``start``."""
    for p in [start, *start.parents]:
        if (p / ".git").exists():
            return p
    for p in [start, *start.parents]:
        if (p / "lakefile.toml").exists():
            return p
    return start.parent


REPO = _find_repo_root(Path(__file__).resolve().parent)
PROGRESS_DIR = REPO / "docs" / "formalization-progress"
# This script's own path, relative to the repo root, for use in messages.
SCRIPT_REL = os.path.relpath(Path(__file__).resolve(), REPO)


@dataclass
class Source:
    """A paper acting as the source of truth, and where to read/write."""
    tag: str            # citation prefix used in the Lean docstrings, e.g. "O24"
    pdf: Path           # the paper PDF
    text: Path | None   # committed `pdftotext -layout` extraction of the PDF;
                        # None derives `<pdf stem>.txt` in PROGRESS_DIR
    title: str          # full reference, shown in the generated header
    lean_root: Path     # directory of Lean sources to scan
    exclude_dirs: tuple[str, ...]  # subdirectory names to skip (e.g. Scratch)
    out_md: Path        # generated Markdown table
    out_json: Path      # generated JSON intermediate
    summaries: Path     # curated one-line element summaries (TOML [summaries])


# Built-in default: Orrù 2024, the paper this repository formalises.
DEFAULT_SOURCE = Source(
    tag="O24",
    pdf=REPO / "docs" / "Orru_2024.pdf",
    text=None,  # derived: PROGRESS_DIR / "Orru_2024.txt"
    title="Michele Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, "
          "IACR ePrint 2024/1552",
    lean_root=REPO / "KVAC",
    exclude_dirs=("Scratch",),  # experimental, not part of the formalisation
    out_md=PROGRESS_DIR / "FORMALIZATION_PROGRESS.md",
    out_json=PROGRESS_DIR / "formalization_progress.json",
    summaries=PROGRESS_DIR / "element_summaries.toml",
)

# --- paper extraction ---------------------------------------------------------

ENV_KINDS = ("Theorem", "Lemma", "Definition", "Claim", "Corollary",
             "Proposition", "Construction")

# A genuine numbered environment heading: keyword, number, optional
# "(Parenthetical name)", a period, then a substantial statement on the same
# line. The trailing-statement requirement rejects cross-references such as
# "Theorem 6.12)." or "Theorem 5.6 below,".
ENV_RE = re.compile(
    r"^\s*(?P<kind>" + "|".join(ENV_KINDS) + r")\s+"
    r"(?P<num>\d+(?:\.\d+)*)"
    r"(?:\s*\((?P<name>[^)]*)\))?"
    r"\.\s+(?P<stmt>\S.{15,})"
)
# Section titles come from the table of contents (used only to recognise the
# matching heading lines in the body, so each element can be assigned to its
# enclosing section). TOC subsection: "  3.1 Title . . . . 24" (the dotted
# leader uses spaced dots); TOC section: "3 Title    24".
TOC_SUB_RE = re.compile(
    r"^\s*(?P<num>\d+\.\d+)\s+(?P<title>.+?)\s*(?:\.\s*){3,}\s*\d+\s*$")
TOC_SEC_RE = re.compile(r"^\s*(?P<num>\d+)\s+(?P<title>[A-Z].+?)\s+\d+\s*$")
# A numbered heading as it appears in the body (no dotted leader, no page no.).
HEAD_RE = re.compile(r"^\s*(?P<num>\d+(?:\.\d+)*)\s+(?P<title>\S.*?)\s*$")
# A figure caption: "Figure 5: ...".
FIG_RE = re.compile(r"^\s*Figure\s+(?P<num>\d+):\s*(?P<caption>.+)")


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s.strip())


@dataclass
class PaperElement:
    key: str            # canonical join key, e.g. "Definition 3.1", "Figure 5", "§3.1"
    kind: str           # Definition | Theorem | Lemma | ... | Figure | Section
    number: str
    label: str          # parenthetical name, e.g. "Correctness" (may be empty)
    statement: str      # snippet of the statement / caption / section title
    section: str        # enclosing section number, e.g. "5.2"
    section_title: str  # enclosing section title, e.g. "Theorems"
    page: int           # 1-based PDF page the element appears on
    seq: int = 0        # document order, used for sorting


@functools.lru_cache(maxsize=None)
def pdf_to_text(pdf: Path) -> str:
    """Layout-preserving text of the PDF (form-feed separated pages). Run only
    by ``extract`` (and ``init``); ``report``/``--check`` read the committed
    extraction instead, so their output does not depend on the local poppler
    version."""
    if not pdf.exists():
        raise SystemExit(f"error: source PDF not found: {pdf}")
    try:
        proc = subprocess.run(
            ["pdftotext", "-layout", str(pdf), "-"],
            check=True, capture_output=True, text=True,
        )
    except FileNotFoundError:
        raise SystemExit("error: 'pdftotext' not found; install poppler-utils.")
    except subprocess.CalledProcessError as e:
        raise SystemExit(f"error: pdftotext failed on {pdf}:\n{e.stderr.strip()}")
    return proc.stdout


def paper_text(path: Path) -> str:
    """The committed text extraction of the paper (form-feed separated pages),
    the single input of the paper side of the report."""
    if not path.exists():
        raise SystemExit(
            f"error: paper text extraction not found: {path}\n"
            f"generate and commit it with: python3 {SCRIPT_REL} extract")
    return path.read_text(encoding="utf-8")


def extract_paper(text: str) -> list[PaperElement]:
    # Section-title map from the TOC, used to recognise body headings.
    toc: dict[str, str] = {}
    for ln in text.splitlines():
        m = TOC_SUB_RE.match(ln) or TOC_SEC_RE.match(ln)
        if m:
            toc.setdefault(m["num"], _norm(m["title"]))

    elements: dict[str, PaperElement] = {}
    section, section_title = "", ""
    seq = 0

    def add(key, kind, number, label, statement, page):
        nonlocal seq
        # First occurrence wins (later mentions are cross-references).
        if key not in elements:
            elements[key] = PaperElement(key, kind, number, label, statement,
                                         section, section_title, page, seq)
            seq += 1

    # Pages are separated by form feeds in pdftotext output; index is 1-based.
    for page_no, page in enumerate(text.split("\f"), start=1):
        for ln in page.splitlines():
            h = HEAD_RE.match(ln)
            if h and toc.get(h["num"]) == _norm(h["title"]):
                section, section_title = h["num"], toc[h["num"]]
                add(f"§{section}", "Section", section, "", section_title, page_no)
                continue
            f = FIG_RE.match(ln)
            if f:
                add(f'Figure {f["num"]}', "Figure", f["num"], "",
                    _norm(f["caption"]), page_no)
                continue
            m = ENV_RE.match(ln)
            if m:
                add(f'{m["kind"]} {m["num"]}', m["kind"], m["num"],
                    (m["name"] or "").strip(), m["stmt"].strip(), page_no)

    return sorted(elements.values(), key=lambda e: e.seq)


# --- Lean extraction ----------------------------------------------------------

DECL_RE = re.compile(
    r"^(?P<mods>(?:noncomputable\s+|private\s+|protected\s+|partial\s+|"
    r"@\[[^\]]*\]\s*)*)"
    r"(?P<kind>def|structure|abbrev|class\s+abbrev|class|instance|lemma|theorem"
    r"|inductive)\s+"
    # The name runs up to the first whitespace or opening delimiter. This is
    # Unicode-aware, so Lean identifiers with Greek/subscripts (e.g.
    # `μCMZBaseMACSyntax`, `x₀`) are captured, not just ASCII ones.
    r"(?P<name>[^\s:({\[]+)?"
)
# Reference kinds recognised inside Lean text: the numbered environments plus
# figures and bare section signs. Kept in sync with the paper-side ENV_KINDS.
REF_KINDS = ENV_KINDS + ("Figure",)


# A single canonical element token: `Theorem 5.1`, `Definition 3.1`, `§3.3`,
# `Equation 9`/`Eq. 9`, `Fig 9`, … The `Eq`/`Fig` abbreviations are normalized to
# `Equation N` / `Figure N` in `normalize_ref`.
_ELEMENT = (r"(?:(?:" + "|".join(REF_KINDS) + r")\s+\d+(?:\.\d+)*"
            r"|(?:Equation|Eq|Fig)\.?\s+\d+"
            r"|§\s?\d+(?:\.\d+)*)")
_ELEMENT_RE = re.compile(_ELEMENT)
# Separators inside a tag-governed list, e.g. `O24 §5.1, Figure 9` or
# `O24 Fig 9 / Eq. 9`.
_SEP = r"(?:\s*(?:,|/|and|&)\s*)"
_EQ_ABBREV_RE = re.compile(r"(?:Equation|Eq)\.?\s+(\d+)$")
_FIG_ABBREV_RE = re.compile(r"Fig\.?\s+(\d+)$")


def make_ref_re(tag: str) -> re.Pattern[str]:
    """Citation matcher. The ``<tag>`` prefix is **mandatory** and governs one or
    more canonical element tokens, allowing a short ``,``/``/``/``and``-separated
    list (e.g. ``O24 §5.1, Figure 9``). A bare element with no tag, or one after a
    different tag (``CMZ14 Figure 5``), does not match — so a prose mention is not
    silently read as a formalization claim, and a citation of another paper is not
    misattributed to this one."""
    return re.compile(rf"{re.escape(tag)}\s+({_ELEMENT}(?:{_SEP}{_ELEMENT})*)")


def normalize_ref(raw: str) -> str:
    raw = raw.replace("§ ", "§").strip()
    m = _EQ_ABBREV_RE.fullmatch(raw)
    if m:
        return f"Equation {m.group(1)}"
    m = _FIG_ABBREV_RE.fullmatch(raw)
    if m:
        return f"Figure {m.group(1)}"
    return raw


SORRY_RE = re.compile(r"\b(sorry|sorryAx|admit)\b")


@dataclass
class LeanDecl:
    name: str
    kind: str
    file: str
    line: int
    refs: list[str] = field(default_factory=list)
    has_sorry: bool = False  # the declaration body is incomplete


@dataclass
class LeanFile:
    file: str
    module_refs: list[str] = field(default_factory=list)
    decls: list[LeanDecl] = field(default_factory=list)


def find_refs(text: str, ref_re: re.Pattern[str]) -> list[str]:
    out, seen = [], set()
    for m in ref_re.finditer(text):
        for em in _ELEMENT_RE.finditer(m.group(1)):
            r = normalize_ref(em.group())
            if r not in seen:
                seen.add(r)
                out.append(r)
    return out


def git_ignored(paths: list[Path]) -> set[Path]:
    """The subset of ``paths`` git ignores via .gitignore, .git/info/exclude,
    and the global excludes file. Empty if git is unavailable or errors."""
    if not paths:
        return set()
    try:
        res = subprocess.run(
            ["git", "-C", str(REPO), "check-ignore", "--stdin"],
            input="\n".join(str(p) for p in paths),
            capture_output=True, text=True)
    except (FileNotFoundError, OSError):
        return set()
    if res.returncode not in (0, 1):  # 0 = some ignored, 1 = none, else error
        return set()
    return {Path(line) for line in res.stdout.splitlines()}


def lean_files(root: Path, exclude_dirs: tuple[str, ...]) -> list[Path]:
    skip = set(exclude_dirs)
    candidates = sorted(
        p for p in root.rglob("*.lean")
        if not (skip & set(p.relative_to(root).parts))
    )
    # Honour git's ignore rules (.gitignore, .git/info/exclude); this is what
    # excludes Scratch/, .lake/, and any other ignored Lean sources.
    ignored = git_ignored(candidates)
    return [p for p in candidates if p not in ignored]


def extract_lean(root: Path, exclude_dirs: tuple[str, ...],
                 ref_re: re.Pattern[str]) -> list[LeanFile]:
    results = []
    for path in lean_files(root, exclude_dirs):
        rel = str(path.relative_to(REPO)) if path.is_relative_to(REPO) \
            else str(path)
        lines = path.read_text(encoding="utf-8").splitlines()
        lf = LeanFile(file=rel)

        # Module doc: first /-! ... -/ block.
        in_mod, mod_buf = False, []
        for ln in lines:
            if "/-!" in ln:
                in_mod = True
            if in_mod:
                mod_buf.append(ln)
            if in_mod and "-/" in ln:
                break
        lf.module_refs = find_refs("\n".join(mod_buf), ref_re)

        # Walk declarations, attaching the immediately preceding /-- -/ docstring.
        doc_buf, in_doc = [], False
        i = 0
        while i < len(lines):
            ln = lines[i]
            stripped = ln.rstrip()
            if not in_doc and ln.lstrip().startswith("/--"):
                in_doc = True
                doc_buf = [ln]
                if "-/" in ln[ln.index("/--") + 3:]:
                    in_doc = False
                i += 1
                continue
            if in_doc:
                doc_buf.append(ln)
                if "-/" in ln:
                    in_doc = False
                i += 1
                continue

            m = DECL_RE.match(ln)
            # Only top-level declarations (column 0); field docstrings inside
            # structures are indented and never match here.
            if m and m["name"] and not ln.startswith(" "):
                doc_text = "\n".join(doc_buf)
                refs = find_refs(doc_text + "\n" + stripped, ref_re)
                # `class abbrev` collapses to `abbrev` (its definitional nature)
                # so it is a matching kind and keeps its real name.
                lf.decls.append(LeanDecl(
                    name=m["name"], kind=m["kind"].split()[-1],
                    file=rel, line=i + 1, refs=refs,
                ))
                doc_buf = []
            elif stripped and not ln.lstrip().startswith("--"):
                # A non-doc, non-blank line breaks the docstring association.
                doc_buf = []
            i += 1

        # Flag declarations whose body (up to the next top-level declaration)
        # contains `sorry`/`admit`, i.e. is not fully proved.
        starts = [d.line for d in lf.decls]
        for k, d in enumerate(lf.decls):
            end = starts[k + 1] - 1 if k + 1 < len(starts) else len(lines)
            body = "\n".join(lines[d.line - 1:end])
            d.has_sorry = bool(SORRY_RE.search(body))

        results.append(lf)
    return results


# --- join + render ------------------------------------------------------------

def build(paper: list[PaperElement], lean: list[LeanFile]):
    # key -> {"decls": [LeanDecl], "modules": [file]}
    by_key: dict[str, dict] = {}
    for lf in lean:
        for d in lf.decls:
            for r in d.refs:
                by_key.setdefault(r, {"decls": [], "modules": []})["decls"].append(d)
        for r in lf.module_refs:
            by_key.setdefault(r, {"decls": [], "modules": []})["modules"].append(lf.file)
    return by_key


def load_summaries(path: Path) -> dict[str, str]:
    """Curated one-line summaries keyed by element (``[summaries]`` table)."""
    if not path.exists():
        return {}
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    table = data.get("summaries", data)
    return {k: str(v).strip() for k, v in table.items()}


def load_dim(path: Path) -> tuple[list[str], str]:
    """Curated dim-list from the summaries file: a top-level ``dim`` array of
    element keys ("Theorem 2") or section prefixes ("§6", which dims every
    element of section 6 and its subsections), plus an optional ``dim_note``
    explaining the graying, shown above the table."""
    if not path.exists():
        return [], ""
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    return [str(d) for d in data.get("dim", [])], str(data.get("dim_note", ""))


def is_dimmed(e: PaperElement, dim: list[str]) -> bool:
    """Whether ``e`` matches the curated dim-list (exact key, or `§N` prefix
    covering the section, its subsections, and their elements)."""
    for d in dim:
        if e.key == d:
            return True
        if d.startswith("§"):
            sec = d[1:]
            for num in (e.section, e.number if e.kind == "Section" else ""):
                if num and (num == sec or num.startswith(sec + ".")):
                    return True
    return False


# --- equations (cite-driven) --------------------------------------------------

# A right-aligned equation number `(N)` at the end of a display-math line.
_EQ_LINE_RE = re.compile(r"\S.*?\s{2,}\((\d+)\)\s*$")


def locate_equations(text: str) -> dict[int, int]:
    """Best-effort ``equation number -> 1-based page`` map, from the right-aligned
    ``(N)`` marker at the end of a display line (first occurrence wins).

    This is a heuristic: it also matches some non-equation parenthesized numbers
    and misses others, so it is used only *on demand* — to place the specific
    equations a Lean docstring cites. A cited equation it cannot place is reported
    by ``--check`` (never silently dropped); give its page in an
    ``[equation_pages]`` table of the summaries file to override."""
    found: dict[int, int] = {}
    for pno, page in enumerate(text.split("\f"), start=1):
        for ln in page.splitlines():
            m = _EQ_LINE_RE.search(ln)
            if m:
                found.setdefault(int(m.group(1)), pno)
    return found


def load_page_overrides(path: Path) -> dict[str, int]:
    """Curated ``key -> page`` overrides from an optional ``[equation_pages]``
    table, for equations the locator heuristic cannot place."""
    if not path.exists():
        return {}
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    return {k: int(v) for k, v in data.get("equation_pages", {}).items()}


def load_section_overrides(path: Path) -> dict[str, str]:
    """Curated ``key -> section number`` overrides from an optional
    ``[element_sections]`` table, for elements the extractor files under the
    wrong enclosing section (e.g. a figure placed just above the heading of
    the section it belongs to)."""
    if not path.exists():
        return {}
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    return {k: str(v) for k, v in data.get("element_sections", {}).items()}


def cited_equation_keys(lean: list[LeanFile]) -> set[str]:
    """The ``Equation N`` keys actually cited by some Lean docstring."""
    keys: set[str] = set()
    for lf in lean:
        keys.update(lf.module_refs)
        for d in lf.decls:
            keys.update(d.refs)
    return {k for k in keys if re.fullmatch(r"Equation \d+", k)}


def equation_elements(text: str, cited: set[str], overrides: dict[str, int],
                      base_seq: int) -> list[PaperElement]:
    """Paper elements for the cited equations we can place (curated page, else the
    heuristic). Equations we cannot place are omitted, so their citations stay
    unresolved and surface in ``--check``."""
    if not cited:
        return []
    located = locate_equations(text)
    out = []
    for key in sorted(cited, key=lambda k: int(k.split()[1])):
        n = int(key.split()[1])
        page = overrides.get(key) or located.get(n)
        if page is None:
            continue
        out.append(PaperElement(
            key=key, kind="Equation", number=str(n), label="", statement="",
            section="", section_title="", page=page, seq=base_seq + n))
    return out


# A Lean declaration is the right *kind* of object for a paper element when a
# definitional construct backs a definition/construction/game, and a proof backs
# a theorem-like statement. This is the "signature match" check.
LEAN_DEFN_KINDS = {"def", "structure", "abbrev", "class", "inductive", "instance"}
LEAN_PROP_KINDS = {"theorem", "lemma"}
PAPER_PROP_KINDS = {"Theorem", "Lemma", "Claim", "Corollary", "Proposition"}


def signature_matches(paper_kind: str, lean_kind: str) -> bool:
    if paper_kind in PAPER_PROP_KINDS:
        return lean_kind in LEAN_PROP_KINDS
    return lean_kind in LEAN_DEFN_KINDS  # Definition / Construction / Figure / Section


# Status marks, a consistent set of circles.
# These marks are heuristic reads of the scan, not verified facts: each is a
# claim worth reviewing, since both the paper extraction and the Lean/citation
# scan are approximate and can miss or misclassify.
ST_DONE = "🟢"      # appears formalized: a sorry-free matching-kind decl seems to cite it
ST_SORRY = "🌐"     # a matching decl is cited but looks to contain `sorry`
ST_MISMATCH = "🌀"  # a decl cites it but its kind looks non-matching
ST_MODULE = "🟡"    # only module-level coverage detected
ST_NONE = "⚪"      # nothing detected yet


def element_status(e: PaperElement, by_key: dict) -> tuple[str, list]:
    """Return a heuristic ``(status, matching_decls)`` for a paper element. Each
    mark is an approximate read to review, not a proof:

    🟢 a sorry-free Lean declaration seems to match the paper object's kind;
    🌐 a kind-matching declaration is cited but appears to contain `sorry`;
    🌀 a declaration cites it but its kind looks non-matching;
    🟡 only module-level coverage detected; ⚪ nothing detected yet.
    """
    hit = by_key.get(e.key) or {"decls": [], "modules": []}
    decls, modules = hit["decls"], hit["modules"]
    matching = [d for d in decls if signature_matches(e.kind, d.kind)]
    matching_ok = [d for d in matching if not d.has_sorry]
    if matching_ok:
        return ST_DONE, matching_ok
    if matching:
        return ST_SORRY, matching
    if decls:
        return ST_MISMATCH, decls
    if modules:
        return ST_MODULE, []
    return ST_NONE, []


# Light-gray wrapper for dimmed rows. Inline styles render in VS Code and most
# Markdown viewers; github.com strips the style attribute and shows plain text.
_DIM_OPEN, _DIM_CLOSE = '<span style="color:#a0a0a0">', "</span>"


def render_markdown(source: Source, paper: list[PaperElement], by_key: dict,
                    lean: list[LeanFile], summaries: dict[str, str],
                    dim: list[str], dim_note: str,
                    sec_titles: dict[str, str]) -> str:
    status = {e.key: element_status(e, by_key) for e in paper}
    formalized = sum(1 for e in paper if status[e.key][0] == ST_DONE)
    covered = sum(1 for e in paper if e.key in by_key)
    total = len(paper)
    n_decls = sum(len(lf.decls) for lf in lean)
    n_files = len(lean)
    n_sorry = sum(1 for lf in lean for d in lf.decls if d.has_sorry)

    out = []
    out.append("# Formalization progress ↔ Lean\n")
    out.append(
        f"Generated by `{SCRIPT_REL}`. Do not edit by hand.\n"
    )
    out.append(
        "This is an approximate map, not an authoritative measurement. Both "
        "sides are recovered heuristically — paper elements by text extraction "
        "from the PDF, Lean declarations and their citations by source scanning, "
        "equation locations by a best-effort locator — so it may miss or "
        "misclassify. Read the counts below as indicative, and each "
        f"{ST_DONE} as a *claim* worth reviewing rather than a verified fact "
        "(see `docs/STYLE_GUIDE.md`).\n"
    )
    out.append(
        f"Reference: {source.title} (cited as **{source.tag}** in the "
        "Lean sources).\n"
    )
    out.append("## Summary\n")
    out.append("These figures are approximate (see the note above).\n")
    out.append(f"- Paper elements catalogued: roughly **{total}**")
    out.append(f"- Paper elements *reported* formalized (a sorry-free Lean "
               f"declaration of matching kind cites them): **{formalized}** "
               f"(~{100 * formalized // total if total else 0}%)")
    out.append(f"- Paper elements with some Lean association: **{covered}**")
    out.append(f"- Lean declarations scanned: **{n_decls}** across "
               f"**{n_files}** files; **{n_sorry}** detected to contain "
               "`sorry`\n")

    # All links are written relative to the Markdown file's own directory, so
    # they resolve correctly wherever the report is placed in the tree.
    base = source.out_md.parent
    pdf_rel = os.path.relpath(source.pdf, base)

    def link(repo_rel_path: str) -> str:
        return os.path.relpath(REPO / repo_rel_path, base)

    # Breakdown by paper element kind: catalogued vs formalized (✅), with the
    # member elements listed by number, each linking to its page in the PDF
    # (dimmed individually when out of scope).
    paper_kinds: dict[str, list] = {}
    for e in paper:
        cell = paper_kinds.setdefault(e.kind, [0, 0, []])
        cell[0] += 1
        if status[e.key][0] == ST_DONE:
            cell[1] += 1
        num = f"[{e.number}]({pdf_rel}#page={e.page})"
        if is_dimmed(e, dim):
            num = f"{_DIM_OPEN}{num}{_DIM_CLOSE}"
        cell[2].append(num)
    out.append("### By paper element\n")
    out.append("| Element kind | Elements | In paper | Formalized | Coverage |")
    out.append("|---|---|--:|--:|--:|")
    for kind in sorted(paper_kinds):
        n, c, nums = paper_kinds[kind]
        out.append(f"| {kind} | {', '.join(nums)} | {n} | {c} | "
                   f"{100 * c // n if n else 0}% |")
    out.append(f"| **Total** | | **{total}** | **{formalized}** | "
               f"**{100 * formalized // total if total else 0}%** |\n")

    # Breakdown by top-level paper section — one row per protocol/topic
    # (§5 µCMZ, §6 µBBS, ...). Out-of-scope sections render dimmed, matching
    # the element table.
    sections: dict[str, list[int]] = {}
    for e in paper:
        num = e.number if e.kind == "Section" else e.section
        top = num.split(".")[0] if num else "—"
        cell = sections.setdefault(top, [0, 0])
        cell[0] += 1
        if status[e.key][0] == ST_DONE:
            cell[1] += 1
    out.append("### By paper section\n")
    out.append("| Section | In paper | Formalized | Coverage |")
    out.append("|---|--:|--:|--:|")
    for top in sorted(sections, key=lambda k: (k == "—", int(k) if k.isdigit()
                                               else 0)):
        n, c = sections[top]
        label = (f"§{top} {sec_titles.get(top, '')}".strip() if top != "—"
                 else "(unsectioned)")
        cells = [label, str(n), str(c), f"{100 * c // n if n else 0}%"]
        if f"§{top}" in dim:
            cells = [f"{_DIM_OPEN}{c_}{_DIM_CLOSE}" for c_ in cells]
        out.append("| " + " | ".join(cells) + " |")
    out.append("")

    # Breakdown by Lean declaration kind: total vs those citing the paper.
    lean_kinds: dict[str, list[int]] = {}
    for lf in lean:
        for d in lf.decls:
            cell = lean_kinds.setdefault(d.kind, [0, 0])
            cell[0] += 1
            if d.refs:
                cell[1] += 1
    cited = sum(v[1] for v in lean_kinds.values())
    out.append("### By Lean declaration\n")
    out.append("| Declaration kind | Count | Cite the paper |")
    out.append("|---|--:|--:|")
    for kind in sorted(lean_kinds):
        n, c = lean_kinds[kind]
        out.append(f"| {kind} | {n} | {c} |")
    out.append(f"| **Total** | **{n_decls}** | **{cited}** |\n")

    out.append(
        "Status legend (heuristic reads, each a claim to verify rather than a "
        f"proof): {ST_DONE} appears formalized — a sorry-free declaration of "
        f"matching kind seems to cite it · "
        f"{ST_SORRY} a matching declaration is cited but looks to contain "
        f"`sorry` · "
        f"{ST_MISMATCH} a declaration cites it but its kind looks non-matching · "
        f"{ST_MODULE} only module-level coverage detected · "
        f"{ST_NONE} nothing detected yet\n")

    missing = sum(1 for e in paper if e.key not in summaries)
    out.append("## Paper element → Lean declarations\n")
    out.append("Each element name links to its page in the source PDF. "
               "Summaries are curated in "
               f"`{os.path.relpath(source.summaries, REPO)}`"
               + (f" ({missing} still pending)." if missing else ".") + "\n")
    if dim and dim_note:
        out.append(f"Rows in light gray: {dim_note}\n")
    out.append("| Paper element | Section | Page | Summary | "
               "Lean declarations | Status |")
    out.append("|---|---|---|---|---|---|")

    for e in paper:
        mark, _ = status[e.key]
        hit = by_key.get(e.key)

        lean_cells = []
        seen = set()
        if hit:
            for d in hit["decls"]:
                tag = (d.name, d.file, d.line)
                if tag in seen:
                    continue
                seen.add(tag)
                flags = []
                if not signature_matches(e.kind, d.kind):
                    flags.append("kind mismatch")
                if d.has_sorry:
                    flags.append("`sorry`")
                suffix = f" — {', '.join(flags)}" if flags else ""
                lean_cells.append(
                    f"`{d.name}` ({d.kind}) "
                    f"[{Path(d.file).name}:{d.line}]({link(d.file)}#L{d.line})"
                    f"{suffix}"
                )
            for f in dict.fromkeys(hit["modules"]):
                # Only show module-only coverage when there is no decl-level hit.
                if not hit["decls"]:
                    lean_cells.append(f"_module_ [{Path(f).name}]({link(f)})")

        name = f"[{e.key}]({pdf_rel}#page={e.page})"
        # A section row's own number would just repeat the element name.
        section = ("—" if e.kind == "Section" else
                   f"§{e.section} {e.section_title}".strip() if e.section else "—")
        summary = summaries.get(e.key, "_(summary pending)_")
        if e.label and not summary.startswith("_("):
            summary = f"**{e.label}.** {summary}"
        summary = summary.replace("|", "\\|")

        cells = [name, section, str(e.page), summary,
                 "<br>".join(lean_cells) if lean_cells else "—", mark]
        if is_dimmed(e, dim):
            cells = [f"{_DIM_OPEN}{c}{_DIM_CLOSE}" for c in cells]
        out.append("| " + " | ".join(cells) + " |")

    out.append("")
    return "\n".join(out)


# --- source resolution + main -------------------------------------------------

# Maps TOML/CLI keys to Source fields and how to coerce them. Paths are resolved
# relative to the repository root when given relative.
_PATH_FIELDS = {"pdf", "text", "lean_root", "out_md", "out_json", "summaries"}


def _resolve_path(value) -> Path:
    p = Path(value)
    return p if p.is_absolute() else REPO / p


def source_from_config(path: Path) -> dict:
    """Read a ``[source]`` table from a TOML file into a field-overrides dict."""
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    table = data.get("source", data)
    overrides = {}
    for key in ("tag", "pdf", "text", "title", "lean_root", "exclude_dirs",
                "out_md", "out_json", "summaries"):
        if key not in table:
            continue
        if key in _PATH_FIELDS:
            overrides[key] = _resolve_path(table[key])
        elif key == "exclude_dirs":
            overrides[key] = tuple(table[key])
        else:
            overrides[key] = table[key]
    return overrides


def resolve_source(args) -> Source:
    """Built-in default < TOML config (--config) < explicit CLI flags."""
    overrides: dict = {}
    if args.config:
        overrides.update(source_from_config(args.config))
    for key in ("tag", "title"):
        if getattr(args, key, None) is not None:
            overrides[key] = getattr(args, key)
    for key in ("pdf", "text", "lean_root", "out_md", "out_json"):
        if getattr(args, key, None) is not None:
            overrides[key] = _resolve_path(getattr(args, key))
    if args.exclude_dirs is not None:
        overrides["exclude_dirs"] = tuple(args.exclude_dirs)
    src = replace(DEFAULT_SOURCE, **overrides)
    if src.text is None:
        # Named after the source PDF, so a different paper never collides
        # with another paper's committed extraction.
        src = replace(src, text=PROGRESS_DIR / f"{src.pdf.stem}.txt")
    return src


# --- metadata extraction (init) -----------------------------------------------

CITATION_KINDS = r"Definition|Theorem|Lemma|Claim|Corollary|Proposition|" \
                 r"Construction|Figure"


def detect_tag(lean_root: Path, exclude_dirs: tuple[str, ...]) -> str | None:
    """Most frequent citation prefix already used in the Lean sources.

    Matches tokens such as ``O24`` / ``CMZ14`` immediately preceding a
    ``Definition``/``Theorem``/``§`` reference. Returns ``None`` if the code
    carries no citations yet (a fresh formalisation)."""
    tag_re = re.compile(rf"\b([A-Z][A-Za-z]*\d{{2}})\s+(?:{CITATION_KINDS}|§)")
    counts: dict[str, int] = {}
    for path in lean_files(lean_root, exclude_dirs):
        for m in tag_re.finditer(path.read_text(encoding="utf-8")):
            counts[m.group(1)] = counts.get(m.group(1), 0) + 1
    return max(counts, key=lambda k: counts[k]) if counts else None


def parse_url(url: str) -> tuple[str | None, str]:
    """Return ``(year, reference-suffix)`` parsed from a known repository URL."""
    m = re.search(r"eprint\.iacr\.org/(\d{4})/(\d+)", url)
    if m:
        return m.group(1), f"IACR ePrint {m.group(1)}/{m.group(2)}"
    m = re.search(r"arxiv\.org/(?:abs|pdf)/(\d{2})(\d{2})\.(\d+)", url)
    if m:
        return f"20{m.group(1)}", f"arXiv:{m.group(1)}{m.group(2)}.{m.group(3)}"
    m = re.search(r"doi\.org/(\S+)", url)
    if m:
        return None, f"doi:{m.group(1)}"
    return None, url


def pdf_metadata(pdf: Path) -> tuple[str, list[str]]:
    """Extract ``(title, authors)`` from the PDF (offline)."""
    info = subprocess.run(["pdfinfo", str(pdf)], capture_output=True,
                          text=True).stdout
    m = re.search(r"^Title:\s*(.+)$", info, re.M)
    title = m.group(1).strip() if m and m.group(1).strip() else ""

    page1 = subprocess.run(
        ["pdftotext", "-f", "1", "-l", "1", "-layout", str(pdf), "-"],
        capture_output=True, text=True).stdout
    lines = [ln.strip() for ln in page1.splitlines() if ln.strip()]
    if not title and lines:
        title = lines[0]

    authors: list[str] = []
    for ln in lines:
        if ln == title:
            continue
        if ln.lower().startswith("abstract"):
            break
        if "@" in ln or ln.isupper():  # skip emails and all-caps affiliations
            continue
        # An author line: split multiple authors on commas / "and".
        for a in re.split(r"\s*(?:,|\band\b)\s*", ln):
            a = a.strip()
            if a and re.search(r"[A-Za-z]", a):
                authors.append(a)
        if authors:
            break
    return title, authors


def fetch_url_metadata(url: str) -> tuple[str, list[str], str | None] | None:
    """Best-effort online enrichment via Highwire ``citation_*`` meta tags.

    Returns ``(title, authors, year)`` or ``None`` on any network/parse failure,
    so callers fall back to offline PDF extraction."""
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        html = urllib.request.urlopen(req, timeout=20).read().decode(
            "utf-8", "replace")
    except (urllib.error.URLError, OSError, ValueError):
        return None

    def meta(name: str) -> list[str]:
        return re.findall(
            rf'<meta[^>]+name="{name}"[^>]+content="([^"]*)"', html)

    titles = meta("citation_title")
    if not titles:
        return None
    authors = meta("citation_author")
    years = meta("citation_publication_date") or meta("citation_year")
    year = years[0][:4] if years else None
    return titles[0].strip(), [a.strip() for a in authors], year


def pdf_url_for(url: str) -> str | None:
    """The direct PDF URL for a known repository landing page, if derivable."""
    m = re.search(r"eprint\.iacr\.org/(\d{4})/(\d+)", url)
    if m:
        return f"https://eprint.iacr.org/{m.group(1)}/{m.group(2)}.pdf"
    m = re.search(r"arxiv\.org/(?:abs|pdf)/(\S+?)(?:\.pdf)?$", url)
    if m:
        return f"https://arxiv.org/pdf/{m.group(1)}.pdf"
    return url if url.lower().endswith(".pdf") else None


def download_pdf(url: str, dest: Path) -> bool:
    """Best-effort download of ``url`` to ``dest``. Returns success."""
    src_url = pdf_url_for(url)
    if not src_url:
        return False
    try:
        req = urllib.request.Request(src_url,
                                     headers={"User-Agent": "Mozilla/5.0"})
        data = urllib.request.urlopen(req, timeout=30).read()
    except (urllib.error.URLError, OSError, ValueError):
        return False
    if not data.startswith(b"%PDF"):
        return False
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    return True


def derive_tag(authors: list[str], year: str | None) -> str:
    """Fallback tag: author-surname initials + 2-digit year (e.g. ``O24``)."""
    initials = "".join(a.split()[-1][0].upper() for a in authors if a.split())
    yy = year[-2:] if year else "??"
    return f"{initials or 'X'}{yy}"


def build_reference(title: str, authors: list[str], suffix: str) -> str:
    who = ", ".join(authors)
    parts = [p for p in (who, f"*{title}*" if title else "", suffix) if p]
    return ", ".join(parts)


def emit_toml(tag: str, pdf: Path, text: Path, title: str, lean_root: Path,
              exclude_dirs: tuple[str, ...], out_md: Path,
              out_json: Path, summaries: Path) -> str:
    def rel(p: Path) -> str:
        return str(p.relative_to(REPO)) if p.is_relative_to(REPO) else str(p)
    excl = ", ".join(f'"{d}"' for d in exclude_dirs)
    esc = title.replace('"', '\\"')
    return (
        f"# Source of truth for {SCRIPT_REL}.\n"
        "# Generated by `formalization_progress.py init`; review and edit by hand\n"
        "# if needed (in particular the `tag`, which must match the citation\n"
        "# prefix actually used in the Lean docstrings).\n\n"
        "[source]\n"
        f'tag = "{tag}"\n'
        f'pdf = "{rel(pdf)}"\n'
        f'text = "{rel(text)}"  # committed pdftotext extraction (regenerate with `extract`)\n'
        f'title = "{esc}"\n'
        f'lean_root = "{rel(lean_root)}"\n'
        f"exclude_dirs = [{excl}]\n"
        f'out_md = "{rel(out_md)}"\n'
        f'out_json = "{rel(out_json)}"\n'
        f'summaries = "{rel(summaries)}"  # curated one-line element summaries\n'
    )


def cmd_init(args) -> int:
    if not args.pdf and not args.url:
        raise SystemExit("error: provide at least one of --pdf / --url.")

    lean_root = _resolve_path(args.lean_root) if args.lean_root \
        else DEFAULT_SOURCE.lean_root
    exclude_dirs = tuple(args.exclude_dirs) if args.exclude_dirs \
        else DEFAULT_SOURCE.exclude_dirs
    out_md = _resolve_path(args.out_md) if args.out_md else DEFAULT_SOURCE.out_md
    out_json = _resolve_path(args.out_json) if args.out_json \
        else DEFAULT_SOURCE.out_json
    out_cfg = _resolve_path(args.out) if args.out \
        else PROGRESS_DIR / "formalization_source.toml"

    year, suffix = parse_url(args.url) if args.url else (None, "")
    title, authors = "", []
    notes: list[str] = []

    # Online metadata (best effort; the URL may be unreachable).
    online = fetch_url_metadata(args.url) if args.url else None
    if online:
        title, authors, o_year = online
        year = o_year or year
        notes.append("metadata read from URL")
    elif args.url:
        notes.append("URL not reachable")

    # Resolve the PDF: use --pdf if given, else try to download it from the URL.
    pdf = _resolve_path(args.pdf) if args.pdf else None
    if pdf and not pdf.exists():
        raise SystemExit(f"error: source PDF not found: {pdf}")
    if pdf is None and args.url:
        dest = REPO / "docs" / f"{(authors[0].split()[-1] if authors else 'paper')}" \
                              f"_{year or 'unknown'}.pdf"
        if download_pdf(args.url, dest):
            pdf = dest
            notes.append(f"downloaded PDF to {dest.relative_to(REPO)}")
        else:
            notes.append("could not download PDF")

    # Offline extraction fills any field the URL did not provide.
    if pdf and pdf.exists():
        p_title, p_authors = pdf_metadata(pdf)
        title = title or p_title
        authors = authors or p_authors

    if not title:
        # Nothing readable (e.g. URL-only with no network). Fall back to the
        # URL-derived reference so there is a TOML to edit by hand.
        notes.append("title unknown; edit `title` in the TOML")
    reference = build_reference(title, authors, suffix) or "TODO: paper title"

    # The tag must match what the Lean code writes; prefer the detected one.
    detected = detect_tag(lean_root, exclude_dirs)
    tag = args.tag or detected or derive_tag(authors, year)
    via = ("supplied" if args.tag else
           "detected from Lean sources" if detected else
           "derived from authors+year")

    # If no usable PDF, record where it should live so `report` can find it.
    pdf_field = pdf if pdf else (
        REPO / "docs" / f"{(authors[0].split()[-1] if authors else 'paper')}"
                        f"_{year or 'unknown'}.pdf")
    if not (pdf and pdf.exists()):
        notes.append(f"set pdf = {pdf_field.relative_to(REPO)} and place the "
                     "file there before running `report`")

    summaries = DEFAULT_SOURCE.summaries
    text_field = PROGRESS_DIR / f"{pdf_field.stem}.txt"
    toml_text = emit_toml(tag, pdf_field, text_field, reference, lean_root,
                          exclude_dirs, out_md, out_json, summaries)
    out_cfg.write_text(toml_text)
    print(f"Wrote {out_cfg}")
    print(f"  title : {reference}")
    print(f"  tag   : {tag} ({via})")
    print(f"  pdf   : {pdf_field}")
    for n in notes:
        print(f"  note  : {n}")
    print("Review the file, then run: "
          f"python3 {SCRIPT_REL} --config "
          f"{out_cfg.relative_to(REPO) if out_cfg.is_relative_to(REPO) else out_cfg}")
    return 0


# --- report (default) ---------------------------------------------------------

def cmd_report(args) -> int:
    src = resolve_source(args)
    ref_re = make_ref_re(src.tag)

    text = paper_text(src.text)
    paper_all = extract_paper(text)
    lean = extract_lean(src.lean_root, src.exclude_dirs, ref_re)
    summaries = load_summaries(src.summaries)
    dim, dim_note = load_dim(src.summaries)
    # Cite-driven equations: only equations a Lean docstring references are added,
    # placed by the on-demand locator (or a curated page override).
    paper_all = paper_all + equation_elements(
        text, cited_equation_keys(lean), load_page_overrides(src.summaries),
        base_seq=len(paper_all))
    # Section number -> title, from the extracted TOC (section elements).
    sec_titles = {e.number: e.statement for e in paper_all
                  if e.kind == "Section"}
    # Curated enclosing-section corrections ([element_sections] in the
    # summaries file); the section title comes from the extracted TOC.
    sec_over = load_section_overrides(src.summaries)
    for e in paper_all:
        num = sec_over.get(e.key)
        if num is not None:
            e.section, e.section_title = num, sec_titles.get(num, "")
    # Numbered environments and equations are always tracked; figures and sections
    # appear only when curated (given a summary), i.e. judged a formalizable
    # contribution.
    paper = [e for e in paper_all
             if e.kind not in ("Figure", "Section") or e.key in summaries]
    paper.sort(key=lambda e: (e.page, e.seq))
    by_key = build(paper, lean)
    md = render_markdown(src, paper, by_key, lean, summaries, dim, dim_note,
                         sec_titles)

    # Drift the tool exists to catch: a Lean citation or a summary key that names
    # no element in the paper universe (a typo like `O24 Theorem 5.9`, a
    # pdftotext extraction miss, or a stale summary key). These are otherwise
    # dropped silently by the element-driven rendering, so surface them.
    universe = {e.key for e in paper_all}
    problems = []
    unresolved = sorted(k for k in by_key if k not in universe)
    if unresolved:
        problems.append("Lean citations naming no paper element: "
                        + ", ".join(unresolved))
    unknown_summaries = sorted(k for k in summaries if k not in universe)
    if unknown_summaries:
        problems.append("element_summaries.toml keys naming no paper element: "
                        + ", ".join(unknown_summaries))
    unknown_sections = sorted(k for k in sec_over if k not in universe)
    if unknown_sections:
        problems.append("[element_sections] keys naming no paper element: "
                        + ", ".join(unknown_sections))

    paper_json = []
    for e in paper:
        d = asdict(e)
        d["summary"] = summaries.get(e.key, "")  # curated; "" if pending
        paper_json.append(d)
    intermediate = {
        "source": {"tag": src.tag, "title": src.title,
                   "pdf": str(src.pdf.relative_to(REPO))
                   if src.pdf.is_relative_to(REPO) else str(src.pdf)},
        "paper": paper_json,
        "lean": [asdict(lf) for lf in lean],
    }
    js = json.dumps(intermediate, indent=2, ensure_ascii=False)

    if args.check:
        stale = []
        if not src.out_md.exists() or src.out_md.read_text() != md:
            stale.append(str(src.out_md))
        if not src.out_json.exists() or src.out_json.read_text() != js:
            stale.append(str(src.out_json))
        if stale or problems:
            if stale:
                print(f"Out of date (re-run {SCRIPT_REL}):", file=sys.stderr)
                for s in stale:
                    print(f"  {s}", file=sys.stderr)
            for p in problems:
                print(f"error: {p}", file=sys.stderr)
            return 1
        print("Up to date.")
        return 0

    for p in problems:
        print(f"warning: {p}", file=sys.stderr)
    src.out_md.write_text(md)
    src.out_json.write_text(js)
    covered = sum(1 for e in paper if e.key in by_key)
    print(f"Wrote {src.out_md} and {src.out_json}: "
          f"{covered}/{len(paper)} paper elements associated.")
    return 0


# --- extract ------------------------------------------------------------------

def cmd_extract(args) -> int:
    src = resolve_source(args)
    text = pdf_to_text(src.pdf)
    src.text.parent.mkdir(parents=True, exist_ok=True)
    src.text.write_text(text, encoding="utf-8")
    pages = text.count("\f") + 1
    print(f"Wrote {src.text} ({pages} pages) from {src.pdf}.")
    print("Commit it: `report` and `--check` read this file, not the PDF.")
    return 0


# --- CLI ----------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    # `report` is the default subcommand, so existing invocations such as
    # `formalization_progress.py --config x.toml --check` keep working.
    if not argv or argv[0] not in ("report", "init", "extract"):
        argv = ["report"] + argv

    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    rep = sub.add_parser("report", help="generate the progress table (default)")
    rep.add_argument("--check", action="store_true",
                     help="exit non-zero if the generated files are out of date")
    rep.add_argument("--config", type=Path,
                     help="TOML file with a [source] table describing the paper")
    # Per-field overrides (take precedence over --config and the default).
    rep.add_argument("--tag", help="citation prefix used in Lean docstrings")
    rep.add_argument("--pdf", type=Path, help="source paper PDF")
    rep.add_argument("--text", type=Path,
                     help="committed text extraction of the paper")
    rep.add_argument("--title", help="full reference shown in the header")
    rep.add_argument("--lean-root", dest="lean_root", type=Path,
                     help="directory of Lean sources to scan")
    rep.add_argument("--exclude-dir", dest="exclude_dirs", action="append",
                     help="subdirectory name to skip (repeatable)")
    rep.add_argument("--out-md", dest="out_md", type=Path)
    rep.add_argument("--out-json", dest="out_json", type=Path)
    rep.set_defaults(func=cmd_report)

    ext = sub.add_parser(
        "extract",
        help="run pdftotext on the source PDF and write the committed text "
             "extraction that `report`/`--check` read (requires poppler)")
    ext.add_argument("--config", type=Path,
                     help="TOML file with a [source] table describing the paper")
    ext.add_argument("--pdf", type=Path, help="source paper PDF")
    ext.add_argument("--text", type=Path,
                     help="where to write the text extraction")
    ext.add_argument("--exclude-dir", dest="exclude_dirs", action="append",
                     help=argparse.SUPPRESS)
    ext.set_defaults(func=cmd_extract)

    ini = sub.add_parser(
        "init", help="generate the source-of-truth TOML from a PDF and/or a URL")
    # At least one of --pdf / --url is required (checked in cmd_init); they are
    # complementary, not exclusive.
    ini.add_argument("--pdf", type=Path, help="source paper PDF")
    ini.add_argument("--url", help="canonical paper URL (IACR ePrint, arXiv, DOI)")
    ini.add_argument("--tag", help="override the auto-detected citation prefix")
    ini.add_argument("--lean-root", dest="lean_root", type=Path,
                     help="Lean sources to scan for the existing citation tag")
    ini.add_argument("--exclude-dir", dest="exclude_dirs", action="append",
                     help="subdirectory name to skip (repeatable)")
    ini.add_argument("--out-md", dest="out_md", type=Path)
    ini.add_argument("--out-json", dest="out_json", type=Path)
    ini.add_argument("--out", type=Path,
                     help="config path to write (default docs/formalization_source.toml)")
    ini.set_defaults(func=cmd_init)

    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
