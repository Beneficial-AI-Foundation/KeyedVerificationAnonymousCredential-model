#!/usr/bin/env python3
"""Blueprint declaration-coverage check.

Asserts that every public declaration of the root KVAC library (as listed by
scripts/blueprint_decl_manifest.lean) appears in exactly one blueprint anchor
list in docs/KVACDocs/*.lean, and that no anchor names a declaration that does
not exist.

Usage:
    lake env lean --run scripts/blueprint_decl_manifest.lean > manifest.tsv
    python3 scripts/blueprint_coverage_check.py manifest.tsv

Exits nonzero on any gap, duplicate, or phantom. Rebuild the root library
(`lake build`) before generating the manifest, or stale .oleans will lie.
"""
import re
import sys
from collections import Counter
from pathlib import Path

def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    manifest = set()
    for line in Path(sys.argv[1]).read_text().splitlines():
        if "\t" in line:
            manifest.add(line.split("\t")[1].strip())

    anchors = []
    for f in sorted(Path("docs/KVACDocs").glob("*.lean")):
        for m in re.finditer(r'\(lean\s*:=\s*"([^"]+)"\s*\)', f.read_text()):
            for name in m.group(1).split(","):
                anchors.append((name.strip(), f.name))

    counts = Counter(name for name, _ in anchors)
    dupes = {n: c for n, c in counts.items() if c > 1}
    covered = set(counts)
    missing = manifest - covered
    phantom = covered - manifest

    print(f"manifest: {len(manifest)}  anchors: {len(anchors)}  unique: {len(covered)}")
    ok = True
    if dupes:
        ok = False
        print(f"DUPLICATE anchors ({len(dupes)}):")
        for n, c in sorted(dupes.items()):
            print(f"  {n} x{c}")
    if missing:
        ok = False
        print(f"MISSING from docs ({len(missing)}):")
        for n in sorted(missing):
            print(f"  {n}")
    if phantom:
        ok = False
        print(f"PHANTOM in docs ({len(phantom)}):")
        for n in sorted(phantom):
            where = ", ".join(f for a, f in anchors if a == n)
            print(f"  {n}  ({where})")
    print("coverage: OK" if ok else "coverage: FAILED")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
