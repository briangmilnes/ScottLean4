#!/bin/zsh
# repoint-index.sh — rewrite INDEX.md's links to the ScottDomains artifacts that
# moved to ScottProjects, leaving the ones that stayed alone.
#
# Usage: scripts/repoint-index.sh [--dry-run]
#
# INDEX.md exists so a path can be jumped to locally — VS Code ⌘-click or ⌘P,
# Emacs `ffap` — so the rewrite uses a *relative* path, `../ScottProjects/…`,
# not a github.com URL: a URL would satisfy the GitHub rendering and break every
# local jump, which is the documented purpose of the file.
#
# What moved (rewritten) and what stayed (untouched) is listed explicitly rather
# than inferred, so a future artifact added under ScottDomains/ is reported as
# unclassified instead of being silently mangled.
set -e

ROOT=${0:A:h}/..
DRY=0
[[ "$1" == "--dry-run" ]] && DRY=1

python3 - "$ROOT" "$DRY" <<'PY'
import sys, pathlib, re, collections

root = pathlib.Path(sys.argv[1])
dry = sys.argv[2] == "1"
idx = root / "INDEX.md"

MOVED = ["ScottDomains/ScottDomains/", "ScottDomains/ScottDomains.lean",
         "ScottDomains/docs/", "ScottDomains/lakefile.toml",
         "ScottDomains/lake-manifest.json", "ScottDomains/lean-toolchain",
         "ScottDomains/README.pdf"]
# Both with and without the trailing slash: INDEX.md links some of these as bare
# directories, and a slash-only list reported those as unclassified.
STAYED = ["ScottDomains/papers", "ScottDomains/logs", "ScottDomains/prompts",
          "ScottDomains/plans", "ScottDomains/reports",
          "ScottDomains/analyses", "ScottDomains/GunterScott90Images",
          "ScottDomains/README.md"]
PREFIX = "../ScottProjects/"

text = idx.read_text(encoding="utf-8")

# Only rewrite inside markdown link targets: (path) and (path:line).
link = re.compile(r'\((ScottDomains/[^)\s]*)\)')

counts = collections.Counter()
unclassified = collections.Counter()

def sub(m):
    p = m.group(1)
    for pre in MOVED:
        if p.startswith(pre):
            counts[pre] += 1
            return "(" + PREFIX + p + ")"
    for pre in STAYED:
        if p.startswith(pre):
            counts["(stayed) " + pre] += 1
            return m.group(0)
    unclassified[p] += 1
    return m.group(0)

new = link.sub(sub, text)

for k in sorted(counts):
    print(f"{counts[k]:4d}  {k}")
if unclassified:
    print("\nUNCLASSIFIED — left untouched, classify these by hand:")
    for p, n in sorted(unclassified.items()):
        print(f"{n:4d}  {p}")

moved_total = sum(v for k, v in counts.items() if not k.startswith("(stayed)"))
print(f"\n{moved_total} link(s) rewritten to {PREFIX}…")
if not dry:
    idx.write_text(new, encoding="utf-8")
    print(f"wrote {idx}")
else:
    print("dry run: nothing written")
PY
