#!/bin/zsh
# repoint-to-scottprojects.sh — update the LIVE measurement scripts to find the
# ScottDomains Lean package at its new home in ScottProjects.
#
# Usage: scripts/repoint-to-scottprojects.sh [--dry-run]
#
# Each of these scripts locates the package through exactly one assignment, so
# each is a one-line change. Verified by grep before writing: the script reports
# every substitution it makes and exits non-zero if any expected line is absent,
# so a silent no-op cannot pass for success.
#
# The other ~140 scripts under scripts/ that mention ScottDomains are per-round
# probes (a1-*, a2-*, a5-r46-*, …) written against a state of the repository
# that no longer exists. They are history and are deliberately NOT touched.
#
# `sed -i` is not used: the project forbids it, and it would give no report of
# what changed.
set -e

DIR=${0:A:h}
DRY=0
[[ "$1" == "--dry-run" ]] && DRY=1

python3 - "$DIR" "$DRY" <<'PY'
import sys, pathlib

d = pathlib.Path(sys.argv[1])
dry = sys.argv[2] == "1"

NEW = "$HOME/projects/ScottProjects/ScottDomains"

# file -> (exact old line, new line)
edits = {
    "counts.sh":          ('pkg="ScottDomains/ScottDomains"',  f'pkg="{NEW}/ScottDomains"'),
    "module-counts.sh":   ('pkg="ScottDomains/ScottDomains"',  f'pkg="{NEW}/ScottDomains"'),
    "unused-theorems.sh": ('pkg="ScottDomains/ScottDomains"',  f'pkg="{NEW}/ScottDomains"'),
    "compile.sh":         ('pkg="$root/ScottDomains"',         f'pkg="{NEW}"'),
    "axioms.sh":          ('pkg="$root/ScottDomains"',         f'pkg="{NEW}"'),
    "numbered-status.sh": ('pkg="$root/ScottDomains"',         f'pkg="{NEW}"'),
    "mathlib-imports.sh": (
        'SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/ScottDomains/ScottDomains"',
        f'SRC="{NEW}/ScottDomains"'),
}

missing, changed = [], []
for name, (old, new) in edits.items():
    p = d / name
    if not p.exists():
        missing.append(f"{name}: file absent")
        continue
    text = p.read_text(encoding="utf-8")
    if old not in text:
        missing.append(f"{name}: expected line not found: {old}")
        continue
    n = text.count(old)
    if not dry:
        p.write_text(text.replace(old, new), encoding="utf-8")
    changed.append(f"{name}: {n} line(s)  {old}  ->  {new}")

for c in changed:
    print(("would change " if dry else "changed ") + c)
if missing:
    print()
    for m in missing:
        print("NOT APPLIED  " + m)
    sys.exit(1)
print(f"\n{len(changed)} script(s) repointed to {NEW}")
PY
