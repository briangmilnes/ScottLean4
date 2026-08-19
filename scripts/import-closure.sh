#!/bin/zsh
# import-closure.sh — transitive import closure of a set of Lean modules within
# one package, and the package-external imports they pull in.
#
# Usage: scripts/import-closure.sh <module-prefix> [<module-prefix> ...]
#
#   scripts/import-closure.sh ScottDomains.EquilogicalSpaces
#
# Why this exists: deciding whether a subtree can be moved to another package
# needs the *transitive* closure, not the direct imports. Grepping `^import` in
# the subtree only shows depth 1, which understates the move by a large factor.
# Reports, in order: closure size, the in-package modules required outside the
# given prefixes, and the distinct external package roots (Mathlib, Std, …).
set -e

ROOT=${0:A:h}/..
LIB=$ROOT/ScottDomains

python3 - "$LIB" "$@" <<'PY'
import os, re, sys

lib = sys.argv[1]
prefixes = sys.argv[2:]

# module name -> file path, for every .lean under the library root
mods = {}
srcroot = os.path.join(lib, "ScottDomains")
for dirpath, _, files in os.walk(srcroot):
    if ".lake" in dirpath:
        continue
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(dirpath, f)
        rel = os.path.relpath(p, lib)[:-len(".lean")]
        mods[rel.replace(os.sep, ".")] = p

imp = re.compile(r'^import\s+([A-Za-z0-9_.]+)', re.M)
deps = {}
for m, p in mods.items():
    with open(p, encoding="utf-8") as fh:
        deps[m] = imp.findall(fh.read())

seeds = [m for m in mods if any(m == x or m.startswith(x + ".") for x in prefixes)]
print(f"seed modules matching {prefixes}: {len(seeds)}")

seen, stack, external = set(), list(seeds), set()
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    for d in deps.get(m, []):
        if d in mods:
            stack.append(d)
        else:
            external.add(d.split(".")[0])

inpkg = sorted(m for m in seen if m not in seeds)
print(f"transitive closure: {len(seen)} modules")
print(f"  of which seeds:   {len(seeds)}")
print(f"  in-package deps:  {len(inpkg)}")
print(f"library total:      {len(mods)} modules")
print()
print("=== in-package modules the seeds require ===")
for m in inpkg:
    print("  " + m)
print()
print("=== external package roots ===")
for e in sorted(external):
    print("  " + e)

lines = 0
for m in seen:
    with open(mods[m], encoding="utf-8") as fh:
        lines += sum(1 for _ in fh)
print()
print(f"total lines to move: {lines}")
PY
