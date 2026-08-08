#!/usr/bin/env bash
# scott1972-verify.sh — fetch the Mathlib cache and kernel-check Ericson's
# formalization of Scott's *Continuous Lattices* (1972), the artifact for
# arXiv 2606.30782.
#
#   scripts/scott1972-verify.sh [cache|build|all]     (default: all)
#
# Why a script rather than two shell commands:
#
#   * The artifact pins `leanprover/lean4:v4.30.0` while this project pins
#     v4.32.2. `lake --dir=<artifact>` does NOT switch toolchains — it runs the
#     *ambient* lake, and against a v4.30.0 package that fails while building
#     `Cache.IO`. elan selects the toolchain from the working directory, so the
#     build has to happen with the artifact as cwd. CLAUDE.md forbids `cd` in the
#     terminal and directs exactly this case into scripts/, which is where the
#     `cd` below lives.
#   * `lake exe cache get` pulls a **second, separate ~7 GB Mathlib** — the
#     artifact's v4.30.0 oleans cannot share this project's v4.32.2 checkout.
#     Measured before the first run: 31 GB free, disk at 94%.
#
# The artifact is third-party, keeps its own .git, and is gitignored (see
# /.gitignore). Its paper is tracked at
# ScottDomains/papers/Ericson 2026 … arXiv-2606.30782.pdf.
#
# Logs follow the project's LoggingStandard: one file per run, second-resolution
# timestamp in the name, ANSI stripped, role slot from the checkout path.
set -u

root=/home/milnes/projects/ScottLean4
art="$root/scott1972"
mode="${1:-all}"

[ -d "$art" ] || { echo "scott1972-verify: no artifact at $art — clone it first" >&2; exit 1; }

case "$root" in *-agent[0-9]*) role="${root##*-}" ;; *) role=orchestrator ;; esac
stamp=$(date +%Y%m%d-%H%M%S)
log="$root/ScottDomains/logs/scott1972-verify-$stamp.$role.log"
mkdir -p "$(dirname "$log")"

strip_ansi() { sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g'; }

{
  echo "# scott1972-verify $stamp"
  echo "# artifact toolchain: $(cat "$art/lean-toolchain")"
  echo "# project toolchain:  $(cat "$root/ScottDomains/lean-toolchain" 2>/dev/null || echo 'n/a')"
  echo "# mode: $mode"
} | tee "$log"

cd "$art" || exit 1

rc=0
if [ "$mode" = cache ] || [ "$mode" = all ]; then
  echo "--- lake exe cache get ---" | tee -a "$log"
  lake exe cache get 2>&1 | strip_ansi | tee -a "$log"
  rc=${PIPESTATUS[0]}
  [ "$rc" -eq 0 ] || { echo "scott1972-verify: cache get failed ($rc)" | tee -a "$log"; exit "$rc"; }
fi

if [ "$mode" = build ] || [ "$mode" = all ]; then
  echo "--- lake build Scott1972 ---" | tee -a "$log"
  /usr/bin/time -v lake build Scott1972 2>&1 | strip_ansi | tee -a "$log"
  rc=${PIPESTATUS[0]}
fi

sorries=$(grep -c "declaration uses 'sorry'\|declaration uses \`sorry\`" "$log" || true)
errors=$(grep -c "^error:" "$log" || true)
echo "scott1972-verify: exit $rc · sorry $sorries · errors $errors · log $log" | tee -a "$log"
exit "$rc"
