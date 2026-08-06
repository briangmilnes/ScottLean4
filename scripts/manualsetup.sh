#!/bin/bash
# manualsetup.sh — the steps a human must perform to bring a Linux host to the
# state the two macs are in: ScottDomains builds against Mathlib, VS Code drives
# interactive proofs, and md2pdf.sh renders Markdown to PDF with zero missing
# glyphs. Root installs, GUI actions, and checks that need eyes on a screen.
#
# Read this and run the steps one at a time; do not execute it as a whole.
# Steps 1 and 4 prompt for the root password, and steps 5 and 7 are actions in
# the VS Code window, not shell commands.
#
# STATUS on this host (Linux 7.0.0-28-generic x86_64, X11/GDM) as of
# 2026-0806: every step below is DONE and round r0001 met all four acceptance
# criteria. The file is kept as the procedure for the next Linux host.
# See ScottDomains/reports/r0001-report-from-orchestrator-to-user-toolchain-audit.md.
#
# Already automated, no manual action: Mathlib fetch and build, the lakefile
# globs fix, both .vscode/settings.json files, and the per-platform font branch
# in scripts/md-pdf-header.tex.

REPO=/home/milnes/projects/ScottLean4

# ---------------------------------------------------------------------------
# 1. ROOT. Two packages, and only two.
#
#    zsh — scripts/md2pdf.sh is #!/bin/zsh and uses the zsh-only ${0:A:h} to
#    locate its header file. Installing zsh keeps one script working on both
#    platforms; rewriting it for bash would edit a file both macs execute.
#
#    texlive-fonts-extra — supplies STIX Two Text and STIX Two Math, the fonts
#    md-pdf-header.tex names. 629 MB download, 1.73 GB installed, for 5.2 MB of
#    font; step 2 is the cheap alternative.
#
#    NOT fonts-stix. That package is STIX 1.x — families STIXGeneral, STIX Math,
#    STIXSizeOneSym — and contains no STIX Two at all. Installing it fixes
#    nothing. texlive-science is also unused by this pipeline.
# ---------------------------------------------------------------------------
sudo apt-get install zsh texlive-fonts-extra

# ---------------------------------------------------------------------------
# 2. Alternative to texlive-fonts-extra: STIX Two from CTAN, no root, 5.2 MB.
#    Use this instead of step 1's second package on a disk-constrained host.
# ---------------------------------------------------------------------------
# mkdir -p ~/.local/share/fonts && cd /tmp \
#   && curl -LO https://mirrors.ctan.org/fonts/stix2-otf.zip \
#   && unzip -j stix2-otf.zip 'stix2-otf/*.otf' -d ~/.local/share/fonts \
#   && fc-cache -f

# ---------------------------------------------------------------------------
# 3. Confirm the fonts resolve. Note fc-list is the WRONG instrument after
#    step 1: texlive-fonts-extra installs into the texmf tree, where lualatex
#    finds fonts via kpathsea but fontconfig never indexes them. kpsewhich is
#    the correct test; after step 2 instead, fc-list is correct and kpsewhich
#    finds nothing.
# ---------------------------------------------------------------------------
kpsewhich STIXTwoText-Regular.otf STIXTwoMath-Regular.otf

# ---------------------------------------------------------------------------
# 4. Build Lean. No root. ~192 s for the olean fetch on a cold host (about
#    440 MB of download), ~2 s when ~/.cache/mathlib already holds the pinned
#    revision. Expect "Build completed successfully (3 jobs)." and exit 0.
# ---------------------------------------------------------------------------
cd "$REPO/ScottDomains" && lake exe cache get && lake build

# ---------------------------------------------------------------------------
# 5. GUI, not a command: reload the VS Code window so it picks up
#    .vscode/settings.json (lean4.input.languages now includes markdown, so the
#    \-abbreviations work in docs/*.md as well as in .lean files):
#      Shift+Ctrl+P  ->  "Developer: Reload Window"
#    Open ScottDomains as its own folder — its lakefile.toml requires Mathlib,
#    the repo root's does not, and the file watcher drops from 17,823 to 9,453
#    .lean files:
# ---------------------------------------------------------------------------
code "$REPO/ScottDomains"

# ---------------------------------------------------------------------------
# 6. Render a document and count missing glyphs. Acceptance criterion is 0 tofu
#    (repo precedent: commit 1137a05). pandoc discards the engine log, so the
#    count needs a separate lualatex run over the same .tex.
# ---------------------------------------------------------------------------
"$REPO/scripts/md2pdf.sh" "$REPO/ScottDomains/docs/PaperInventory.md" /tmp
pandoc "$REPO/ScottDomains/docs/PaperInventory.md" -s -o /tmp/tofu.tex \
  -H "$REPO/scripts/md-pdf-header.tex" -V geometry:margin=0.75in -V fontsize=10pt
cd /tmp && lualatex -interaction=nonstopmode tofu.tex >/dev/null 2>&1
echo "missing characters: $(grep -c 'Missing character' /tmp/tofu.log)"

# ---------------------------------------------------------------------------
# 7. GUI, not a command: confirm the interactive proof loop.
#    Open ScottDomains/ScottDomains/ExistingTheories.lean and check the infoview
#    renders. It is a #check catalog of the reused Mathlib declarations, so each
#    of the 8 #checks that elaborates is evidence the dependency resolved:
#    OmegaCompletePartialOrder, CompletePartialOrder, ScottContinuous,
#    ScottContinuousOn, Topology.IsScott, Topology.IsScottHausdorff,
#    OrderHom.lfp, OrderHom.gfp.
#
#    To read Mathlib source with a working infoview, open files under
#      ScottDomains/.lake/packages/mathlib/
#    NOT the repo-root mathlib/ copy — that has no lean-toolchain and no
#    lakefile, so the extension walks up to the Mathlib-less root project and
#    the infoview fails there. The two trees are byte-identical at the same
#    commit, so nothing is lost by reading the .lake copy.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# 8. Watch disk. ScottDomains/.lake costs 7.4 GiB and this volume sat at 97%
#    with 15 GiB free after the build. Playground/ and Beeson/lean4/ pin the
#    same Mathlib and are unbuilt here; each would add roughly another 7 GiB,
#    so two more such builds exhaust the volume. The shared olean cache
#    (~/.cache/mathlib, 874 MiB) is not the cost — the per-project decompressed
#    package trees are.
# ---------------------------------------------------------------------------
df -h "$REPO"
du -sh "$REPO/ScottDomains/.lake" ~/.cache/mathlib

# ---------------------------------------------------------------------------
# 9. Optional insurance, no effect on an X11 session. elan is on PATH only
#    because /etc/gdm3/Xsession sources ~/.profile; a Wayland session skips
#    that file and the Lean server would stop finding elan.
# ---------------------------------------------------------------------------
# mkdir -p ~/.config/environment.d && printf 'PATH=%s/.elan/bin:${PATH}\n' "$HOME" > ~/.config/environment.d/10-elan.conf
