# GeometryPapers

Euclidean-geometry formalization references for Dana.

- **`LeanEuclid-2405.17216.pdf`** — *Autoformalizing Euclidean Geometry*, Logan
  Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar, Xujie Si
  (arXiv:2405.17216, ICML 2024). Introduces the formal system **E** for
  diagrammatic Euclidean reasoning and a benchmark for autoformalization.

- **`LeanEuclid/`** — the accompanying Lean 4 development and benchmark
  (<https://github.com/loganrjmurphy/LeanEuclid>), cloned locally and gitignored
  (keeps its own `.git`). Mathlib-based; defines system **E** in Lean.

  ### STATUS: does NOT build on this machine (macOS 26 / Tahoe)

  Mathlib itself built fine (5.1 GB, v4.19.0). The blocker is LeanEuclid's `smt`
  dependency — Kaiyu Yang's `lean-smt` fork (`github.com/yangky11/lean-smt`),
  pinned to Lean **v4.19.0**. That toolchain's linker builds native plugin dylibs
  whose `__DATA_CONST` segment lacks the **`SG_READ_ONLY`** flag, and macOS 26's
  dyld now *enforces* that flag and refuses to load them:

  ```
  dlopen(.../smt/.lake/build/lib/lean/Smt_Data_Sexp.dylib):
      __DATA_CONST segment missing SG_READ_ONLY flag
  Lean exited with code 134
  ```

  Failing modules: `Smt.Dsl.Sexp`, `Smt.Graph`, `Smt.Tactic.WHNFConfigurable`
  (and everything importing them). This is an upstream / OS-compatibility issue,
  not a local misconfiguration:

  - LeanEuclid's latest commit (`7c8f38b`, 2025-11-25) is still on **v4.19.0**;
    there is no newer revision to switch to.
  - Upstream `ufmg-smite/lean-smt` has moved to **v4.32.0** (a linker new enough
    to set the flag), but it can't be dropped into a v4.19.0 project without
    porting the whole of LeanEuclid + its Mathlib to v4.32.0.

  So the SMT-backed build is blocked. The **paper and Lean sources remain
  readable**; only `Smt`-importing modules stay red. (A separate, untried route
  would be to patch the `SG_READ_ONLY` flag into the locally-built dylibs.)
  The full SMT proof-checking pipeline would additionally need **Z3, CVC5, and
  Python** (`pip install smt-portfolio openai`) per LeanEuclid's own README.
