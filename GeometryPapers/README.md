# GeometryPapers

Euclidean-geometry formalization references for Dana.

- **`LeanEuclid-2405.17216.pdf`** — *Autoformalizing Euclidean Geometry*, Logan
  Murphy, Kaiyu Yang, Jialiang Sun, Zhaoyu Li, Anima Anandkumar, Xujie Si
  (arXiv:2405.17216, ICML 2024). Introduces the formal system **E** for
  diagrammatic Euclidean reasoning and a benchmark for autoformalization.

- **`LeanEuclid/`** — the accompanying Lean 4 development and benchmark
  (<https://github.com/loganrjmurphy/LeanEuclid>), cloned locally. Mathlib-based;
  defines system **E** in Lean. *Cloned locally and gitignored* (keeps its own
  `.git` — `git pull` there to update). Its Lean side (toolchain + Mathlib) is
  set up on this box; the full SMT proof-checking pipeline additionally needs
  **Z3, CVC5, and Python** (`pip install smt-portfolio openai`) per its README.
