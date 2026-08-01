# For Dana — working in ScottLean4

Practical advice for writing and checking Lean 4 proofs in this workspace, using
VS Code and Claude Code. Read this once end to end; each section stands on its
own afterward.

## 1. The tools, and what each one is for

- **VS Code** — the editor. It runs the Lean server, shows the proof goal state,
  and has a terminal built in. This is where the work happens.
- **Lean 4** — the proof language and its kernel. You write definitions and
  theorems; the kernel checks that each proof actually proves its statement.
- **Claude Code** — an assistant that reads `CLAUDE.md` in this folder and works
  as a Lean 4 expert. Ask it to draft a proof, explain a tactic, or find the
  relevant Mathlib lemma. It states what it proved and under which assumptions.

## 2. Installing Lean 4 in VS Code

1. Open the **Extensions** panel (⇧⌘X) and install **Lean 4**
   (`leanprover.lean4`). It installs and manages the Lean toolchain for you
   through a tool called `elan` — you do not install Lean separately.
2. Open this folder: **File ▸ Open Folder…**, select `ScottLean4`.
3. Open a `.lean` file. The Lean server starts on its own. The **first** start
   downloads the toolchain and can take a few minutes; later starts are fast.

## 3. The goal view (the Infoview)

This is the center of interactive proving.

- With a `.lean` file open, the **Lean Infoview** panel opens on the right. If it
  is closed, open the command palette (⇧⌘P) and run **Lean 4: Infoview: Toggle**.
- Put the cursor inside a proof. The Infoview shows the **goal state** at that
  point: the hypotheses currently in scope, and the proposition still to prove.
- Move the cursor line by line through the proof. Each tactic transforms the
  goal; watch the goal shrink as hypotheses are introduced and cases are closed.
  When the goal reads **"No goals,"** the proof is complete.
- A red squiggle plus a message in the Infoview means the kernel rejected that
  step. Read the message: it names the goal it could not close.

## 4. Reading the Markdown files in this project

The `.md` files (this one, `README.md`, `CLAUDE.md`) are **Markdown**: plain text
with light formatting marks.

- **Read them in VS Code.** Open the file and press **⇧⌘V** for a rendered
  preview, or click the split-preview icon at the top-right of the editor.
- **A web browser does not render Markdown.** Point Safari or Chrome at a `.md`
  file and you see the raw source (the `#`, `|`, and backticks), not formatted
  text. No browser renders Markdown on its own.
- To open a local file in a browser at all, type a **`file://` URL** in the
  address bar — three slashes, then the absolute path, e.g.
  `file:///Users/<you>/projects/ScottLean4/README.md`. You will still see raw
  Markdown; use VS Code's preview for a formatted view.
- The `ComputAItionalThinking` repository is also on GitHub, which renders
  Markdown server-side:
  `https://github.com/briangmilnes/ComputAItionalThinking`.

## 5. The terminal

- Open a terminal inside VS Code with **Terminal ▸ New Terminal**. It opens in
  the project folder.
- This terminal is where Lean compiles a whole project: run `lake build` to
  build, once a `lakefile` exists.
- The shell prompt shows the current directory. Shortcuts `up1`, `up2`, `up3`,
  `up4` move up one, two, three, or four directory levels (`up2` is `cd ../..`).

## 6. Terminology this project keeps precise

- **Verified** means **formally verified**: the Lean kernel accepted a proof of a
  stated proposition. A successful `lake build` or a passing test is **"built and
  tested,"** not "verified." The distinction matters — a program can build and
  still be wrong; a verified theorem cannot be false under its stated
  assumptions.
- The imported ruleset asks the assistant to name mechanisms and measured
  outcomes rather than use analogies or metaphors, so its reports say what a
  proof establishes and under which axioms. Read
  `ComputAItionalThinking/ComputAItionalThinkingRules.md` for the full rules.

## 7. A first proof to try

Once a Lean file is open, this is a complete, kernel-checkable proof — type it
and watch the Infoview reach "No goals":

```lean
theorem and_comm_example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
```

Put the cursor after `obtain …` to see the two hypotheses `hp : p` and `hq : q`
appear, then after `exact …` to see the goal close.
