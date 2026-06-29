---
name: auto-formalise
description: >
  Formalise the already-proven results of a given paper into Lean 4 + Mathlib, end-to-end to
  green. Use when you are handed a source whose theorems are ALREADY PROVED in the literature
  (a paper / textbook / arXiv id) and the task is faithful transcription + proving, NOT picking
  a research direction. Triggers: "formalise this paper", "formalise the results in <paper>",
  "autoformalise arXiv:XXXX", "formalise Theorem 3 of <source>", "formalise <seabed>'s paper".
  For taking a NEW/exploratory step outward from formalised territory (discover a research
  direction first, then formalise), this is the wrong skill — that is novel research work.
---

# auto-formalise — formalise a paper's proven results

This is the **autoformalisation-only** path: a source whose results are already established is
turned into green Lean. The "direction" is not discovered, it is *read off the paper* — plus
**batching** over the paper's results in dependency order. Everything from the skeleton onward is
the standard skeleton-first prove loop described in **Per-target loop** below.

> **The proving core.** The unit of work is a typechecking, `sorry`-bearing **skeleton** whose
> *statement* is frozen after human sign-off (no EVOLVE markers); many independent provers
> Ralph-loop on the body with per-turn compiler feedback; a *validator* gates admission (frozen
> statement intact + sorry/axiom-clean) and a metered prover-*oracle* (Aristotle) is called on
> stuck subgoals. There is **no** numerical / special-case test-lemma gate. What is specific to
> this skill is only (a) where targets come from (the paper, not a survey), and (b) that we run a
> *worklist* of them.

## Environment

- **Seabeds** = the user's per-paper Lean formalisation repos (separate repos under personal
  `github.com/yangdabei/`). `~/Documents/formalisation/` holds ONLY Lean seabeds; research repos
  live elsewhere under `~/Documents/`. Record both the seabed path and (if any) the research-repo
  path.
- **GPT-5.5 = `codex` CLI** (`~/.local/bin/codex`), NOT the API. Invoke with `codex exec
  "<prompt>"` from inside the seabed (a git repo, so no `--skip-git-repo-check`).
- **Aristotle** = `aristotlelib` 2.x in the seabed's `.venv`; an ATP used as a metered oracle on
  stuck subgoals and as a critic on complex finished proofs (Stage 4), not as the primary prover.
  Submission Lean files under `aristotle/aristotle-in/`, outputs under `aristotle/aristotle-out/`,
  job metadata in `aristotle/aristotle-jobs.json`; never print or commit the API key (local
  `.env`).
- **Retrieval**: `scripts/theorem-search` (arXiv + restatements; NOT a Mathlib search) and
  `scripts/lean-search` / loogle / `lean-lsp-mcp` (Mathlib). Keep both.
- **Concurrency**: isolate each prover in its own `git worktree` (branch `auto/<topic>-p<i>`) so
  they don't race on imports / `.lake` / untracked files. Release every worktree when done.
- Per-seabed `.mcp.json` registers the Lean LSP server and (optionally) the theoremsearch MCP
  server.

## Inputs

- **Source** — the paper (PDF/TeX in `<seabed>/papers/`, or an arXiv id to fetch). Ground truth.
- **Selection** — which results: `all`, a list (`Thm 1, Lemma 3.2, Eq. 12`), or `main` (the
  headline theorem + its stated prerequisites). Ask once if unspecified.
- **Seabed** — the target Lean repo. If greenfield, scaffold from `../autoformalisation-template`
  first (see Environment).

## Stage F0 — Target extraction + worklist (HUMAN-IN-THE-LOOP)

Instead of discovering a direction, read it off the paper. No survey, no codex direction-picking.

1. **Read the source.** Extract every selected result *verbatim*: its statement, its label
   (`Thm 1` / `eq:foo` / §3.2), its hypotheses, and any constants/closed-forms it names. Note
   each result's **literature dependencies** (results it cites but does not prove) — these become
   `status.main_results[].literature_dependencies` / `alignment` `literature-dependency` rows,
   not things to prove.
2. **Order by dependency.** A paper's Lemma 1 before the Theorem 2 that uses it. Prerequisites in
   the same paper are formalised first; cited external results are recorded as dependencies, not
   targets. Tag any result whose paper proof is informal ("easy to see", "clearly") — these need
   the *proof strategy* validated, not just the statement (that phrase is a red flag).
3. **Write the worklist** to `<seabed>/notes/<source>-worklist.md`: ordered list, each row =
   `paper label → intended Lean name → module → deps → status`. This is the batch plan and the
   seed of the `alignment` table.
4. **Human confirms the worklist + the transcribed statements** before any proving. This is the
   batch statement-freeze: the human is signing off that the Lean statements you are about to
   commit to *faithfully say what the paper says*. Cheap; do it up front for the whole list.

## Per-target loop (Stages 1 → 5)

Run each worklist item, in order, through the skeleton-first prove loop. Each stage below gives
the base step plus the paper-specific adaptation:

- **Stage 1 (skeleton).** Draft the Lean **target statement** (declaration signature) that tracks
  the paper's `<label>`, body `:= by sorry`. Consult codex — but here the statement is
  *transcribed*, not invented, so the consult shifts from "is this the right direction?" to
  **"does this Lean statement faithfully capture the paper's `<label>`?"** Keep the deliberation —
  a wrong transcription is the dominant failure mode here — but it is lighter. The skeleton must
  **typecheck** before the stage closes; pin the frozen statement to `sketches/<topic>.frozen.lean`
  (`cp` to a read-only baseline) and cite the paper label in the docstring. This source-faithful
  transcription + human sign-off **is** the misformalisation guard — there is no numerical or
  special-case test-lemma gate; read the statement against the source carefully here.
- **Stage 2 (prior-art).** `scripts/theorem-search` the statement — if the *paper itself* already
  has a Lean formalisation, surface it before re-proving. `scripts/lean-search` / loogle /
  `lean-lsp-mcp` + `rg` through `.lake/packages/mathlib/` for the Mathlib lemmas to build on; feed
  the hits into the skeleton as comments so the provers reach for them first.
- **Stage 3 (prover fan-out).** Spawn **N prover subagents** (Agent tool), each in its own
  `git worktree` (`auto/<topic>-p<i>`), each Ralph-looping on the same skeleton with per-turn
  `lean-lsp-mcp` feedback; keep the first to reach *validated green*, else the best partial. Edit
  the **proof body** only; the frozen statement stays fixed. Where the paper leaves a constant
  implicit, the proof pins it (an ordinary `def`); usually the value is given and the work is the
  proof. Use the Mathlib-first ladder (below) and escalate stuck subgoals to the Aristotle oracle
  at episode boundaries only.
- **Stage 4 (Aristotle).** Run the critic on every non-mechanical result (skip short/mechanical
  lemmas). The honesty audit's **F1 (target-restating helper)** check matters most here: an
  informal-paper proof tempts a prover to offload the hard step into a helper that morally
  restates the claim. Also audit **F2** (a step leaning on a hallucinated "known" lemma). A
  *strategy* proposal from the critic escalates to the human; subgoal proofs from the oracle role
  do not (they still pass `scripts/validate`).
- **Stage 5 (close).** Update `formalization.yaml` per result as you go (don't batch to the end):
  add the `alignment.statements` row (`paper label → Lean decl → module → proved`), bump
  `status.main_results` / `sorry_count` / `axioms`, and record `fidelity.divergences` for any
  deviation (weakened hypothesis, renamed lemma, conditional interface threaded as an explicit
  hypothesis). Mark the worklist row ✓.

Batch rhythm: finish (green + validated + yaml row) one target before starting the next, so a
dependency is real Lean before its dependent needs it. Independent targets may fan out in
parallel worktrees (`auto/<topic>-p<i>`), same as Stage 3.

## Mathlib conventions quick-check (enforce on every declaration)

Distilled from `cameronfreer/lean4-skills`; full detail in
[`../lean-references/mathlib-style.md`](../lean-references/README.md).

- **100-character line width** (not 80). Keep a line that fits ≤100 on one line; see mathlib-style
  for break strategies past 100.
- **`fun x ↦ …`** (`\mapsto`) for ordinary math lambdas, **not** `fun x => …`. Use `=>` only for
  `match`/`do` branches and metaprogramming callbacks.
- **`show P by tac`** for tactic proofs; `show P from term` only for term proofs.
- **Never change a frozen statement, type signature, or docstring, and never add an `axiom`,
  without explicit human sign-off.** A needed axiom is a Stage-1 conversation, not a quiet edit.
  (Docstrings are API; inline comments may be edited.)

## Tactic + verification defaults

- **Automation cascade** (tier-2 of the Mathlib-first ladder; stop on first success):
  `rfl → simp → ring → linarith → nlinarith → omega → exact? → apply? → grind → aesop`.
  `exact?`/`apply?` hit Mathlib (slow); `grind`/`aesop` are powerful but can time out.
- **Verification ladder**: `lean_diagnostic_messages` after every edit → `lake env lean
  <path/to/File.lean>` (run from repo root) as a per-file gate → `lake build` only at module
  boundaries / final. `scripts/no_sorry.sh` + `scripts/validate` + capstone `#print axioms`
  (`[propext, Classical.choice, Quot.sound]`) are the green bar.

## Done when

Every selected result is validated-green, its `formalization.yaml` `alignment` row reads
`proved` (or honestly `literature-dependency` / `in-progress`), the README "what's proved" table
matches, and a single retrospective (Stage 5) covers the batch. Honest partial coverage beats a
yaml that overclaims.
