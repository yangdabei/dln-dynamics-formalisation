# DlnDynamics — project memory for Claude Code

Lean 4 + Mathlib formalization of the core analytical results of Saxe,
McClelland & Ganguli (2014), *Exact solutions to the nonlinear dynamics of
learning in deep linear neural networks* (arXiv:1312.6120). The compiled paper
is `saxe-2014.pdf` at the repo root. The TeX source files are in @arXiv-1312.6120v3. 

## Scope (what is formalized)
- `DlnDynamics/Basic.lean` — the two-mode gradient flow `IsABFlow` (Saxe Eq.
  `ab_dyn`), the closed-form solution `uf` (Eq. `u_soln`), and `denom_pos`.
- `DlnDynamics/Conservation.lean` — `a² − b²` is a constant of motion
  (`ab_conserved`, Saxe §1.3).
- `DlnDynamics/ClosedForm.lean` — `uf` solves the reduced logistic ODE
  `τ u' = 2 u (s − u)` (`uf_hasDerivAt`, Eq. `sigmoidal_dyn`) with `uf 0 = u₀`.

Deferred, not yet formalized: the `t → ∞` limit `uf → s`, ODE uniqueness, and the
depth-`N` law (Eq. `deep_dyn`). Do not stub these; add them as real theorems when
the time comes.

## Conventions
- Paper regime `0 < u₀ < s`, `0 < τ` carried explicitly as hypotheses.
- Cite the Saxe equation label (`ab_dyn`, `sigmoidal_dyn`, `u_soln`) in each
  theorem's docstring.
- Skeleton-first: get a correct *statement* compiling before filling the proof.
  A wrong statement is worse than a visible gap.

## Proof Workflow

**Skeleton correctness takes priority over filling in sorries.** A sorry with a correct statement is valuable (it documents what remains to prove); a sorry with a wrong statement is actively harmful (it creates false confidence and wasted work downstream). When auditing reveals incorrect lemma statements, fix them before working on other tractable sorries — even in other files. An honest skeleton with more sorries beats a dishonest one with fewer.

**Verify theorem statements against the source paper early.** Before building infrastructure, read the primary source to confirm: (1) single application or repeated/recursive? (2) essential tree structures or bookkeeping? (3) definitions match exactly? Informal sources can mislead about the precise result. Read primary sources at the design stage.

**Formalization adds lemmas for implicit hypotheses.** When an informal proof says "X follows because the construction has property P," the formal proof needs an explicit predicate for P and a lemma proving the construction satisfies it. Having more intermediate lemmas than the paper is EXPECTED — the extra lemmas make implicit paper assumptions explicit. Don't conflate "fewer lemmas" with "closer to the paper"; the paper's argument structure matters more than its lemma count.

Before attempting a `sorry`, estimate the probability of proving it directly (e.g., 30%, 50%, 80%) and report this. If the probability is below ~50%, first factor the `sorry` into intermediate lemmas — smaller steps that are each individually likely to succeed. This avoids wasting long build-test cycles on proofs that need restructuring.

**Recognize thrashing and ask the user.** After 3+ failed approaches to the same goal, stop and ask for guidance. Signs: repeated restructuring, oscillating between approaches, growing helper count without progress. A 2-minute conversation is cheaper than 30 minutes of failed builds.

**Never silently abandon an agreed plan.** If a plan was approved and a step turns out harder than expected, do NOT silently switch to a shortcut (e.g., replacing a proof with `native_decide` or `sorry`). Always confirm radical plan changes with the user first — explain what's hard, what the alternatives are, and let them decide. A 2-minute conversation about changing course is far cheaper than discovering the change broke assumptions downstream.

**Assess proof risk before significant work.** Break non-trivial theorems into phases with risk levels: LOW (definition, direct proof), MEDIUM (standard argument, uncertain details), HIGH (novel connection, unclear if approach works). Identify the highest-risk phase, document fallback plans (axiomatize, defer, reformulate), and validate the critical bottleneck lemma before building dependencies. Escalate to user after 2-3 failed attempts on a MEDIUM+ phase.

**Analyze uncertain lemmas in natural language before formal proof attempts.** Work through the math with concrete examples BEFORE formalizing: (1) test the proof idea with specific numbers, (2) look for counterexamples, (3) verify each step informally, (4) only then formalize. Informal analysis is instant vs. 20s-2min build cycles. A careful analysis can reveal a lemma is unprovable (saving days) or clarify the exact proof structure needed.

**Keep proofs small and factored.** If a proof has more than ~3 intermediate `have` steps, factor them into standalone lemmas. Each lemma should have a small, independently testable interface — this avoids churning where fixing one step breaks steps below it.

**When a user suggests an approach or lesson, rephrase it for CLAUDE.md** rather than copying verbatim. Lessons should be concise, actionable, and fit the existing style.

**Work autonomously on low-risk tasks once the path is clear.** When reduced to well-understood engineering (Mathlib interfacing, type bridging, assembling existing components), continue autonomously. Check in when hitting unexpected obstacles, discovering the approach won't work, or completing major milestones. Progress over permission when risk is low.

**Review subtle definitions interactively before building downstream infrastructure.** Definitions that involve distinguishability (e.g., 0-1 values vs labeled elements) or quantifier structure (∀ permutations vs ∀ Boolean sequences) can be subtly wrong in ways that only surface when attempting proofs. When a definition is the foundation for multiple sorry'd lemmas, validate it with the user before committing to downstream work.

**"Easy to see" in papers is a red flag for formalization.** When a paper says "it is easy to see" without proof, validate the *proof strategy* — not just the statement — before investing in Lean infrastructure. Always ask: "what is the proof, not just the claim?"

**Sanity-check formulas empirically.** Before a long proof, write a Python script with `numpy`/`scipy.integrate.quad` that evaluates the formula at specific parameter values and compares to numerical integration. A mismatch at this stage is much cheaper to find than mid-proof.

## Proof tactics

After completing each proof, reflect on what worked and what didn't. If there's a reusable lesson — a tactic pattern, a Mathlib gotcha, a refactoring that unlocked progress — add it here (not in auto memory). This file is the single source of truth for accumulated lessons, so they persist across machines.

## Mathlib API Reference (build out as we go)

## House rules
- No `sorry`, `admit`, `native_decide`, or new `axiom`s in committed code.
  `scripts/no_sorry.sh` enforces this and runs in CI.
- Standard Mathlib analysis tactics only; reach for `exact?` / `apply?` / Loogle /
  LeanSearch on lemma lookup. After ~3 failed approaches to a goal, stop and
  reassess rather than thrash.
- Numerically sanity-check any new closed form before proving it
  (`scripts/check_closed_form.py` is the template).

## MCP tooling and `lake` fallback

`.mcp.json` wires up **`lean-lsp-mcp`** (`uvx lean-lsp-mcp`), which talks to a
persistent `lake serve` LSP in the project root. **Use the MCP tools as the
default check-loop — read the goal state and diagnostics after every edit rather
than guessing — and reserve `lake build` for full verification.** A warm LSP
query is sub-second; a full `lake build` re-elaborates against all of Mathlib
(~90 s/file here), so it is the fallback, not the inner loop. Run `lake build`
once at the start of a session so imports are warm (avoids first-call timeouts).

Core loop (LSP-backed, fast, no network):
- `lean_diagnostic_messages` — all errors/warnings for a file; the primary "did
  my edit compile?" check.
- `lean_goal` — tactic state at a line/column; the workhorse for stepping a proof.
- `lean_term_goal` — expected type at a term hole.
- `lean_hover_info` — docs + signature for a symbol (LSP hover).
- `lean_completions` — identifiers/imports valid at a position.
- `lean_declaration_file` / `lean_references` — read a lemma's source / find uses.
- `lean_multi_attempt` — try several tactics at one position and compare the
  resulting goals; pick the winner without a rebuild.
- `lean_run_code` — run an independent snippet (`#check` / `#eval` / experiments).
- `lean_verify` — list the axioms a finished proof uses and scan for unsafe code
  (confirm no surprise axioms / `sorry`).

Lemma search (try the local one first; the rest are external and rate-limited to
~3 requests / 30 s):
- `lean_local_search` — ripgrep over the local project + stdlib (needs `rg`); no
  network.
- `lean_loogle` — Mathlib search by name / subexpression / type signature.
- `lean_leansearch` — natural-language search over Mathlib.
- `lean_state_search` / `lean_hammer_premise` — theorems / premises applicable to
  the current goal.

Fallback / recovery:
- `lean_build` (MCP) or `lake build` (shell) — full build + restart the LSP; use
  when the LSP state goes stale or the MCP server misbehaves.

Plain shell build (CI and first checkout):
    lake exe cache get      # once: download prebuilt Mathlib oleans
    lake build              # full verification
    bash scripts/no_sorry.sh
