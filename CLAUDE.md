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

**Derivative combinators build the function at the `Pi` level, not as `fun r => …`.** `HasDerivAt.mul/.div/.sub/.add` produce `HasDerivAt (c * d) …`, `(c / d)`, `(f - g)` — pointwise `Pi` operations, *not* lambdas. So `convert <combinator> using 1` fails on the *function* argument (it compares `c / d` against your `fun r => …` or a `def` like `uf`), and the closing tactic then "made no progress" on the leftover goal. Don't fight `convert`: `rw` the derivative *value* into the exact combinator form, then discharge with `exact`, which checks full definitional equality and transparently unfolds your `def`, `Pi.div`, and `pow_two`. **Rule of thumb: prefer `exact`/defeq over `convert`/syntactic whenever the goal's function is a `def` or `fun` and the combinator's is a `Pi`-op.**

**To retarget a `HasDerivAt`'s derivative to a nicer expression,** prove `<combinator-derivative> = <nice form>` (by `field_simp`/`ring`) and `rw [show … = … by …] at h; exact h` — or `rw` the goal's stated derivative into the combinator form and `exact <combinator>`. `convert … using 1/2` does **not** reliably expose the scalar derivative equation for `HasDerivAt` (it unfolds through `HasDerivAtFilter`/`HasFDerivAt`).

**A bare `_` for the derivative in a term-mode `have h : HasDerivAt f _ x := term` can fail** with "don't know how to synthesize placeholder for argument `f'`" when `f` is a `def` that doesn't unify *syntactically* with `term`'s function. Give the explicit value, or use a tactic proof (`:= by unfold f; exact term`).

**`field_simp` sometimes closes the goal by itself** (it runs a `ring`-normalizer), so a trailing `; ring` then errors `no goals`; other times it leaves a polynomial identity that needs `ring`. Don't reflexively chain `field_simp; ring` — check which case applies. `field_simp` also needs the relevant `_ ≠ 0` facts *in context*; stage them first (`have hDne := (denom_pos …).ne'`).

**Keep an opaque subterm (e.g. `Real.exp (2*s*t/τ)`) as a single `ring` atom** by building it from ONE shared `HasDerivAt` for the inner function, so every occurrence is *syntactically identical*. `ring` treats it as one variable only if the terms match exactly — a differently-associated inner argument silently becomes a second atom and `ring` fails.

**Prefer `pow_two` + `.mul` over `.pow 2`** when the result feeds `ring`/`rw`/`exact`: `.pow n` emits `↑n * f x ^ (n-1) * f'` with a `Nat.cast` and an unreduced `n-1` that trip term-matching. `(h.mul h)` is cast-free.

**Confirm gap-freeness with `#print axioms <thm>`** (or `lean_verify`): expect `[propext, Classical.choice, Quot.sound]`. A `sorryAx` is a real hole that the text-based sorry-gate won't catch if it entered via a dependency.

**Grep the Mathlib source for exact signatures instead of recalling them** — `_root_.` prefixes, argument order, and the exact derivative form are not reliably memorable. `grep -rn "theorem HasDerivAt.div " .lake/packages/mathlib/Mathlib/` resolved three bugs at once this session.

## Mathlib API Reference (build out as we go)

Derivative combinators (`Mathlib/Analysis/Calculus/Deriv/*`). The *function* comes out as a `Pi`-op (see Proof tactics); these *derivative* forms are exact:
- `HasDerivAt.mul (hc) (hd) : HasDerivAt (c * d) (c' * d x + c x * d') x`
- `HasDerivAt.div (hc) (hd) (hx : d x ≠ 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x`
- `HasDerivAt.sub (hf) (hg) : HasDerivAt (f - g) (f' - g') x`  — also `.add`, `.add_const`, `.sub_const`
- `HasDerivAt.const_mul (c) (hf) : HasDerivAt (fun x => c * f x) (c * f') x`  — also `.div_const c`
- `HasDerivAt.exp (hf) : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x`
- `HasDerivAt.pow n (hf) : HasDerivAt (fun x => f x ^ n) (↑n * f x ^ (n-1) * f') x`  (casts — see tactics)
- `hasDerivAt_id (x) : HasDerivAt id 1 x`;  `HasDerivAt.deriv : … → deriv f x = f'`;  `.differentiableAt`

Constancy (`Mathlib/Analysis/Calculus/MeanValue.lean`):
- `is_const_of_deriv_eq_zero (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x = 0) (x y) : f x = f y` (note the `_root_.` prefix; `is_const_of_fderiv_eq_zero` is the normed-space version)

Real / order lemmas used:
- `Real.exp_pos`, `Real.exp_zero`
- `one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a`
- `div_eq_iff (hc : c ≠ 0) : a / c = b ↔ a = b * c`

Forward pointers (not yet used):
- Gradients (next session — deriving the ODE from the loss): `HasGradientAt` / `gradient` in `Mathlib/Analysis/Calculus/Gradient/Basic.lean`, bridged to `fderiv`/`HasDerivAt` via `hasGradientAt_iff_hasFDerivAt`.
- ODE uniqueness (time analysis, later): `ODE_solution_unique_of_mem_Icc` in `Mathlib/Analysis/ODE/ExistUnique.lean` (set-local Lipschitz; the bare `ODE_solution_unique` needs GLOBAL Lipschitz — won't fit a quadratic RHS like `2u(s-u)`).
- Limits (`t→∞`, later): `Real.tendsto_exp_atTop`, `tendsto_inv_atTop_zero`, `Filter.Tendsto.div`.
- Mathlib has NO SVD *factorization* (only `LinearMap.singularValues`); the symmetric spectral theorem + PSD machinery exist if the full matrix→mode reduction is attempted.

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
