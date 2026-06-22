# DlnDynamics — project memory for Claude Code

Lean 4 + Mathlib formalization of the core analytical results of Saxe,
McClelland & Ganguli (2014), *Exact solutions to the nonlinear dynamics of
learning in deep linear neural networks* (arXiv:1312.6120). The compiled paper
is `saxe-2014.pdf` at the repo root. The TeX source files are in @arXiv-1312.6120v3. 

## Scope (what is formalized)

The full **3-layer** chain `network gradient descent → matrix flow → SVD basis →
decoupled modes → scalar ab_dyn → conserved quantity + closed-form sigmoidal solution`
is formalized end-to-end and gap-free (balanced / orthogonal-mode regime, square
correlation matrix). Modules:
- `Basic.lean` — two-mode gradient flow `IsABFlow` (Eq. `ab_dyn`), closed form `uf`
  (Eq. `u_soln`), `denom_pos`.
- `Conservation.lean` — `a² − b²` constant of motion (`ab_conserved`, §1.3).
- `ClosedForm.lean` — `uf` solves the logistic `τ u' = 2 u (s − u)` (`uf_hasDerivAt`,
  Eq. `sigmoidal_dyn`) with `uf 0 = u₀`.
- `GradientFlow.lean` / `Network.lean` — per-mode loss gradient flow ⇒ `IsABFlow`.
- `MatrixFlow.lean` (Phase A) — matrix flow `wb_avg` from gradient descent.
- `SVDReduction.lean` (Phase B) — SVD change of variables ⇒ decoupled `wbo_dyn`
  (`IsSVD` hypothesis).
- `ModeDynamics.lean` (Phase C) — mode extraction `a_dyn`/`b_dyn` (competition sums).
- `InvariantManifold.lean` (Phase D-1) — reduction on the manifold `isABFlow_of_modeFlow`.
- `ManifoldInvariance.lean` (Phase D-3) — forward-invariance *in time* via ODE uniqueness;
  hypothesis-free balanced headline.
- `SVDExistence.lean` (Phase E) — SVD *existence* for any square `Sg` (`exists_isSVD`),
  discharging `IsSVD`; end-to-end `exists_mode_dynamics_of_gradFlow`.
- `DeepDynamics.lean` (depth-`N`) — the **depth-`N` law** (Eq. `deep_dyn`): full `m`-scalar
  deep gradient flow `IsDeepFlow` on `E = (1/2τ)(s − ∏ aᵢ)²`, conserved quantities
  `aᵢ² − aⱼ²` (`deepFlow_conserved`), symmetric reduction (`isDeepSymFlow_of_symmetric`), and
  `u = aᵐ` obeying `τ u' = (N_l−1) u^{2−2/(N_l−1)}(s − u)` (`deep_dyn`), recovering
  `sigmoidal_dyn` at `m = 2` (`deepSym_hasDerivAt_two`).
- `DeepMatrixFlow.lean` (depth-`N` Phase A) — derives the `N_l`-layer matrix gradient flow
  `multilayer_dyn` (Eq. `multilayer_dyn`) from gradient descent on `E = ½‖Σ³¹ − ∏W‖²`
  (equal-size square layers): ordered product `prodDesc` (a `List.prod`, matrices don't
  commute) + product split `prodDesc_update`/`prodDesc_split`, the unified bilinear
  entry-derivative `hasDerivAt_loss_layer` (`∂/∂X ½‖S−AXB‖² = −Aᵀ(S−AXB)Bᵀ`),
  `IsDeepMatrixGradFlow` ⇒ `multilayerFlow_of_gradFlow`. Also `prodDesc_telescope` (the
  `Rₗ` change-of-variables cancellation).
- `DeepReduction.lean` (depth-`N` Phases B–C) — the change of variables + mode extraction.
  Sub-range telescoping `aboveProd_factored`/`belowProd_factored` (prefix/suffix products
  ⇒ `R_m diag R₍ₗ₊₁₎ᵀ`, `Rₗ diag R₀ᵀ`); the mode-decoupling cancellation `flowval_conj`
  (conjugating the matrix velocity by the frames ⇒ diagonal of scalar deep-flow velocities);
  `isDeepFlow_of_gradFlow` (each mode obeys `IsDeepFlow`) and the end-to-end
  `deep_dyn_of_gradFlow` (`N_l`-layer gradient descent ⇒ `deep_dyn` on the symmetric
  submanifold). **The depth-`N` matrix reduction is complete** (equal-square layers,
  diagonality-in-frame as a hypothesis).

**Next steps (agreed direction):**
1. **Time equation** — the `t → ∞` limit `uf → s` and the learning-time integral
   `t(u)`/`u_int` (Eq. `u_int`) (`ClosedForm` currently verifies the *solution*, not the
   integration or the asymptotics). The more self-contained milestone.
2. **Infinite-depth limit** — `τ u' = N_l u²(s − u)` (Eq. `inf_dyn`) and its learning
   time `t(u)` (Eq. `inf_tc`), the `N_l → ∞` companion of `deep_dyn`.
3. **Symmetric-manifold forward-invariance in time** — the depth-`N` analog of
   `ManifoldInvariance` (ODE uniqueness), discharging the diagonality-in-frame hypothesis
   of `DeepReduction`.

Also deferred: unbalanced / hyperbolic dynamics (Appendix A, `a ≠ b`; the manifold theorem
already takes scalar solutions as a hypothesis) and rectangular `Σ³¹`. Do not stub any of
these; add them as real theorems when the time comes.

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

**Make the Lean proof structure mirror the human/paper proof.** Each step of the paper's argument should be its own named lemma or labelled `have`, in the paper's order, so a human can read the formal proof against the source line-by-line (e.g. `competition_vanishes` ↔ "the modes don't compete", then "project onto rᵅ" ↔ `HasDerivAt.dotProduct_const`). Prefer this even when a single opaque `simp`/`nlinarith` would close the goal faster — auditability against the source is the priority. A proof that only a machine can follow is a liability for a formalization whose point is to certify the paper.

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

**For a *symbolic* exponent `m`, `.pow m` IS the right tool — retarget its value by `rw [show … by ring, hpow]`.** The depth-`N` law `deepSym_hasDerivAt` needs `(fun r => a r ^ m)'`; `(h.ha t).pow m : HasDerivAt _ (↑m * a t^(m-1) * a') t`. Collapse the doubled power with `hpow : a t^(m-1) * a t^(m-1) = a t^(2*(m-1)) := by rw [← pow_add, two_mul]`, applied after a `ring` step that exposes the pair: `rw [show ↑m * a t^(m-1) * (… * a t^(m-1) / τ) = ↑m * … * (a t^(m-1) * a t^(m-1)) / τ from by ring, hpow] at key`. Then `exact key`. (`(m:ℝ)` literally matches the `↑m` that `.pow` emits.)

**Specialize a general `HasDerivAt` at a numeral exponent with `norm_num at key`.** To derive the `m = 2` case from a `∀ m` lemma: `have key := general h t; norm_num at key` reduces `↑(2:ℕ) → 2` and the Nat exponent `2*(2-1) → 2` in `key`'s value in one shot; a final `rw [show … by ring] at key; exact key` reorders factors to the target. (`deepSym_hasDerivAt_two` ↔ `sigmoidal_dyn` cross-check.)

**Confirm gap-freeness with `#print axioms <thm>`** (or `lean_verify`): expect `[propext, Classical.choice, Quot.sound]`. A `sorryAx` is a real hole that the text-based sorry-gate won't catch if it entered via a dependency.

**Grep the Mathlib source for exact signatures instead of recalling them** — `_root_.` prefixes, argument order, and the exact derivative form are not reliably memorable. `grep -rn "theorem HasDerivAt.div " .lake/packages/mathlib/Mathlib/` resolved three bugs at once this session.

**Bridge a `def`'s `^2`/`Pi`-op to a `.mul` combinator with `simp only [theDef, pow_two]` then `exact`.** For `HasDerivAt (fun x => myDef …) v x` where `myDef` unfolds to `(…)^2/2`: build `h := (h1.mul h1).div_const 2` from the inner `h1`, then `simp only [myDef, pow_two]` (rewrites the goal's function *under the binder* into the `(…)*(…)/2` form the combinator produced), `rw` the derivative value into the combinator's exact shape (`(c'·d + d·c')/2`, including any un-simplified `1*b`/`a*1` from `mul_const`/`const_mul`), then `exact h`. `^2` is *not* defeq to `x*x` (`npow` vs `mul`), so the `pow_two` rewrite is mandatory; `id x` *is* defeq to `x`, so leftover `id` from `hasDerivAt_id` needs no cleanup.

**Drop an additive constant from a partial derivative with `.add_const`.** To show two losses differing by a weight-independent constant have the same gradient: prove the function identity `(fun a => Lbig a) = (fun a => Lsmall a + c)` by `funext; exact <algebra lemma>`, `rw` it, then `exact (hasDerivAt_Lsmall …).add_const _`. Lets a network-loss partial reuse the abstract-loss partial verbatim.

**Expand `∑ (f − c·g)²` into separate sums with `mul_sum` + `← sum_sub_distrib` + `← sum_add_distrib`, close with `sum_congr rfl (fun _ _ => by ring)`.** Pull every scalar inside its sum (`Finset.mul_sum`), then merge the sums back into one (`← Finset.sum_sub_distrib`, `← Finset.sum_add_distrib`) so a single per-term `ring` finishes. Keep an irreducible sum (e.g. `∑ yμ²`) as a `ring` atom by leaving it untouched on both sides.

**Put a `deriv …` directly in a `structure` field, then collapse it with `.deriv`.** A gradient-flow predicate can read `HasDerivAt a (-(deriv (fun x => L s x (b t)) (a t)) / τ) t`; downstream, `rw [(hasDerivAt_L_fst …).deriv] at hflow` turns the `deriv` into the closed form and a `show … = … by ring` retargets the value. Reads like the math (`a' = −∂ₐL/τ`) and stays honest (references `L`).

**LSP `lean_diagnostic_messages` returning `success:false, items:[]` means "not elaborated yet", not "clean".** Happens when a file imports a *new* sibling module not yet compiled to oleans. Don't read it as success — run `lake build` (which compiles the dependency) and trust that.

**`Matrix`'s normed/topology instances are non-instances activated by `open Matrix`** (`Matrix.normedAddCommGroup := fast_instance% Pi.normedAddCommGroup`, scoped). Consequence for matrix-valued `HasDerivAt`: `Pi` lemmas like `hasDerivAt_pi` will NOT `rw` (the goal carries `instTopologicalSpaceMatrix`, the lemma `Pi.topologicalSpace` — syntactically distinct) but DO apply through `exact`/`apply`, which unify up to defeq (`fast_instance%` is defeq to the `Pi` instance). **Bundle entrywise derivatives in term mode:** `hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun l => <entry proof>`, never `rw [hasDerivAt_pi]`. (Needs `open Matrix` in scope for the instances at all — without it, `HasDerivAt` on a `Matrix` won't even typecheck.)

**`HasDerivAt.sum` yields a sum-*of-functions*-applied, not a function-of-sum.** Nesting it for `fun x => ∑ i, ∑ j, body` gives a goal whose function is `(∑ i, ∑ j, fun x => body) x` — defeq-blocked from `∑ i, ∑ j, body[x]` by `Finset.sum_apply` (a lemma, NOT beta). Close the final `exact` with `simpa only [Finset.sum_apply] using <built deriv>`.

**Take an entry partial derivative as a directional derivative along `Matrix.single k l 1` at `0`** (`Matrix.single` = the single-entry matrix, formerly `stdBasisMatrix`). `fun x => loss (A + x • single k l 1)` is then a sum of squares of functions *affine in `x`*, so the Layer-1/2 squared-affine technique applies directly — no `Function.update` gymnautics, and `single`'s selector lemmas collapse the sum (see API).

**Annotate `fun (x : ℝ) =>` and `single k l (1 : ℝ)` when the body smuls a real matrix.** An unannotated scalar `x • M` / literal `1` in a `Matrix _ _ ℝ` context defaults to `ℕ`, surfacing as `failed to synthesize NontriviallyNormedField ℕ` / `HSMul ℕ …` — a misleading error whose real cause is the missing `: ℝ`.

**Rectangular matrix `*` is heterogeneous `HMul`, so the homogeneous smul-mul lemmas don't fire.** `smul_mul_assoc`/`mul_smul_comm` are stated for `Mul` (one type); a rectangular product `(a•M)*N` (different shapes) is `HMul`, so `rw` reports "did not find pattern `?r • ?x * ?y`". Use the `Matrix`-specific `Matrix.smul_mul : (a•M)*N = a•(M*N)` and `Matrix.mul_smul : M*(a•N) = a•(M*N)`.

**To expose a *mid-product* pair like `Vᵀ*V` or `U*Uᵀ` for `rw [hV]`, target the exact grouping with `rw [show <flat> = <regrouped> from by simp only [Matrix.mul_assoc]]`.** Neither full left- nor right-assoc normal form puts an interior pair adjacent, so `simp only [Matrix.mul_assoc]` alone never lets the cancellation `rw` fire. Instead state the regrouped form (pair parenthesized) in a `show` and prove that step by `simp only [Matrix.mul_assoc]` (both sides flatten to the same normal form); then `rw [hV, Matrix.mul_one]` cancels. This is the workhorse for orthogonal-invariance / change-of-variables algebra (`SVDReduction.lean`).

**Frobenius orthogonal invariance via trace.** To prove `∑∑ (U M Vᵀ)ᵢⱼ² = ∑∑ Mᵢⱼ²`: bridge `∑∑ Nᵢⱼ² = (Nᵀ*N).trace` (prove once: `simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]; rw [Finset.sum_comm]; …pow_two`), then `rw [← bridge, ← bridge, Matrix.trace_mul_comm, <NNᵀ identity>, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_mul_comm]`. `trace_mul_comm` flips `NᵀN`↦`NNᵀ`; prove `(UMVᵀ)(UMVᵀ)ᵀ = U(MMᵀ)Uᵀ` (cancels `Vᵀ*V`), then `trace_mul_cycle` (`A*B*C↦C*A*B`) brings `Uᵀ*U` adjacent for `hU`.

**Real spectral theorem → plain `V·diagonal d·Vᵀ` (the SVD-existence adapter).** Mathlib's `Matrix.IsHermitian.spectral_theorem` lands in `conjStarAlgAut`/`unitaryGroup`/`RCLike.ofReal` form, NOT `*`/`ᵀ`. Unfold over ℝ with `conv_lhs => rw [hA.spectral_theorem]; rw [Unitary.conjStarAlgAut_apply, hof, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]` where `hof : (RCLike.ofReal ∘ hA.eigenvalues : Fin N → ℝ) = hA.eigenvalues := by funext i; simp`. Orthogonality `Vᵀ*V=1` for `V := (↑hA.eigenvectorUnitary : Matrix _ _ ℝ)`: `Unitary.coe_star_mul_self` then the same `star_eq_conjTranspose`+`conjTranspose_eq_transpose_of_trivial` bridge (`star`↦`ᵀ` over ℝ). PSD→PosDef of the Gram `Sgᵀ*Sg`: `(posSemidef_conjTranspose_mul_self Sg)` (rewrite `ᴴ`↦`ᵀ`), then `PosSemidef.posDef_iff_det_ne_zero` + `det_mul, det_transpose` + `IsUnit.ne_zero`; eigenvalues `>0` from `PosDef.eigenvalues_pos`. Then `U := Sg*V*diagonal (fun i => (√(d i))⁻¹)` (POINTWISE-inverse diagonal — avoids `Ring.inverse`/matrix inverse entirely); `UᵀU=1` and `Sg=U·diagonal σ·Vᵀ` collapse by the regroup-and-cancel `rw [show <flat> = <pair-parenthesized> from by simp only [Matrix.mul_assoc], hVtV/hVVt/hgram]` style, with `diagonal_mul_diagonal` + scalar `inv_mul_cancel₀`/`mul_self_sqrt`. Full square full-rank SVD in `SVDExistence.lean`.

**Build an orthogonal matrix by completing an orthonormal family of columns (rank-deficient SVD).** To get `U` orthogonal with prescribed columns on a subset `s ⊆ Fin N`: use `Orthonormal.exists_orthonormalBasis_extension_of_card_eq (card_ι) (hv : Orthonormal 𝕜 (s.restrict v))` — it returns `b : OrthonormalBasis (Fin N) 𝕜 E` with `∀ i ∈ s, b i = v i`, handling the `Fin N ↔ s ↔ complement` reindexing internally (NO manual bookkeeping). `card_ι : finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N)` is `by rw [finrank_euclideanSpace_fin, Fintype.card_fin]`. Then `U := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis.toMatrix ⇑b` is orthogonal for free via `(basisFun).toMatrix_orthonormalBasis_mem_unitary b` (+ `mem_unitaryGroup_iff'` + `star`↦`ᵀ`), and `U i j = (b j) i` by `rfl`. Build the Euclidean candidate vectors with `(WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => …)` — a bare `fun i => … : EuclideanSpace ℝ (Fin N)` does NOT ascribe (the elaborator won't unfold `WithLp`); coordinate readout `((…).symm f) i = f i` is `rfl`, and `⟪x, y⟫_ℝ = ∑ i, x i * y i` via `simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]`. Reduce the whole orthonormal-completion problem to a clean `Aᵀ A = diagonal (σ²)` Gram hypothesis (`column_completion` in `SVDExistence.lean`).

**`conv_lhs => rw [h]` to dodge a dependent-motive failure.** When the rewrite target reappears inside a *dependent* term on the other side (e.g. `rw [hgram : Sgᵀ Sg = …]` with the goal `Vᵀ (Sgᵀ Sg) V = diagonal hH.eigenvalues`, where `hH : (Sgᵀ Sg).IsHermitian` so `hH.eigenvalues` secretly depends on `Sgᵀ Sg`), plain `rw` fails with "motive is not type correct". `conv_lhs => rw [hgram]` rewrites only the LHS, never touching the dependent RHS occurrence. (Alternative: `set d := hH.eigenvalues` first to make the RHS opaque.)

**Derivative through a CONSTANT matrix factor — go entrywise, bridge with `funext`.** For `HasDerivAt (fun s => f s * C) (f' * C) t` (C constant): `refine hasDerivAt_pi.2 (fun k => hasDerivAt_pi.2 (fun l => ?_))`, project the matrix hyp with `hasDerivAt_pi.1 (hasDerivAt_pi.1 hf k) m`, sum `HasDerivAt.sum (fun m _ => (proj m).mul_const (C m l))`. The sum-of-functions ↔ function-of-sum bridge via `simpa only [Finset.sum_apply, Matrix.mul_apply] using` can FAIL the defeq close for `Finset.sum` over `Fin`; instead prove the function identity explicitly: `have hfun : (fun s => (f s*C) k l) = ∑ m, (fun s => f s k m * C m l) := by funext s; simp only [Matrix.mul_apply, Finset.sum_apply]`, then `rw [hfun, hval]; exact hsum`.

**Dot notation `h.myLemma` fails for a *self-defined* `HasDerivAt.myLemma`** — Lean unfolds `HasDerivAt` to `HasFDerivAtFilter` for the projection lookup and reports `HasFDerivAtFilter.myLemma` missing. Call it qualified: `HasDerivAt.myLemma h args`. (Mathlib's own `HasDerivAt.mul_const` etc. dot-resolve fine; only your new ones in a non-root namespace need qualification.)

**Read a column/row derivative off a matrix `HasDerivAt` with nested `hasDerivAt_pi`.** `hasDerivAt_pi.2 (fun i => hasDerivAt_pi.1 (hasDerivAt_pi.1 h k) i)` gives `HasDerivAt (fun s => <row/col k of M s>) (<row/col k of M'>) t` — the result is a genuine `Pi` vector (no `Matrix`-instance friction). Then retarget the value vector by `funext i` + `Matrix.smul_apply`/`Pi.smul_apply`/`Pi.sub_apply`/`Finset.sum_apply`/`smul_eq_mul` and a per-entry identity.

**Split a full sum into a distinguished term + the rest with `← Finset.add_sum_erase _ _ (Finset.mem_univ α)`, then `ring`.** Turns `∑ γ, f γ` into `f α + ∑ γ ∈ univ.erase α, f γ`; combined with the surrounding algebra (`ring`, treating the erase-sum and dot products as atoms) it produces the paper's `(… ) − ∑_{γ≠α} …` competition form (`ModeDynamics.lean`).

**`simp only [theDef]` may close a per-term goal by rfl when both sides line up after unfolding** — add a trailing `; ring` ONLY when commutativity is genuinely needed, else it errors "no goals". (Same proof skeleton: the a-side `flow_a_entry` needed `ring` (scalar on the opposite factor); the symmetric b-side did not.)

**Reduce a vector ODE to a scalar one along a fixed direction by dotting the `HasDerivAt` with that direction.** For a flow `HasDerivAt (fun s => v s) D t` on `Fin n → ℝ`, `HasDerivAt.dotProduct_const h r : HasDerivAt (fun s => v s ⬝ᵥ r) (D ⬝ᵥ r) t` (build it like `HasDerivAt.matrix_mul_const`: `hasDerivAt_pi.1 h i |>.mul_const (r i)`, `HasDerivAt.sum`, `funext` bridge with `simp only [dotProduct, Finset.sum_apply]`). Then `rw` the function to the scalar projection (`fun s => v s ⬝ᵥ rᵅ = ca` via the manifold hypothesis) and the value to its closed form. This is the "project onto rᵅ" step that turns the paper's vector mode dynamics into scalar `ab_dyn` (`InvariantManifold.lean`).

**For `ContDiff`/`infer_instance`/ODE lemmas on a *folded* `Matrix` type, you MUST `open scoped Matrix.Norms.Elementwise`** — plain `open Matrix` does NOT register a `NormedAddCommGroup (Matrix m n ℝ)` instance. Matrix-valued `HasDerivAt` typechecks without it (the elaborator unfolds `Matrix` to the `Pi` type and uses `Pi.normedAddCommGroup` via `hasDerivAt_pi`), but `ContDiff ℝ n f`, `infer_instance`, `ProperSpace`, and the `ODE_solution_unique_*` lemmas need the instance on the *folded* `Matrix`/`Matrix × Matrix` type, which only `open scoped Matrix.Norms.Elementwise` provides. Its instance is `fast_instance% Pi.normedAddCommGroup` — **defeq** to the one matrix `HasDerivAt` already uses, so there is no diamond: committed lemmas like `a_dyn`/`wbo_dyn` still apply unchanged. The concrete `Matrix (Fin a)(Fin b) ℝ × …` is then automatically `FiniteDimensional`/`ProperSpace`. (`lean_run_code` does not reproduce the scoped-instance activation faithfully — validate norm-instance questions in a real project file via `lean_diagnostic_messages`, not `lean_run_code`.)

**Prove `ContDiff` of a matrix-valued polynomial field entrywise.** `fun_prop` chokes on matrix `*`/`ᵀ` at the matrix level, but proves a single scalar entry directly (it knows matrix entry projection `fun M => M i j` is `ContDiff`). So: `apply ContDiff.prodMk` (split a product codomain), then on each matrix goal `apply contDiff_pi.2; intro i; apply contDiff_pi.2; intro j; simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.transpose_apply, smul_eq_mul]; fun_prop`. The `simp` turns the entry into sums/products of coordinate projections that `fun_prop` finishes. Lipschitz-on-a-ball then follows: `ContDiffOn.exists_lipschitzOnWith (hF.contDiffOn) (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)`.

**`ODE_solution_unique_of_mem_Ioo` is the cleanest ODE-uniqueness entry point** (`Analysis/ODE/ExistUnique.lean`): open interval `Ioo a b`, plain `HasDerivAt` (not within-at), continuity derived internally. Hypotheses bundle as `hf : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t ∧ f t ∈ s t`. For an autonomous field on all of ℝ: given `t`, pick `T = |t|+1`, set `a=-T, b=T, t₀=0`, `s _ := Metric.closedBall 0 R` with `R` bounding both trajectories on the compact interval (`IsCompact.exists_bound_of_continuousOn`), and `K` from the Lipschitz-on-ball lemma above. Package an abstract `eq_of_autonomous_ode {E}[…][ProperSpace E] (hF : ContDiff) (hf hg : ∀ t, HasDerivAt _ (F (_ t)) t) (h0) : ∀ t, f t = g t` once, then instantiate.

**Couple two matrix flows into one product-space ODE with `HasDerivAt.prodMk`, and let the field `def` close the gap by defeq.** `(hWba s).prodMk (hWbb s) : HasDerivAt (fun s => (Wba s, Wbb s)) (deriv₁, deriv₂) s`; feed it where `eq_of_autonomous_ode` expects `HasDerivAt f (flowField S τ (f s)) s` — `flowField` unfolds (`p.1 := Wba s`, `p.2 := Wbb s`) to exactly `(deriv₁, deriv₂)`, so the term typechecks without a rewrite. A matrix-valued field `def` that uses `1/τ` (real division) must be marked `noncomputable`. Split the final trajectory-equality `(Wba t, Wbb t) = (aLift…, bLift…)` into components with `simp only [Prod.mk.injEq] at heq` (the bare `.1`/`.2` projections do NOT reduce under `rw`).

**Collapse an orthonormal-frame dot product with `smul_dotProduct` + `dotProduct_smul` + the orthonormality hypothesis.** `(c • r α) ⬝ᵥ (d • r β) = c • (d • (r α ⬝ᵥ r β))`; rewrite `r α ⬝ᵥ r β` by `horth α β : … = if α = β then 1 else 0`, then `if_pos rfl`/`if_neg h` and `smul_eq_mul`/`smul_zero`. Distinct modes give `0` (competition vanishes); the diagonal gives `c * d` (after `mul_one`). `ring` mops up the leftover `c • (d • 1)` ordering.

**An ordered product of `N` *non-commuting* matrices is a `List.prod`, never a `Finset.prod`** (no `CommMonoid`). Use `prodDesc W := (List.ofFn W).reverse.prod` (descending `W_{m-1}⋯W₀`, the convention that telescopes with the paper's `Wₗ = R₍ₗ₊₁₎ W̄ₗ Rₗᵀ` change of variables). Peel the top factor with `prodDesc_succ` via `simp only [List.ofFn_succ', List.concat_eq_append, List.reverse_concat', List.prod_cons]` (`ofFn_succ'` emits a `.concat`, so `concat_eq_append` then `reverse_concat'`). Induct on `m` for telescoping: `induction m` AUTO-generalizes `R, Wb` (their types `Fin (m+1) → …` depend on `m`) — a bare `generalizing R Wb` is rejected as redundant; the IH lands fully `∀`-quantified. Reindex the IH with `R ∘ castSucc`, bridge `i.castSucc.succ ↔ i.succ.castSucc` by `Fin.castSucc_succ`, caps by `Fin.succ_last`/`Fin.castSucc_zero'`, then the regroup-and-cancel `simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Cᵀ C _, hCC (Cᵀ*C=1), Matrix.one_mul]`.

**Split an ordered product at one factor with `List.prod_set`.** `prodDesc (Function.update W l V) = aboveProd · V · belowProd` (the crux of depth-`N` Phase A — makes the loss affine in one layer's perturbation) follows from: `List.ofFn (Function.update W l V) = (List.ofFn W).set ↑l V` (prove by `List.ext_getElem`; entries via `getElem_ofFn`/`getElem_set`/`Function.update_apply`/`Fin.ext_iff`, the two `if`-conditions differ by `eq_comm` so `by_cases hil; · simp [hil]; · simp [hil, Ne.symm hil]`); `reverse_set : (L.set i a).reverse = L.reverse.set (L.length-1-i) a` (also `ext_getElem`, but `rw [List.length_set]` fails a dependent motive inside the `getElem` proof — use `simp only [List.getElem_reverse, List.getElem_set, List.length_set]` instead, then `by_cases` + `omega` on the reflected index); then `List.prod_set` (guarded `if n < length`, discharge with `omega` and `l.isLt`).

**One bilinear entry-derivative subsumes every layer's loss partial.** `∂/∂X ½‖S − A X B‖² = −Aᵀ(S − A X B)Bᵀ` (`hasDerivAt_loss_layer`): with `A = aboveProd`, `B = belowProd` it is *every* layer's partial of the deep loss (and `A=Wᵇ,B=I` / `A=I,B=Wᵃ` recover the two 3-layer `MatrixFlow` partials). The sandwich selector `(A · single k j 1 · B) p q = A p k · B j q` (`single_sandwich_apply`, two `mul_apply` + `sum_eq_single`) reduces it to the Layer-1 squared-affine technique; the Frobenius assembly `(Aᵀ M Bᵀ)ₖⱼ = ∑ₚ∑_q Aₚₖ Mₚ_q B_jq` needs a `Finset.sum_comm` (expand the inner `mul_apply` with `Finset.sum_mul`, then swap).

**Bridge a `deriv (fun x => …)` whose function is β-defeq but not syntactically equal with a `have hd : deriv <clean form> = … := (lemma).deriv`.** The gradient-flow structure stores `deriv (fun x => Edeep S (update (fun i => W i t) l (W l t + x•single))) 0`, but `hasDerivAt_Edeep_layer S (fun i => W i t) …` produces the same with `(fun i => W i t) l` in place of `W l t`. State `hd` in the *structure's* form and close it by `exact (lemma).deriv` — defeq accepts the β-difference — then `rw [hd] at hflow` matches syntactically. (Same `hasDerivAt_pi.2`-bundle + `Matrix.smul_apply` + `show (1/τ)*M k l = -(-(M k l))/τ by ring` closer as the 3-layer `matrixFlow_of_gradFlow`.)

**Telescope a *sub-range* (prefix/suffix) ordered product by its `succ`-recursion, not by reindexing.** `prodDesc_telescope` handles the full product, but `aboveProd`/`belowProd` (= `take`/`drop` of the reversed list) have no clean `ofFn`-reindexing (the `List.drop_reverse`/`take_ofFn` lemmas don't exist). Instead prove the one-step recursions — `belowProd W i.succ = W i.castSucc * belowProd W i.castSucc` (via `List.cons_getElem_drop_succ` + `List.getElem_reverse`/`getElem_ofFn` + `omega` on the reflected index) and `aboveProd W i.castSucc = aboveProd W i.succ * W i.succ` (via `List.prod_take_succ`) — then telescope by `induction l using Fin.induction` (below, bottom-up) / `Fin.reverseInduction` (above, top-down). Both need `obtain ⟨k, rfl⟩ : ∃ k, m = k+1 := ⟨m-1, by have := l.isLt; omega⟩` first (`Fin.induction` wants `Fin (k+1)`). The per-step `Finset.Iio`/`Ioi` shift is `Iio i.succ = insert i.castSucc (Iio i.castSucc)` (prove by `ext; simp [Fin.lt_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]; omega`).

**Don't `rw [Finset.prod_insert]` under a `fun α => …` binder — lift it into a `diagonal`-level `have`.** To rewrite `diagonal (fun α => ∏ j ∈ insert i s, f j α)`, prove `hdiag : diagonal (∏ over insert) = diagonal (f i) * diagonal (∏ over s)` by `rw [Matrix.diagonal_mul_diagonal]; congr 1; funext α; rw [Iio_succ_eq, Finset.prod_insert (by simp)]` (and `mul_comm` for the suffix order), then `rw [hdiag]`. The orthogonal cancellation that follows is the standard `simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Cᵀ C, hC, Matrix.one_mul]`.

**Collapse a frame-conjugated matrix velocity to a diagonal by cancelling all four orthogonal pairs at once.** `flowval_conj`: after substituting the factored `above/below/prodDesc`, `simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]`, fold `S − ∏` with `← Matrix.diagonal_sub` (it is `diag−diag = diag(−)`, so use `←`; keep the arg as `fun i => σ i − …`, NOT `Pi.sub`, or the pattern won't match) + `mul_sub` + `sub_mul`, then `simp only [Matrix.mul_assoc]` and cancel left-to-right: `rw [← Matrix.mul_assoc Xᵀ X, hR X, Matrix.one_mul]` per interior pair — but the LAST (innermost) pair is already adjacent (`diag * (Xᵀ * X)`), so close it with `hR X, Matrix.mul_one` (no `← mul_assoc`). Two `diagonal_mul_diagonal` merge the three diagonals; `congr 1; funext; ring`.

**Extract a scalar entry's derivative from a matrix `HasDerivAt` through constant conjugating factors.** `hasDerivAt_conj_apply h A B p q : HasDerivAt (fun s => (A · M s · B) p q) ((A·M'·B) p q) t` from `h : HasDerivAt M M' t`: expand the entry as `∑ y ∑ x A p x · (M s) x y · B y q` (`hexp`, `mul_apply` + `sum_mul`), then `HasDerivAt.sum (… HasDerivAt.sum (… (proj.const_mul (A p x)).mul_const (B y q)))` where `proj = hasDerivAt_pi.1 (hasDerivAt_pi.1 h x) y`. `HasDerivAt.sum` yields a *sum-of-functions* (`∑ y ∑ x fun s => …`), defeq-blocked from the goal's *function-of-sum*; bridge with an explicit `have hfeq : (fun s => ∑ y ∑ x body[s]) = (∑ y ∑ x fun s => body) := by funext s; simp only [Finset.sum_apply]` then `rw [hfeq]; exact …`.

## Mathlib API Reference (build out as we go)

Derivative combinators (`Mathlib/Analysis/Calculus/Deriv/*`). The *function* comes out as a `Pi`-op (see Proof tactics); these *derivative* forms are exact:
- `HasDerivAt.mul (hc) (hd) : HasDerivAt (c * d) (c' * d x + c x * d') x`
- `HasDerivAt.div (hc) (hd) (hx : d x ≠ 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) x`
- `HasDerivAt.sub (hf) (hg) : HasDerivAt (f - g) (f' - g') x`  — also `.add`, `.add_const`, `.sub_const`
- `HasDerivAt.const_mul (c) (hf) : HasDerivAt (fun x => c * f x) (c * f') x`  — also `.div_const c`
- `HasDerivAt.const_sub (c) (hf) : HasDerivAt (fun x => c − f x) (−f') x`  — used for `fun x => s − x*b₀`; note `mul_const`/`const_mul` leave a literal `1*b`/`a*1` in `f'`, absorb it with the value-`rw … by ring`
- `HasDerivAt.add_const (hf) (c) : HasDerivAt (fun x => f x + c) f' x`  — drops a weight-independent loss constant
- `HasDerivAt.exp (hf) : HasDerivAt (fun x => Real.exp (f x)) (Real.exp (f x) * f') x`
- `HasDerivAt.pow n (hf) : HasDerivAt (fun x => f x ^ n) (↑n * f x ^ (n-1) * f') x`  (casts — see tactics)
- `hasDerivAt_id (x) : HasDerivAt id 1 x`;  `HasDerivAt.deriv : … → deriv f x = f'`;  `.differentiableAt`

Constancy (`Mathlib/Analysis/Calculus/MeanValue.lean`):
- `is_const_of_deriv_eq_zero (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x = 0) (x y) : f x = f y` (note the `_root_.` prefix; `is_const_of_fderiv_eq_zero` is the normed-space version)

Finset sums (`Mathlib/Algebra/BigOperators/*`), for the network square loss:
- `Finset.mul_sum : b * ∑ i, f i = ∑ i, b * f i`  (pulls a scalar into a sum)
- `Finset.sum_sub_distrib : ∑ (f − g) = ∑ f − ∑ g`;  `Finset.sum_add_distrib : ∑ (f + g) = ∑ f + ∑ g`  (use `←` to merge sums)
- `Finset.sum_congr rfl (fun i _ => by ring)`  (close `∑ f = ∑ g` term-by-term)
- `Finset.sum_eq_single a (h_ne : ∀ b ∈ s, b ≠ a → f b = 0) (h_mem : a ∉ s → f a = 0) : ∑ x ∈ s, f x = f a`  (collapse a sum to one surviving term — picks out the `single`-selected index)
- `Finset.sum_apply : (∑ k ∈ s, g k) i = ∑ k ∈ s, g k i`  (sum-of-functions ↦ function-of-sum; the bridge after `HasDerivAt.sum`)
- `Finset.prod_erase_mul s f (h : a ∈ s) : (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x`  (and `Finset.mul_prod_erase` for the other order) — the workhorse of the depth-`N` conservation `deepFlow_conserved`: `(∏_{k≠i} aₖ)·aᵢ = ∏ₖ aₖ` makes `aᵢ aᵢ'` independent of `i`, so `d/dt(aᵢ²−aⱼ²)=0` closes by `ring` after `rw [hPi, hPj, sub_self]`
- `Finset.prod_const : ∏ _x ∈ s, c = c ^ s.card`;  `Finset.card_erase_of_mem (h : a ∈ s) : (s.erase a).card = s.card − 1`;  `Finset.card_univ`/`Fintype.card_fin : (univ : Finset (Fin m)).card = m`  (collapse `∏ᵢ c = cᵐ`, `∏_{i≠l} c = cᵐ⁻¹` on the symmetric submanifold — `isDeepSymFlow_of_symmetric`)

Matrix (`Mathlib/Data/Matrix/*`, `Mathlib/Analysis/Matrix/*`), for the three-layer flow (`open Matrix` for the scoped normed instances + `ᵀ` notation):
- `Matrix.single i j a` — single-entry matrix (formerly `stdBasisMatrix`); `Matrix.single_apply : single i j a i' j' = if i = i' ∧ j = j' then a else 0`
- selectors (proved locally in `MatrixFlow.lean`): `(B * single k l 1) i j = if j = l then B i k else 0` (column pick); `(single k l 1 * A) i j = if i = k then A l j else 0` (row pick) — both by `mul_apply` + `single_apply` + `Finset.sum_eq_single`
- `Matrix.mul_add`, `Matrix.add_mul`, `Matrix.mul_smul : M * (a • N) = a • (M * N)`, `Matrix.smul_mul : (a • M) * N = a • (M * N)`
- entry lemmas: `Matrix.add_apply`, `Matrix.sub_apply`, `Matrix.smul_apply` (`(a • M) i j = a • M i j`), `Matrix.transpose_apply : Mᵀ i j = M j i`, `Matrix.mul_apply : (M * N) i j = ∑ k, M i k * N k j`, `Matrix.diagonal_apply : diagonal d i j = if i = j then d i else 0`
- `Matrix.transpose_mul : (M*N)ᵀ = Nᵀ*Mᵀ`, `Matrix.transpose_transpose : Mᵀᵀ = M`, `Matrix.transpose_one`, `Matrix.mul_assoc`, `Matrix.one_mul`, `Matrix.mul_one`, `Matrix.mul_sub`/`Matrix.sub_mul`
- `Matrix.smul_mul : (a•M)*N = a•(M*N)`, `Matrix.mul_smul : M*(a•N) = a•(M*N)` (NOT `smul_mul_assoc`/`mul_smul_comm` for rectangular `*`)
- `Matrix.mul_eq_one_comm_of_equiv (e : m ≃ n) : A*B = 1 ↔ B*A = 1` — square orthogonal reverse `U*Uᵀ=1` from `Uᵀ*U=1` via `(… (Equiv.refl _)).mp`
- trace (`Mathlib/LinearAlgebra/Matrix/Trace.lean`): `Matrix.trace`, `Matrix.diag_apply : diag A i = A i i`, `Matrix.trace_mul_comm : trace (A*B) = trace (B*A)`, `Matrix.trace_mul_cycle : trace (A*B*C) = trace (C*A*B)`
- `Matrix.dotProduct` (`⬝ᵥ`, needs `open Matrix`) `= ∑ i, u i * v i`; unfold with `simp only [dotProduct]`

Real / order lemmas used:
- `Real.exp_pos`, `Real.exp_zero`
- `one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a`
- `div_eq_iff (hc : c ≠ 0) : a / c = b ↔ a = b * c`
- real-power bridge (`Mathlib/Analysis/SpecialFunctions/Pow/*`), for the depth-`N`
  law's `(aᵐ)^{2−2/m} = a^{2(m−1)}` (`rpow_bridge`): `Real.rpow_natCast x n : x^(n:ℝ) = x^n`
  (use `←` to lift a Nat power into rpow), `Real.rpow_mul (hx : 0 ≤ x) y z : x^(y*z) = (x^y)^z`
  (use `←` to fold `(x^y)^z`), then close the exponent identity `m·(2−2/m) = ↑(2(m−1))` with
  `push_cast [Nat.cast_sub hm]; field_simp` (`Nat.cast_sub (h : n ≤ m) : (↑(m−n) : ℝ) = ↑m − ↑n`
  is mandatory — `push_cast` won't touch Nat subtraction without it)

Forward pointers (not yet used):
- Per-coordinate gradient flow chosen over abstract `gradient` (Layer 1, done): raw `ℝ×ℝ` carries the sup-norm, *not* an inner product, so `gradient`/`HasGradientAt` would need `EuclideanSpace ℝ (Fin 2)` or `WithLp 2 (ℝ×ℝ)`. If a true `∇` form is ever wanted: `Mathlib/Analysis/Calculus/Gradient/Basic.lean`, bridged via `hasGradientAt_iff_hasFDerivAt`.
- ODE uniqueness (time analysis, later): `ODE_solution_unique_of_mem_Icc` in `Mathlib/Analysis/ODE/ExistUnique.lean` (set-local Lipschitz; the bare `ODE_solution_unique` needs GLOBAL Lipschitz — won't fit a quadratic RHS like `2u(s-u)`).
- Limits (`t→∞`, later): `Real.tendsto_exp_atTop`, `tendsto_inv_atTop_zero`, `Filter.Tendsto.div`.
- Mathlib has NO SVD *factorization* (only `LinearMap.singularValues`, values-only). **Phase E is DONE for any square `Sg`** (`SVDExistence.lean`): `exists_isSVD` (general, via `column_completion`) + `exists_isSVD_of_isUnit` (explicit full-rank `U = Sg V Σ⁻¹`). The feared rank-deficient "reindexing sink" was avoided by `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (it packs `exists_equiv_extend_of_card_eq` internally — lands on `Fin N`, agreeing on the subset, no manual `Fin N ↔ support` bookkeeping).

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
