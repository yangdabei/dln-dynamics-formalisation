# Handoff: Phase D — Option 3 (forward-invariance of the orthogonal-mode manifold)

**Paste this whole file as the opening prompt of a fresh Claude Code session in this
repo** (`/Users/yangd/Documents/dln-dynamics-formalisation`). It is self-contained.
Read `CLAUDE.md` first (project conventions, MCP/LSP loop, proof-tactic lessons).

This session works **in parallel** with the main session, which is doing Phase D
**option 1** (`DlnDynamics/InvariantManifold.lean`). To avoid merge conflicts:

- Work only in a **new file `DlnDynamics/ManifoldInvariance.lean`**.
- Do **not** edit `InvariantManifold.lean`, `ModeDynamics.lean`, `SVDReduction.lean`,
  or `MatrixFlow.lean` (the main session and committed work own those).
- The only shared edit is one import line in the root `DlnDynamics.lean`; add
  `import DlnDynamics.ManifoldInvariance` at the end and expect a trivial conflict there.
- Run `lake build` once up front to warm Mathlib oleans; use the `lean-lsp-mcp` tools
  (`lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`) as the inner loop.
- House rules: **no `sorry`/`admit`/`native_decide`/`axiom` in committed code**
  (`scripts/no_sorry.sh` + CI enforce it). Skeleton-first: land correct *statements*
  (a local `sorry` is fine while iterating, but the file must be gap-free before commit).
- **Make the Lean proof structure mirror the human/paper proof** (named lemmas per
  human step) — this is an explicit project requirement.

## What you are proving

Saxe 2014 (arXiv:1312.6120), §"The time course of learning" (source
`arXiv-1312.6120v3/iclr2014_revised.tex`, lines ~162–189), the sentence:

> "It is straightforward to verify that starting from these initial conditions, aᵅ and
> bᵅ will remain parallel to rᵅ for all future time."

That is **forward-invariance in time** of the orthogonal-mode manifold for the decoupled
matrix gradient flow `wbo_dyn`. It is asserted without proof ("straightforward to
verify") — the classic CLAUDE.md "easy to see" red flag — and is the genuine bottleneck.

The flow (already formalized, in `DlnDynamics/SVDReduction.lean` /
`DlnDynamics/ModeDynamics.lean`), in the square case `N₃ = N₁ = N`, `S = diagonal σ`,
`N₂` = hidden width:

```
HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t
HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t
```
with `Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ`, `Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ`,
`S : Matrix (Fin N) (Fin N) ℝ`, `τ : ℝ`.

## The integration contract (what option 1 needs from you)

Option 1's reduction theorem (already proven, gap-free, in `InvariantManifold.lean`) is:

```lean
theorem isABFlow_of_modeFlow {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    {ca cb : Fin N → ℝ → ℝ}
    (hWba : ∀ t, HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t)
    (hWbb : ∀ t, HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t)
    (hmemA : ∀ t γ, aMode (Wba t) γ = ca γ t • r γ)
    (hmemB : ∀ t γ, bMode (Wbb t) γ = cb γ t • r γ)
    (α : Fin N) :
    IsABFlow (σ α) τ (ca α) (cb α)
```

It **takes manifold-membership-for-all-t (`hmemA`/`hmemB`) as a hypothesis**. Your job is
to **discharge those hypotheses** from manifold membership at `t = 0` only. I.e. prove a
theorem of roughly this shape (adjust as the proof dictates):

```lean
theorem manifold_forward_invariant {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} (hτ : τ ≠ 0)
    {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hWba : ∀ t, HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t)
    (hWbb : ∀ t, HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t)
    -- initial condition on the manifold:
    {ca0 cb0 : Fin N → ℝ}
    (hinitA : ∀ γ, aMode (Wba 0) γ = ca0 γ • r γ)
    (hinitB : ∀ γ, bMode (Wbb 0) γ = cb0 γ • r γ) :
    ∃ ca cb : Fin N → ℝ → ℝ,
      (∀ t γ, aMode (Wba t) γ = ca γ t • r γ) ∧ (∀ t γ, bMode (Wbb t) γ = cb γ t • r γ)
```

Composing your `manifold_forward_invariant` with `isABFlow_of_modeFlow` then yields the
full Saxe claim with **no manifold hypothesis** — only a manifold *initial condition*.
Write that ~5-line corollary too (call it `isABFlow_of_modeFlow_of_init` or similar).
`aMode`/`bMode` and `⬝ᵥ` (dotProduct) come from `DlnDynamics.ModeDynamics` (`open Matrix`).

## Proof strategy (forward-invariance via ODE uniqueness)

1. **Construct the lifted manifold solution.** From the scalar two-mode ODE
   `IsABFlow (σ α) τ a b` (`DlnDynamics.Basic`), obtain scalar solutions
   `ca γ, cb γ : ℝ → ℝ` for each mode with the given initial values `ca0 γ, cb0 γ`.
   (`DlnDynamics.ClosedForm`/`Basic` give the closed form `uf` of the *product* `u = ab`;
   you may need to reconstruct `a(t), b(t)` themselves, or set up the scalar IVP directly.
   Existence of the scalar solution may be the fiddly sub-part — see Picard–Lindelöf below,
   or build `a,b` from `uf` and the conserved quantity `a² − b²`, `ab_conserved`.)
   Define `W̄a(t)`, `W̄b(t)` by `column α = ca α t • rᵅ`, `row α = cb α t • rᵅ`. Prove this
   lift satisfies `wbo_dyn` (reuse the algebra: competition vanishes, `IsABFlow` gives the
   per-mode derivative — this mirrors `isABFlow_of_modeFlow` run backwards).
2. **Uniqueness.** Package the state as the product
   `Matrix (Fin N₂) (Fin N) ℝ × Matrix (Fin N) (Fin N₂) ℝ` (use `HasDerivAt.prodMk` to
   combine the two matrix flows into one). The vector field
   `F (Wba, Wbb) = ((1/τ)•(Wbbᵀ(S−WbbWba)), (1/τ)•((S−WbbWba)Waᵀ))` is a polynomial,
   hence `C^∞` and locally Lipschitz. Apply the set-local uniqueness lemma to conclude the
   given trajectory `(Wba, Wbb)` equals the constructed lifted solution on any interval.
3. **Conclude.** Equality of trajectories ⇒ `Wba t`'s columns are `ca α t • rᵅ` for all t
   ⇒ `hmemA`/`hmemB`. Done.

## Scouted Mathlib API (verify exact names with `lean_hover_info` before relying on them)

ODE uniqueness — `Mathlib/Analysis/ODE/ExistUnique.lean`:

- **`ODE_solution_unique_of_mem_Icc_right`** *(the one to use — set-local Lipschitz)*:
  ```
  (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
  (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
  (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
  (hg …) (hg' …) (hgs …) (ha : f a = g a) : EqOn f g (Icc a b)
  ```
- `ODE_solution_unique_of_mem_Icc` — same but initial point `t₀ ∈ Ioo a b`, full
  `HasDerivAt` (not just right-sided). Use if your IC sits at an interior time.
- `ODE_solution_unique` — needs **global** `LipschitzWith`; **insufficient** here (the
  field is quadratic ⇒ only locally Lipschitz). Don't use it.

Lipschitz-from-smoothness — `Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`:

- `ContDiffOn.exists_lipschitzOnWith (hf : ContDiffOn ℝ n f s) (hn : n ≠ 0)
  (hs : Convex ℝ s) (hs' : IsCompact s) : ∃ K, LipschitzOnWith K f s` — cleanest: `F`
  is `C^∞` on a compact convex closed ball ⇒ global `LipschitzOnWith` on that ball.
- `ContDiffAt.exists_lipschitzOnWith`, `ContDiff.locallyLipschitz`,
  `ContDiffOn.locallyLipschitzOn` — alternatives.
- Smoothness of `F`: it's polynomial in the entries; try `fun_prop` or compose
  `ContDiff` lemmas (`contDiff_const`, `.mul`, `.smul`, matrix mul as a bilinear map).

State/derivative plumbing:

- `HasDerivAt.prodMk (hf₁ : HasDerivAt f₁ f₁' x) (hf₂ : HasDerivAt f₂ f₂' x) :
  HasDerivAt (fun x => (f₁ x, f₂ x)) (f₁', f₂') x` — `Mathlib/Analysis/Calculus/Deriv/Prod.lean`.
- `Matrix` normed instances are scoped: keep `open Matrix` in scope. The product of two
  normed spaces is automatically a `NormedAddCommGroup`/`NormedSpace ℝ`.
- For `HasDerivWithinAt` from `HasDerivAt`: `HasDerivAt.hasDerivWithinAt`.
- Continuity on `Icc` from differentiability: `HasDerivAt.continuousOn` / build via
  `Continuous` of the trajectory.

Existence (if you construct the comparison solution via the abstract IVP rather than the
closed form) — `Mathlib/Analysis/ODE/PicardLindelof.lean`: `IsPicardLindelof`,
`exists_eq_forall_mem_Icc_hasDerivWithinAt`. Lower priority: prefer building the lifted
solution explicitly from the scalar `ca, cb`.

Worked example of applying the uniqueness lemma:
`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean` (`isMIntegralCurveAt_eventuallyEq_…`):
extract a local Lipschitz constant from `C¹`, then feed the two solutions + IC to the
uniqueness lemma.

Suggested imports for the new file:
```lean
import DlnDynamics.InvariantManifold
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
```

## Risk / fallbacks (HIGH risk — escalate after ~3 failed attempts on any step, per CLAUDE.md)

- **Likely sink:** packaging the two coupled matrix ODEs as a single product-space IVP and
  discharging the `LipschitzOnWith`/continuity/state-membership side conditions of the
  uniqueness lemma. Validate the Lipschitz bottleneck (`F` is `C^∞` ⇒ `LipschitzOnWith` on
  a closed ball) on a *toy* first.
- **Scalar-solution existence** (step 1) may itself need work; if reconstructing `a(t),b(t)`
  from `uf` is painful, set up the scalar IVP via Picard–Lindelöf, or take the scalar
  solutions as a hypothesis (`∀ α, IsABFlow (σ α) τ (ca α) (cb α)` with matching init) and
  prove invariance *relative to* that — still discharges option 1's hypotheses.
- If full forward-invariance stalls, a valuable partial result is **local-in-time**
  invariance on a fixed `Icc 0 T`, or the **uniqueness lemma instantiated** to this flow
  (reusable infrastructure) — commit those as honest milestones with the remaining gap
  documented (no `sorry` in committed code; keep WIP on a branch).

## Verification before commit
- `lake build` clean; `bash scripts/no_sorry.sh` green.
- `#print axioms <your_capstone>` / `lean_verify` = `[propext, Classical.choice, Quot.sound]`.
- Numerically sanity-check any constructed solution / Lipschitz constant first
  (`scripts/check_svd_reduction.py` is the template; pure stdlib).
