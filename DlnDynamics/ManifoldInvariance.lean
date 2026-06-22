import DlnDynamics.InvariantManifold
import DlnDynamics.ClosedForm
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Forward-invariance of the orthogonal-mode manifold (Phase D, option 3)

Layer-3 **Phase D, option 3** (Saxe §"The time course of learning", arXiv lines 162–189).
Saxe asserts, without proof — *"It is straightforward to verify that starting from these
initial conditions, `aᵅ` and `bᵅ` will remain parallel to `rᵅ` for all future time"* — that
the orthogonal-mode manifold is **forward-invariant in time** under the decoupled flow
`wbo_dyn`. Phase D option 1 (`InvariantManifold.lean`) reduced the on-manifold dynamics to the
scalar `ab_dyn` but *took manifold membership for all `t` as a hypothesis*. This module
discharges that hypothesis via **ODE uniqueness**, so the conclusion needs only a manifold
*initial condition*.

The argument (mirroring the standard "invariant manifold via uniqueness" proof):

1. **Lift** scalar two-mode solutions `ca γ, cb γ` (`IsABFlow`) to barred matrices `aLift`,
   `bLift` whose column / row `α` is `ca α t • rᵅ`, `cb α t • rᵅ` (`aMode_aLift`/`bMode_bLift`).
2. The lift **solves the decoupled flow** `wbo_dyn` (`aLift_solves`/`bLift_solves`) — this is
   `isABFlow_of_modeFlow` run backwards: competition vanishes, leaving the per-mode `ab_dyn`.
3. **Uniqueness** (`trajectory_eq_lift`): the given matrix trajectory and the lift both solve the
   same polynomial (hence locally Lipschitz) ODE on the product state space and agree at `t = 0`,
   so they agree for all `t` (`ODE_solution_unique_of_mem_Ioo`).
4. Reading membership off the equality gives forward-invariance (`manifold_forward_invariant`),
   and composing with `isABFlow_of_modeFlow` gives the init-only headline.

For the **balanced paper regime** `0 < u₀ < s` the scalar solutions are *constructed*
(`ca = cb = √∘uf`, `isABFlow_sqrt_uf`), making the headline hypothesis-free. General unbalanced
initial conditions need scalar existence (Picard–Lindelöf) and are deferred.
-/

namespace DlnDynamics

open Matrix Set
open scoped Matrix.Norms.Elementwise

variable {N N₂ : ℕ}

/-! ## Step 1 — the manifold lift -/

/-- Lift of scalar `a`-amplitudes to a barred matrix: column `α` is `ca α t • rᵅ`. -/
def aLift (r : Fin N → Fin N₂ → ℝ) (ca : Fin N → ℝ → ℝ) (t : ℝ) :
    Matrix (Fin N₂) (Fin N) ℝ := fun i α => ca α t * r α i

/-- Lift of scalar `b`-amplitudes to a barred matrix: row `α` is `cb α t • rᵅ`. -/
def bLift (r : Fin N → Fin N₂ → ℝ) (cb : Fin N → ℝ → ℝ) (t : ℝ) :
    Matrix (Fin N) (Fin N₂) ℝ := fun α i => cb α t * r α i

/-- The `α`-th column of `aLift` is `ca α t • rᵅ` — the lift lands on the manifold. -/
theorem aMode_aLift (r : Fin N → Fin N₂ → ℝ) (ca : Fin N → ℝ → ℝ) (t : ℝ) (γ : Fin N) :
    aMode (aLift r ca t) γ = ca γ t • r γ := by
  funext i; simp only [aMode, aLift, Pi.smul_apply, smul_eq_mul]

/-- The `α`-th row of `bLift` is `cb α t • rᵅ` — the lift lands on the manifold. -/
theorem bMode_bLift (r : Fin N → Fin N₂ → ℝ) (cb : Fin N → ℝ → ℝ) (t : ℝ) (γ : Fin N) :
    bMode (bLift r cb t) γ = cb γ t • r γ := by
  funext i; simp only [bMode, bLift, Pi.smul_apply, smul_eq_mul]

/-! ## Step 2 — the lift solves the decoupled flow `wbo_dyn` -/

/-- **The `a`-lift solves `wbo_dyn`** (Saxe Eq. `wbo_dyn`, `a`-component) — this is
`isABFlow_of_modeFlow` run backwards. Each column `α` of `aLift` evolves by the scalar
`ab_dyn` (`hsol`), the competition between distinct modes vanishes by orthonormality
(`competition_vanishes`), and reassembling the entries gives exactly the matrix flow value. -/
theorem aLift_solves {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {ca cb : Fin N → ℝ → ℝ}
    (hsol : ∀ α, IsABFlow (σ α) τ (ca α) (cb α)) (t : ℝ) :
    HasDerivAt (fun s => aLift r ca s)
      ((1 / τ) • ((bLift r cb t)ᵀ * (S - bLift r cb t * aLift r ca t))) t := by
  have hentry : HasDerivAt (fun s => aLift r ca s)
      (fun i α => cb α t * (σ α - ca α t * cb α t) / τ * r α i) t :=
    hasDerivAt_pi.2 (fun i => hasDerivAt_pi.2 (fun α => ((hsol α).ha t).mul_const (r α i)))
  have hval : (fun i α => cb α t * (σ α - ca α t * cb α t) / τ * r α i)
      = (1 / τ) • ((bLift r cb t)ᵀ * (S - bLift r cb t * aLift r ca t)) := by
    funext i α
    have hcomp : (∑ γ ∈ Finset.univ.erase α,
        (bMode (bLift r cb t) γ ⬝ᵥ aMode (aLift r ca t) α) * bMode (bLift r cb t) γ i) = 0 := by
      have h0 := competition_vanishes horth α
        (fun γ => bMode_bLift r cb t γ) (aMode_aLift r ca t α)
      have h1 := congrFun h0 i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1
    have hdot : bMode (bLift r cb t) α ⬝ᵥ aMode (aLift r ca t) α = ca α t * cb α t := by
      rw [bMode_bLift, aMode_aLift, smul_dotProduct, dotProduct_smul, horth α α, if_pos rfl,
        smul_eq_mul, smul_eq_mul, mul_one]; ring
    have hbi : bMode (bLift r cb t) α i = cb α t * r α i := by
      rw [bMode_bLift, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.smul_apply, flow_a_entry hdiag (aLift r ca t) (bLift r cb t) α i, smul_eq_mul,
      hcomp, hdot, hbi]
    ring
  rwa [hval] at hentry

/-- **The `b`-lift solves `wbo_dyn`** (Saxe Eq. `wbo_dyn`, `b`-component) — symmetric to
`aLift_solves`. -/
theorem bLift_solves {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {ca cb : Fin N → ℝ → ℝ}
    (hsol : ∀ α, IsABFlow (σ α) τ (ca α) (cb α)) (t : ℝ) :
    HasDerivAt (fun s => bLift r cb s)
      ((1 / τ) • ((S - bLift r cb t * aLift r ca t) * (aLift r ca t)ᵀ)) t := by
  have hentry : HasDerivAt (fun s => bLift r cb s)
      (fun α i => ca α t * (σ α - ca α t * cb α t) / τ * r α i) t :=
    hasDerivAt_pi.2 (fun α => hasDerivAt_pi.2 (fun i => ((hsol α).hb t).mul_const (r α i)))
  have hval : (fun α i => ca α t * (σ α - ca α t * cb α t) / τ * r α i)
      = (1 / τ) • ((S - bLift r cb t * aLift r ca t) * (aLift r ca t)ᵀ) := by
    funext α i
    have hcomp : (∑ γ ∈ Finset.univ.erase α,
        (aMode (aLift r ca t) γ ⬝ᵥ bMode (bLift r cb t) α) * aMode (aLift r ca t) γ i) = 0 := by
      have h0 := competition_vanishes horth α
        (fun γ => aMode_aLift r ca t γ) (bMode_bLift r cb t α)
      have h1 := congrFun h0 i
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h1
    have hdot : aMode (aLift r ca t) α ⬝ᵥ bMode (bLift r cb t) α = ca α t * cb α t := by
      rw [aMode_aLift, bMode_bLift, smul_dotProduct, dotProduct_smul, horth α α, if_pos rfl,
        smul_eq_mul, smul_eq_mul, mul_one]
    have hai : aMode (aLift r ca t) α i = ca α t * r α i := by
      rw [aMode_aLift, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.smul_apply, flow_b_entry hdiag (aLift r ca t) (bLift r cb t) α i, smul_eq_mul,
      hcomp, hdot, hai]
    ring
  rwa [hval] at hentry

/-! ## Step 3 — ODE uniqueness on the product state -/

/-- The (autonomous) vector field of the decoupled flow `wbo_dyn`, packaged on the product
state space `W̄ᵃ × W̄ᵇ`:
`F (A, B) = ((1/τ)·Bᵀ(S − BA), (1/τ)·(S − BA)Aᵀ)`. It is a polynomial, hence `C^∞`. -/
noncomputable def flowField (S : Matrix (Fin N) (Fin N) ℝ) (τ : ℝ) :
    Matrix (Fin N₂) (Fin N) ℝ × Matrix (Fin N) (Fin N₂) ℝ →
    Matrix (Fin N₂) (Fin N) ℝ × Matrix (Fin N) (Fin N₂) ℝ :=
  fun p => ((1 / τ) • (p.2ᵀ * (S - p.2 * p.1)), (1 / τ) • ((S - p.2 * p.1) * p.1ᵀ))

/-- The flow field is `C^∞` (it is a matrix polynomial). Proved entrywise: split the product
codomain (`ContDiff.prodMk`), reduce each matrix to its entries (`contDiff_pi`), expand the
entry to sums/products of coordinate projections (`simp`), and finish with `fun_prop`. -/
theorem flowField_contDiff (S : Matrix (Fin N) (Fin N) ℝ) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flowField (N₂ := N₂) S τ) := by
  unfold flowField
  apply ContDiff.prodMk <;>
  · apply contDiff_pi.2; intro i
    apply contDiff_pi.2; intro j
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.transpose_apply,
      smul_eq_mul]
    fun_prop

/-- **ODE uniqueness on a finite-dimensional space.** Two global solutions of the same
autonomous `C¹` ODE `ż = F z` that agree at `t = 0` agree for all `t`. Localizes to a symmetric
open interval `Ioo (-T) T ∋ 0, t`, bounds both trajectories in a closed ball there (continuity +
compactness), extracts a Lipschitz constant for `F` on that ball (`ContDiffOn.exists_lipschitzOnWith`),
and applies `ODE_solution_unique_of_mem_Ioo`. -/
theorem eq_of_autonomous_ode {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (F (f t)) t) (hg : ∀ t, HasDerivAt g (F (g t)) t)
    (h0 : f 0 = g 0) : ∀ t, f t = g t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_iff_continuousAt.2 (fun t => (hg t).continuousAt)
  intro t
  obtain ⟨T, hT0, htT⟩ : ∃ T : ℝ, 0 < T ∧ |t| < T :=
    ⟨|t| + 1, by positivity, by linarith [abs_nonneg t]⟩
  have htmem : t ∈ Ioo (-T) T := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h0mem : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hT0⟩
  obtain ⟨Cf, hCf⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hfc.continuousOn
  obtain ⟨Cg, hCg⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hgc.continuousOn
  set R := max Cf Cg with hRdef
  obtain ⟨K, hK⟩ := ContDiffOn.exists_lipschitzOnWith hF.contDiffOn (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  have hmem : ∀ s ∈ Ioo (-T) T,
      f s ∈ Metric.closedBall (0 : E) R ∧ g s ∈ Metric.closedBall (0 : E) R := by
    intro s hs
    have hsIcc : s ∈ Icc (-T) T := Ioo_subset_Icc_self hs
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]; exact (hCf s hsIcc).trans (le_max_left _ _)
    · rw [mem_closedBall_zero_iff]; exact (hCg s hsIcc).trans (le_max_right _ _)
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => F)
    (s := fun _ => Metric.closedBall (0 : E) R) (K := K) (fun s _ => hK) h0mem
    (fun s hs => ⟨hf s, (hmem s hs).1⟩) (fun s hs => ⟨hg s, (hmem s hs).2⟩) h0 htmem

/-- **The trajectory equals the lift** (the crux of forward-invariance). Given scalar solutions
`ca, cb` of `ab_dyn` and a matrix trajectory `(Wᵃ, Wᵇ)` of `wbo_dyn` that starts on the manifold
(`hinitA`/`hinitB`), the trajectory coincides with the lifted manifold solution for all `t`. Both
solve the same autonomous `C^∞` ODE `ż = flowField S τ z` (the trajectory by hypothesis, the lift
by `aLift_solves`/`bLift_solves`) and agree at `t = 0`, so `eq_of_autonomous_ode` forces them
equal everywhere. -/
theorem trajectory_eq_lift {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hWba : ∀ t, HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t)
    (hWbb : ∀ t, HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t)
    {ca cb : Fin N → ℝ → ℝ} (hsol : ∀ α, IsABFlow (σ α) τ (ca α) (cb α))
    (hinitA : ∀ γ, aMode (Wba 0) γ = ca γ 0 • r γ)
    (hinitB : ∀ γ, bMode (Wbb 0) γ = cb γ 0 • r γ) :
    ∀ t, (Wba t, Wbb t) = (aLift r ca t, bLift r cb t) := by
  refine eq_of_autonomous_ode (flowField_contDiff S τ)
    (fun s => (hWba s).prodMk (hWbb s))
    (fun s => (aLift_solves horth hdiag hsol s).prodMk (bLift_solves horth hdiag hsol s)) ?_
  have hA : Wba 0 = aLift r ca 0 := by
    funext i γ
    simpa only [aMode, aLift, Pi.smul_apply, smul_eq_mul] using congrFun (hinitA γ) i
  have hB : Wbb 0 = bLift r cb 0 := by
    funext α i
    simpa only [bMode, bLift, Pi.smul_apply, smul_eq_mul] using congrFun (hinitB α) i
  rw [hA, hB]

/-! ## Step 4 — forward-invariance (general core; scalar solutions assumed) -/

/-- **Forward-invariance of the orthogonal-mode manifold** (Saxe's *"`aᵅ` and `bᵅ` will remain
parallel to `rᵅ` for all future time"*). Given scalar two-mode solutions `ca, cb` of `ab_dyn`, a
matrix trajectory of `wbo_dyn` that lies on the manifold at `t = 0` lies on it for **all** `t`:
each `aᵅ(t)`, `bᵅ(t)` stays parallel to `rᵅ`. This discharges the membership hypotheses
`hmemA`/`hmemB` of `isABFlow_of_modeFlow` from an initial condition alone. -/
theorem manifold_forward_invariant {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hWba : ∀ t, HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t)
    (hWbb : ∀ t, HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t)
    {ca cb : Fin N → ℝ → ℝ} (hsol : ∀ α, IsABFlow (σ α) τ (ca α) (cb α))
    (hinitA : ∀ γ, aMode (Wba 0) γ = ca γ 0 • r γ)
    (hinitB : ∀ γ, bMode (Wbb 0) γ = cb γ 0 • r γ) :
    (∀ t γ, aMode (Wba t) γ = ca γ t • r γ) ∧ (∀ t γ, bMode (Wbb t) γ = cb γ t • r γ) := by
  have heq := trajectory_eq_lift horth hdiag hWba hWbb hsol hinitA hinitB
  simp only [Prod.mk.injEq] at heq
  refine ⟨fun t γ => ?_, fun t γ => ?_⟩
  · rw [(heq t).1, aMode_aLift]
  · rw [(heq t).2, bMode_bLift]

/-! ## Step 5 — the constructive balanced solution `ca = cb = √∘uf` -/

/-- The closed form `uf` is strictly positive on the paper regime `0 < u₀ < s`
(numerator `s · e^{…} > 0`, denominator `> 0` by `denom_pos`). -/
theorem uf_pos (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (t : ℝ) : 0 < uf s τ u₀ t := by
  have hs : 0 < s := hu₀.trans hlt
  unfold uf
  exact div_pos (mul_pos hs (Real.exp_pos _)) (denom_pos s τ u₀ hu₀ hlt t)

/-- **Balanced solution of `ab_dyn`.** On the regime `0 < u₀ < s`, `0 < τ`, the balanced pair
`a = b = √(uf s τ u₀)` solves the scalar two-mode flow `IsABFlow` (Saxe Eq. `ab_dyn`): from
`uf' = (2/τ) uf (s − uf)` (`uf_hasDerivAt`) and the chain rule for `√`, with `√uf · √uf = uf`,
`(√uf)' = (1/τ) √uf (s − uf) = √uf (s − √uf·√uf)/τ`. -/
theorem isABFlow_sqrt_uf (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (hτ : 0 < τ) :
    IsABFlow s τ (fun t => Real.sqrt (uf s τ u₀ t)) (fun t => Real.sqrt (uf s τ u₀ t)) := by
  have key : ∀ t, HasDerivAt (fun t => Real.sqrt (uf s τ u₀ t))
      (Real.sqrt (uf s τ u₀ t)
        * (s - Real.sqrt (uf s τ u₀ t) * Real.sqrt (uf s τ u₀ t)) / τ) t := by
    intro t
    have hpos := uf_pos s τ u₀ hu₀ hlt t
    have hsqrt := (uf_hasDerivAt s τ u₀ hu₀ hlt hτ t).sqrt hpos.ne'
    rw [show Real.sqrt (uf s τ u₀ t)
          * (s - Real.sqrt (uf s τ u₀ t) * Real.sqrt (uf s τ u₀ t)) / τ
        = (2 / τ * uf s τ u₀ t * (s - uf s τ u₀ t)) / (2 * Real.sqrt (uf s τ u₀ t)) from ?_]
    · exact hsqrt
    · set q := Real.sqrt (uf s τ u₀ t) with hqdef
      have hqpos : 0 < q := Real.sqrt_pos.mpr hpos
      have huq : uf s τ u₀ t = q * q := (Real.mul_self_sqrt hpos.le).symm
      rw [huq]; field_simp
  exact ⟨key, key⟩

/-! ## Step 6 — hypothesis-free headline and end-to-end corollary -/

/-- **Hypothesis-free headline (Phase D option 3, balanced paper regime).** For the balanced
orthogonal-mode initial condition `aᵅ(0) = bᵅ(0) = √(u₀ α) · rᵅ` with `0 < u₀ α < σ α`, a matrix
trajectory of the decoupled flow `wbo_dyn` *stays on the manifold for all time* and each mode's
scalar overlap obeys Saxe Eq. `ab_dyn`. The scalar solutions are **constructed** (`√∘uf`,
`isABFlow_sqrt_uf`), so — unlike `isABFlow_of_modeFlow` — this needs **no** manifold hypothesis,
only the initial condition. Conclusion: (1) per mode `α`, `IsABFlow (σ α) τ (√∘uf) (√∘uf)` (hence
the conservation law and the closed form `uf` of Layers 1–2); (2)–(3) forward-invariance — every
`aᵅ(t)`, `bᵅ(t)` remains parallel to `rᵅ`. -/
theorem isABFlow_of_modeFlow_of_init {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} (hτ : 0 < τ)
    {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hWba : ∀ t, HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t)
    (hWbb : ∀ t, HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t)
    {u₀ : Fin N → ℝ} (hu₀ : ∀ γ, 0 < u₀ γ) (hlt : ∀ γ, u₀ γ < σ γ)
    (hinitA : ∀ γ, aMode (Wba 0) γ = Real.sqrt (u₀ γ) • r γ)
    (hinitB : ∀ γ, bMode (Wbb 0) γ = Real.sqrt (u₀ γ) • r γ) :
    (∀ α, IsABFlow (σ α) τ (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t))
        (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t)))
      ∧ (∀ t γ, aMode (Wba t) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) t) • r γ)
      ∧ (∀ t γ, bMode (Wbb t) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) t) • r γ) := by
  have hsol : ∀ α, IsABFlow (σ α) τ (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t))
      (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t)) :=
    fun α => isABFlow_sqrt_uf (σ α) τ (u₀ α) (hu₀ α) (hlt α) hτ
  have hinitA' : ∀ γ, aMode (Wba 0) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) 0) • r γ := fun γ => by
    rw [hinitA γ, uf_zero (σ γ) τ (u₀ γ) (hu₀ γ) (hlt γ)]
  have hinitB' : ∀ γ, bMode (Wbb 0) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) 0) • r γ := fun γ => by
    rw [hinitB γ, uf_zero (σ γ) τ (u₀ γ) (hu₀ γ) (hlt γ)]
  have hinv := manifold_forward_invariant horth hdiag hWba hWbb hsol hinitA' hinitB'
  exact ⟨hsol, hinv.1, hinv.2⟩

/-- **End-to-end from network gradient descent (Phases A–D, option 3).** Composing the whole
chain: per-entry gradient flow on the network loss (`IsMatrixGradFlow`), an SVD `Σ³¹ = U S Vᵀ`
with diagonal `S`, and the balanced orthogonal-mode initial condition force each SVD-coordinate
mode `aᵅ = column α of (Wᵃ V)`, `bᵅ = row α of (Uᵀ Wᵇ)` to **stay parallel to `rᵅ` for all time**
and to obey Saxe Eq. `ab_dyn`. Unlike `isABFlow_of_gradFlow_on_manifold`, the manifold-for-all-`t`
hypothesis is discharged — only the initial condition is assumed. -/
theorem isABFlow_of_gradFlow_of_init {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {Sg S : Matrix (Fin N) (Fin N) ℝ} {U V : Matrix (Fin N) (Fin N) ℝ}
    (hdiag : S = Matrix.diagonal σ) (hsvd : IsSVD Sg U S V)
    {τ : ℝ} (hτ : 0 < τ)
    {Wa : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb)
    {u₀ : Fin N → ℝ} (hu₀ : ∀ γ, 0 < u₀ γ) (hlt : ∀ γ, u₀ γ < σ γ)
    (hinitA : ∀ γ, aMode (Wa 0 * V) γ = Real.sqrt (u₀ γ) • r γ)
    (hinitB : ∀ γ, bMode (Uᵀ * Wb 0) γ = Real.sqrt (u₀ γ) • r γ) :
    (∀ α, IsABFlow (σ α) τ (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t))
        (fun t => Real.sqrt (uf (σ α) τ (u₀ α) t)))
      ∧ (∀ t γ, aMode (Wa t * V) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) t) • r γ)
      ∧ (∀ t γ, bMode (Uᵀ * Wb t) γ = Real.sqrt (uf (σ γ) τ (u₀ γ) t) • r γ) :=
  isABFlow_of_modeFlow_of_init (Wba := fun s => Wa s * V) (Wbb := fun s => Uᵀ * Wb s)
    horth hdiag hτ
    (fun t => (wbo_dyn_of_gradFlow hsvd hflow t).1)
    (fun t => (wbo_dyn_of_gradFlow hsvd hflow t).2)
    hu₀ hlt hinitA hinitB

end DlnDynamics
