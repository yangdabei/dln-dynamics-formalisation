import DlnDynamics.ModeDynamics

/-!
# Decoupled invariant manifold and reduction to scalar `ab_dyn` (Phase D, option 1)

Layer-3 **Phase D** (Saxe §"The time course of learning", arXiv lines 162–189). Saxe
restricts to a special class of initial conditions where the connectivity modes are
*aligned to an orthonormal frame*: `aᵅ ∝ rᵅ`, `bᵅ ∝ rᵅ` with `rᵅ · rᵝ = δ_{αβ}`. The
paper observes:

* *"because the different active modes are orthogonal to each other, they do not
  compete... (all dot products in the second terms of `a_dyn` are 0)"* — the
  **competition vanishes** (`competition_vanishes`);
* *"this class of conditions defines an invariant manifold... let a = aᵅ·rᵅ,
  b = bᵅ·rᵅ ... then the dynamics of the scalar projections (a,b) obeys [`ab_dyn`]"* —
  the **reduction** to the scalar two-mode flow `IsABFlow` (`isABFlow_of_modeFlow`).

We follow that argument literally: on the manifold the competition sums drop, the
surviving cooperative term is `(σα − aᵅ·bᵅ) bᵅ`, and projecting onto `rᵅ` (using
`|rᵅ| = 1`) yields `τ ȧ = b(σα − ab)` — Saxe Eq. `ab_dyn`, i.e. `IsABFlow`. This closes
the chain to Layers 1–2 (`Conservation`, `ClosedForm`).

**Deferred (option 3 / the genuinely hard part).** The paper's *"It is straightforward
to verify that ... aᵅ and bᵅ will remain parallel to rᵅ for all future time"* — i.e.
forward-invariance *in time* of the manifold — is a separate ODE-uniqueness argument and
is NOT proved here; we take manifold membership (`aᵅ(t) ∝ rᵅ` for all `t`) as an explicit
hypothesis. See `PHASE_D_OPTION3.md`.

This module provides:

* `HasDerivAt.dotProduct_const` — project a vector derivative onto a constant vector;
* `competition_vanishes` — orthogonal modes don't compete (Saxe line 181);
* `isABFlow_of_modeFlow` — on the manifold, mode dynamics reduces to scalar `ab_dyn`;
* `isABFlow_of_gradFlow_on_manifold` — the whole chain from network gradient descent.
-/

namespace DlnDynamics

open Matrix

variable {N N₂ : ℕ}

/-- Project a vector-valued `HasDerivAt` onto a constant vector `w`: differentiating
`s ↦ v s ⬝ᵥ w` gives `v' ⬝ᵥ w`. (Entrywise, like `HasDerivAt.matrix_mul_const`.) -/
theorem HasDerivAt.dotProduct_const {v : ℝ → Fin N₂ → ℝ} {v' : Fin N₂ → ℝ} {t : ℝ}
    (h : HasDerivAt v v' t) (w : Fin N₂ → ℝ) :
    HasDerivAt (fun s => v s ⬝ᵥ w) (v' ⬝ᵥ w) t := by
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (hasDerivAt_pi.1 h i).mul_const (w i))
  have hfun : (fun s => v s ⬝ᵥ w) = ∑ i, (fun s => v s i * w i) := by
    funext s; simp only [dotProduct, Finset.sum_apply]
  have hval : v' ⬝ᵥ w = ∑ i, v' i * w i := by simp only [dotProduct]
  rw [hfun, hval]; exact hsum

/-- **Competition vanishes on the orthogonal-mode manifold** (Saxe line 181). If every
mode `u γ` is aligned to its frame direction `rᵞ` and the fixed mode `w` is aligned to
`rᵅ`, then the competition sum over `γ ≠ α` is zero, because distinct modes are
orthogonal (`u γ ⬝ᵥ w = cu γ · cw · (rᵞ·rᵅ) = 0`). -/
theorem competition_vanishes {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {u : Fin N → Fin N₂ → ℝ} {w : Fin N₂ → ℝ} {cu : Fin N → ℝ} {cw : ℝ} (α : Fin N)
    (hu : ∀ γ, u γ = cu γ • r γ) (hw : w = cw • r α) :
    ∑ γ ∈ Finset.univ.erase α, (u γ ⬝ᵥ w) • u γ = 0 := by
  apply Finset.sum_eq_zero
  intro γ hγ
  have hγα : γ ≠ α := Finset.ne_of_mem_erase hγ
  have hdot : u γ ⬝ᵥ w = 0 := by
    rw [hu γ, hw, smul_dotProduct, dotProduct_smul, horth γ α, if_neg hγα, smul_zero, smul_zero]
  rw [hdot, zero_smul]

/-- **Reduction to scalar `ab_dyn` (Saxe Eq. `ab_dyn`).** On the orthogonal-mode
manifold — every mode `aᵞ(t) = ca γ t · rᵞ`, `bᵞ(t) = cb γ t · rᵞ` for all `t`, with
`{rᵅ}` orthonormal — the decoupled mode dynamics `wbo_dyn` reduces, for each mode `α`,
to the scalar two-mode flow `IsABFlow (σ α) τ (ca α) (cb α)`: the competition drops out
and projecting onto `rᵅ` gives `τ ȧ = b(σα − ab)`, `τ ḃ = a(σα − ab)`. -/
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
    IsABFlow (σ α) τ (ca α) (cb α) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- a-equation: the mode follows `a_dyn`, project onto `rᵅ`.
    have hproj := HasDerivAt.dotProduct_const (a_dyn hdiag (hWba t) α) (r α)
    have hca : (fun s => aMode (Wba s) α ⬝ᵥ r α) = ca α := by
      funext s; rw [hmemA s α, smul_dotProduct, horth α α, if_pos rfl, smul_eq_mul, mul_one]
    have hbb : bMode (Wbb t) α ⬝ᵥ aMode (Wba t) α = ca α t * cb α t := by
      rw [hmemB t α, hmemA t α, smul_dotProduct, dotProduct_smul, horth α α, if_pos rfl,
        smul_eq_mul, smul_eq_mul, mul_one]; ring
    have hbr : bMode (Wbb t) α ⬝ᵥ r α = cb α t := by
      rw [hmemB t α, smul_dotProduct, horth α α, if_pos rfl, smul_eq_mul, mul_one]
    have hval : ((1 / τ) • ((σ α - bMode (Wbb t) α ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) α
          - ∑ γ ∈ Finset.univ.erase α,
              (bMode (Wbb t) γ ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) γ)) ⬝ᵥ r α
        = cb α t * (σ α - ca α t * cb α t) / τ := by
      rw [competition_vanishes horth α (hmemB t) (hmemA t α), sub_zero, smul_dotProduct,
        smul_dotProduct, hbr, hbb, smul_eq_mul]
      ring
    rw [hca] at hproj
    rw [hval] at hproj
    exact hproj
  · -- b-equation: symmetric.
    have hproj := HasDerivAt.dotProduct_const (b_dyn hdiag (hWbb t) α) (r α)
    have hcb : (fun s => bMode (Wbb s) α ⬝ᵥ r α) = cb α := by
      funext s; rw [hmemB s α, smul_dotProduct, horth α α, if_pos rfl, smul_eq_mul, mul_one]
    have haa : aMode (Wba t) α ⬝ᵥ bMode (Wbb t) α = ca α t * cb α t := by
      rw [hmemA t α, hmemB t α, smul_dotProduct, dotProduct_smul, horth α α, if_pos rfl,
        smul_eq_mul, smul_eq_mul, mul_one]
    have har : aMode (Wba t) α ⬝ᵥ r α = ca α t := by
      rw [hmemA t α, smul_dotProduct, horth α α, if_pos rfl, smul_eq_mul, mul_one]
    have hval : ((1 / τ) • ((σ α - aMode (Wba t) α ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) α
          - ∑ γ ∈ Finset.univ.erase α,
              (aMode (Wba t) γ ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) γ)) ⬝ᵥ r α
        = ca α t * (σ α - ca α t * cb α t) / τ := by
      rw [competition_vanishes horth α (hmemA t) (hmemB t α), sub_zero, smul_dotProduct,
        smul_dotProduct, har, haa, smul_eq_mul]
      ring
    rw [hcb] at hproj
    rw [hval] at hproj
    exact hproj

/-- **End-to-end (Phases A–D, option 1): scalar `ab_dyn` from network gradient descent.**
Per-entry gradient flow on the network loss, an SVD `Σ³¹ = U S Vᵀ` with diagonal `S`, and
the orthogonal-mode manifold together force each mode's scalar projections `(ca α, cb α)`
to obey Saxe Eq. `ab_dyn` (`IsABFlow`) — hence the conservation law and closed form of
Layers 1–2. (Forward-invariance of the manifold in time is assumed via `hmemA`/`hmemB`;
see option 3.) -/
theorem isABFlow_of_gradFlow_on_manifold {r : Fin N → Fin N₂ → ℝ}
    (horth : ∀ α β, r α ⬝ᵥ r β = if α = β then 1 else 0)
    {σ : Fin N → ℝ} {Sg S : Matrix (Fin N) (Fin N) ℝ} {U V : Matrix (Fin N) (Fin N) ℝ}
    (hdiag : S = Matrix.diagonal σ) (hsvd : IsSVD Sg U S V)
    {τ : ℝ} {Wa : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb)
    {ca cb : Fin N → ℝ → ℝ}
    (hmemA : ∀ t γ, aMode (Wa t * V) γ = ca γ t • r γ)
    (hmemB : ∀ t γ, bMode (Uᵀ * Wb t) γ = cb γ t • r γ)
    (α : Fin N) :
    IsABFlow (σ α) τ (ca α) (cb α) :=
  isABFlow_of_modeFlow (Wba := fun s => Wa s * V) (Wbb := fun s => Uᵀ * Wb s) horth hdiag
    (fun t => (wbo_dyn_of_gradFlow hsvd hflow t).1)
    (fun t => (wbo_dyn_of_gradFlow hsvd hflow t).2)
    hmemA hmemB α

end DlnDynamics
