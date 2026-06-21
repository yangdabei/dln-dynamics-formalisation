import DlnDynamics.SVDReduction

/-!
# Mode extraction from the decoupled SVD flow (Phase C, start)

Layer-3 **Phase C** (Saxe §1.1): read off the per-mode vector ODEs from the decoupled
flow `wbo_dyn`. We specialize to the square case `N₃ = N₁ = N` with `S = diagonal σ`
(`N₂` = hidden width, arbitrary); the rectangular-diagonal generalization is future work.

With `W̄ᵃ : N₂×N` and `W̄ᵇ : N×N₂`, the modes are
`aᵅ := column α of W̄ᵃ` (`aMode`) and `bᵅ := row α of W̄ᵇ` (`bMode`), both in hidden
space `ℝ^{N₂}`. Reading off column / row `α` of the decoupled flow gives Saxe Eqs.
`a_dyn` / `b_dyn` with the explicit competition sums over the other modes:

`τ ȧᵅ = (sᵅ − bᵅ·aᵅ) bᵅ − ∑_{γ≠α} (bᵞ·aᵅ) bᵞ`,
`τ ḃᵅ = (sᵅ − aᵅ·bᵅ) aᵅ − ∑_{γ≠α} (aᵞ·bᵅ) aᵞ`.

This module provides:

* `aMode` / `bMode` — the column/row mode vectors;
* `mul_apply_eq_dot` / `mul_apply_eq_dot'` — entries of `W̄ᵇ W̄ᵃ` as mode dot products;
* `flow_a_entry` / `flow_b_entry` — the per-entry competition identities (diagonal `S`);
* `a_dyn` / `b_dyn` — the per-mode vector ODEs (Saxe Eqs. `a_dyn`, `b_dyn`).
-/

namespace DlnDynamics

open Matrix

variable {N N₂ : ℕ}

/-- The `α`-th input–output mode read from `W̄ᵃ`: column `α`, a vector `aᵅ ∈ ℝ^{N₂}`. -/
def aMode (Wba : Matrix (Fin N₂) (Fin N) ℝ) (α : Fin N) : Fin N₂ → ℝ :=
  fun i => Wba i α

/-- The `α`-th input–output mode read from `W̄ᵇ`: row `α`, a vector `bᵅ ∈ ℝ^{N₂}`. -/
def bMode (Wbb : Matrix (Fin N) (Fin N₂) ℝ) (α : Fin N) : Fin N₂ → ℝ :=
  fun i => Wbb α i

/-- An entry of `W̄ᵇ W̄ᵃ` as a mode dot product: `(W̄ᵇ W̄ᵃ) k α = bᵏ · aᵅ`. -/
theorem mul_apply_eq_dot (Wba : Matrix (Fin N₂) (Fin N) ℝ) (Wbb : Matrix (Fin N) (Fin N₂) ℝ)
    (k α : Fin N) : (Wbb * Wba) k α = bMode Wbb k ⬝ᵥ aMode Wba α := by
  simp only [Matrix.mul_apply, dotProduct, bMode, aMode]

/-- An entry of `W̄ᵇ W̄ᵃ` as a mode dot product (other index order): `(W̄ᵇ W̄ᵃ) α k = aᵏ · bᵅ`. -/
theorem mul_apply_eq_dot' (Wba : Matrix (Fin N₂) (Fin N) ℝ) (Wbb : Matrix (Fin N) (Fin N₂) ℝ)
    (α k : Fin N) : (Wbb * Wba) α k = aMode Wba k ⬝ᵥ bMode Wbb α := by
  rw [Matrix.mul_apply, dotProduct]
  exact Finset.sum_congr rfl (fun j _ => by simp only [aMode, bMode]; ring)

/-! ## Per-entry competition identities (diagonal `S`) -/

/-- The `a`-flow value, entry `(i, α)`, in competition form. -/
theorem flow_a_entry {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ}
    (hdiag : S = Matrix.diagonal σ) (Wba : Matrix (Fin N₂) (Fin N) ℝ)
    (Wbb : Matrix (Fin N) (Fin N₂) ℝ) (α : Fin N) (i : Fin N₂) :
    (Wbbᵀ * (S - Wbb * Wba)) i α
      = (σ α - bMode Wbb α ⬝ᵥ aMode Wba α) * bMode Wbb α i
        - ∑ γ ∈ Finset.univ.erase α, (bMode Wbb γ ⬝ᵥ aMode Wba α) * bMode Wbb γ i := by
  have key : (Wbbᵀ * (S - Wbb * Wba)) i α
      = σ α * bMode Wbb α i - ∑ γ, (bMode Wbb γ ⬝ᵥ aMode Wba α) * bMode Wbb γ i := by
    have expand : ∀ k ∈ Finset.univ, Wbbᵀ i k * (S - Wbb * Wba) k α
        = Wbb k i * (if k = α then σ k else 0)
          - (bMode Wbb k ⬝ᵥ aMode Wba α) * bMode Wbb k i := by
      intro k _
      rw [Matrix.transpose_apply, Matrix.sub_apply, hdiag, Matrix.diagonal_apply, mul_sub,
          mul_apply_eq_dot]
      simp only [bMode]; ring
    rw [Matrix.mul_apply, Finset.sum_congr rfl expand, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single α (fun k _ hk => by rw [if_neg hk, mul_zero])
        (fun h => absurd (Finset.mem_univ α) h), if_pos rfl]
      simp only [bMode]; ring
  rw [key, ← Finset.add_sum_erase _ _ (Finset.mem_univ α)]
  ring

/-- The `b`-flow value, entry `(α, i)`, in competition form. -/
theorem flow_b_entry {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ}
    (hdiag : S = Matrix.diagonal σ) (Wba : Matrix (Fin N₂) (Fin N) ℝ)
    (Wbb : Matrix (Fin N) (Fin N₂) ℝ) (α : Fin N) (i : Fin N₂) :
    ((S - Wbb * Wba) * Wbaᵀ) α i
      = (σ α - aMode Wba α ⬝ᵥ bMode Wbb α) * aMode Wba α i
        - ∑ γ ∈ Finset.univ.erase α, (aMode Wba γ ⬝ᵥ bMode Wbb α) * aMode Wba γ i := by
  have key : ((S - Wbb * Wba) * Wbaᵀ) α i
      = σ α * aMode Wba α i - ∑ γ, (aMode Wba γ ⬝ᵥ bMode Wbb α) * aMode Wba γ i := by
    have expand : ∀ k ∈ Finset.univ, (S - Wbb * Wba) α k * Wbaᵀ k i
        = (if α = k then σ α else 0) * Wba i k
          - (aMode Wba k ⬝ᵥ bMode Wbb α) * aMode Wba k i := by
      intro k _
      rw [Matrix.transpose_apply, Matrix.sub_apply, hdiag, Matrix.diagonal_apply, sub_mul,
          mul_apply_eq_dot']
      simp only [aMode]
    rw [Matrix.mul_apply, Finset.sum_congr rfl expand, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_eq_single α (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_mul])
        (fun h => absurd (Finset.mem_univ α) h), if_pos rfl]
      simp only [aMode]
  rw [key, ← Finset.add_sum_erase _ _ (Finset.mem_univ α)]
  ring

/-! ## The per-mode vector dynamics (`a_dyn`, `b_dyn`) -/

/-- **Saxe Eq. `a_dyn`.** Reading off column `α` of the decoupled flow `wbo_dyn` (with
diagonal `S = diagonal σ`) gives the per-mode vector ODE
`τ ȧᵅ = (sᵅ − bᵅ·aᵅ) bᵅ − ∑_{γ≠α} (bᵞ·aᵅ) bᵞ`. -/
theorem a_dyn {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ} {t : ℝ}
    (hWba : HasDerivAt Wba ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) t) (α : Fin N) :
    HasDerivAt (fun s => aMode (Wba s) α)
      ((1 / τ) • ((σ α - bMode (Wbb t) α ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) α
        - ∑ γ ∈ Finset.univ.erase α,
            (bMode (Wbb t) γ ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) γ)) t := by
  have hproj : HasDerivAt (fun s => aMode (Wba s) α)
      (fun i => ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) i α) t :=
    hasDerivAt_pi.2 (fun i => hasDerivAt_pi.1 (hasDerivAt_pi.1 hWba i) α)
  have hvec : (fun i => ((1 / τ) • ((Wbb t)ᵀ * (S - Wbb t * Wba t))) i α)
      = (1 / τ) • ((σ α - bMode (Wbb t) α ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) α
          - ∑ γ ∈ Finset.univ.erase α,
              (bMode (Wbb t) γ ⬝ᵥ aMode (Wba t) α) • bMode (Wbb t) γ) := by
    funext i
    rw [Matrix.smul_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    rw [flow_a_entry hdiag (Wba t) (Wbb t) α i]
  rwa [hvec] at hproj

/-- **Saxe Eq. `b_dyn`.** Reading off row `α` of the decoupled flow `wbo_dyn` (with
diagonal `S = diagonal σ`) gives the per-mode vector ODE
`τ ḃᵅ = (sᵅ − aᵅ·bᵅ) aᵅ − ∑_{γ≠α} (aᵞ·bᵅ) aᵞ`. -/
theorem b_dyn {σ : Fin N → ℝ} {S : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ)
    {τ : ℝ} {Wba : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wbb : ℝ → Matrix (Fin N) (Fin N₂) ℝ} {t : ℝ}
    (hWbb : HasDerivAt Wbb ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) t) (α : Fin N) :
    HasDerivAt (fun s => bMode (Wbb s) α)
      ((1 / τ) • ((σ α - aMode (Wba t) α ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) α
        - ∑ γ ∈ Finset.univ.erase α,
            (aMode (Wba t) γ ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) γ)) t := by
  have hproj : HasDerivAt (fun s => bMode (Wbb s) α)
      (fun i => ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) α i) t :=
    hasDerivAt_pi.2 (fun i => hasDerivAt_pi.1 (hasDerivAt_pi.1 hWbb α) i)
  have hvec : (fun i => ((1 / τ) • ((S - Wbb t * Wba t) * (Wba t)ᵀ)) α i)
      = (1 / τ) • ((σ α - aMode (Wba t) α ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) α
          - ∑ γ ∈ Finset.univ.erase α,
              (aMode (Wba t) γ ⬝ᵥ bMode (Wbb t) α) • aMode (Wba t) γ) := by
    funext i
    rw [Matrix.smul_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul]
    rw [flow_b_entry hdiag (Wba t) (Wbb t) α i]
  rwa [hvec] at hproj

/-! ## End-to-end: mode dynamics straight from network gradient descent -/

/-- **`a_dyn` from gradient descent.** Composing Phases A–C: per-entry gradient flow on
the network loss (`IsMatrixGradFlow`), given an SVD `Σ³¹ = U S Vᵀ` with diagonal `S`,
makes the SVD-coordinate mode `aᵅ = column α of (Wᵃ V)` obey Saxe Eq. `a_dyn`. -/
theorem a_dyn_of_gradFlow {σ : Fin N → ℝ} {Sg S : Matrix (Fin N) (Fin N) ℝ}
    {U V : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ) (hsvd : IsSVD Sg U S V)
    {τ : ℝ} {Wa : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb) (t : ℝ) (α : Fin N) :
    HasDerivAt (fun s => aMode (Wa s * V) α)
      ((1 / τ) • ((σ α - bMode (Uᵀ * Wb t) α ⬝ᵥ aMode (Wa t * V) α) • bMode (Uᵀ * Wb t) α
        - ∑ γ ∈ Finset.univ.erase α,
            (bMode (Uᵀ * Wb t) γ ⬝ᵥ aMode (Wa t * V) α) • bMode (Uᵀ * Wb t) γ)) t :=
  a_dyn (Wba := fun s => Wa s * V) (Wbb := fun s => Uᵀ * Wb s) hdiag
    (wbo_dyn_of_gradFlow hsvd hflow t).1 α

/-- **`b_dyn` from gradient descent.** As `a_dyn_of_gradFlow`, for the mode
`bᵅ = row α of (Uᵀ Wᵇ)` (Saxe Eq. `b_dyn`). -/
theorem b_dyn_of_gradFlow {σ : Fin N → ℝ} {Sg S : Matrix (Fin N) (Fin N) ℝ}
    {U V : Matrix (Fin N) (Fin N) ℝ} (hdiag : S = Matrix.diagonal σ) (hsvd : IsSVD Sg U S V)
    {τ : ℝ} {Wa : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb) (t : ℝ) (α : Fin N) :
    HasDerivAt (fun s => bMode (Uᵀ * Wb s) α)
      ((1 / τ) • ((σ α - aMode (Wa t * V) α ⬝ᵥ bMode (Uᵀ * Wb t) α) • aMode (Wa t * V) α
        - ∑ γ ∈ Finset.univ.erase α,
            (aMode (Wa t * V) γ ⬝ᵥ bMode (Uᵀ * Wb t) α) • aMode (Wa t * V) γ)) t :=
  b_dyn (Wba := fun s => Wa s * V) (Wbb := fun s => Uᵀ * Wb s) hdiag
    (wbo_dyn_of_gradFlow hsvd hflow t).2 α

end DlnDynamics
