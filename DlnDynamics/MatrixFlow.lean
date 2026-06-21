import DlnDynamics.Basic

/-!
# Matrix gradient flow of the three-layer linear network (Phase A)

The full three-layer linear network (Saxe §1) maps `x ↦ Wᵇ Wᵃ x` with
`Wᵃ : N₂×N₁` (input→hidden) and `Wᵇ : N₃×N₂` (hidden→output). Under whitened
inputs (`Σ¹¹ = I`) the population square loss is

`E(Wᵃ, Wᵇ) = ½ ‖Σ³¹ − Wᵇ Wᵃ‖²_F = ½ ∑ᵢⱼ (Σ³¹ − Wᵇ Wᵃ)ᵢⱼ²`,

where `Σ³¹` is the input–output correlation matrix. This module derives Saxe
Eq. `wb_avg` — the matrix gradient flow

`τ Ẇᵃ = Wᵇᵀ (Σ³¹ − Wᵇ Wᵃ)`,  `τ Ẇᵇ = (Σ³¹ − Wᵇ Wᵃ) Wᵃᵀ`

— from per-entry gradient descent on `E`. This is the matrix analog of
`DlnDynamics.GradientFlow` (Layers 1–2): the entry partials are computed as
directional derivatives along the single-entry matrices `Matrix.single k l 1`
(avoiding single-entry-update bookkeeping), then bundled into a matrix-valued
`HasDerivAt` via `hasDerivAt_pi`.

This is Layer-3 **Phase A** and is complete and gap-free. Phase B (the SVD change
of variables `Σ³¹ = U S Vᵀ` decoupling the modes, with the SVD hypothesized)
builds on this; see `PROGRESS.md`. What is established here is the matrix flow
`wb_avg` from the network loss — *not yet* the SVD reduction to the scalar
`ab_dyn`; the scalar development in `GradientFlow`/`Network` is a derived
side result for the already-decoupled one-mode loss, not that reduction.

This module provides:

* `Ematrix` — the network square loss (Saxe Eq. `ab_en` with `Σ¹¹ = I`);
* `hasDerivAt_Ematrix_fst/_snd` — the entry partials `∂E/∂Wᵃₖₗ = −(Wᵇᵀ(Σ³¹−WᵇWᵃ))ₖₗ`,
  `∂E/∂Wᵇₖₗ = −((Σ³¹−WᵇWᵃ)Wᵃᵀ)ₖₗ`;
* `IsMatrixGradFlow` — per-entry gradient flow on `E`;
* `matrixFlow_of_gradFlow` — that flow is Saxe Eq. `wb_avg`.
-/

namespace DlnDynamics

open Matrix

variable {N₁ N₂ N₃ : ℕ}

/-- Three-layer network square loss with whitened inputs (`Σ¹¹ = I`):
`E(Wᵃ, Wᵇ) = ½ ∑ᵢⱼ (Σ³¹ − Wᵇ Wᵃ)ᵢⱼ²` (Saxe Eq. `ab_en`, single-mode-free form). -/
noncomputable def Ematrix (S : Matrix (Fin N₃) (Fin N₁) ℝ)
    (Wa : Matrix (Fin N₂) (Fin N₁) ℝ) (Wb : Matrix (Fin N₃) (Fin N₂) ℝ) : ℝ :=
  (∑ i, ∑ j, (S i j - (Wb * Wa) i j) ^ 2) / 2

/-- `B * single k l 1` selects column `l`: its `(i,j)` entry is `B i k` when
`j = l` and `0` otherwise. -/
private lemma mul_single_sel (B : Matrix (Fin N₃) (Fin N₂) ℝ) (k : Fin N₂) (l : Fin N₁)
    (i : Fin N₃) (j : Fin N₁) :
    (B * Matrix.single k l (1 : ℝ)) i j = if j = l then B i k else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k (fun p _ hp => by simp [Ne.symm hp]) (by simp)]
  simp [eq_comm]

/-- Entry of `B * (A + x • single k l 1)`, separating the `x`-linear part. -/
private lemma mulB_add_smul_apply (B : Matrix (Fin N₃) (Fin N₂) ℝ) (A : Matrix (Fin N₂) (Fin N₁) ℝ)
    (k : Fin N₂) (l : Fin N₁) (x : ℝ) (i : Fin N₃) (j : Fin N₁) :
    (B * (A + x • Matrix.single k l (1 : ℝ))) i j
      = (B * A) i j + x * (B * Matrix.single k l (1 : ℝ)) i j := by
  rw [Matrix.mul_add, Matrix.add_apply, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]

/-- Derivative at `0` of a squared affine function `x ↦ (c − x d)²`. -/
private lemma hasDerivAt_sq_affine (c d : ℝ) :
    HasDerivAt (fun x : ℝ => (c - x * d) ^ 2) (-2 * d * c) 0 := by
  have h1 : HasDerivAt (fun x : ℝ => c - x * d) (-d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_sub c
  have h2 := h1.mul h1
  simp only [pow_two]
  rw [show (-2 * d * c : ℝ) = (-d) * (c - 0 * d) + (c - 0 * d) * (-d) by ring]
  exact h2

/-- Entry partial of `E` in the first layer:
`∂E/∂Wᵃₖₗ = −(Wᵇᵀ (Σ³¹ − Wᵇ Wᵃ))ₖₗ` (the `a`-component of `−∇E`, Saxe Eq. `wb_avg`),
taken as the directional derivative of `E` along `single k l 1`. -/
theorem hasDerivAt_Ematrix_fst (S : Matrix (Fin N₃) (Fin N₁) ℝ)
    (A : Matrix (Fin N₂) (Fin N₁) ℝ) (B : Matrix (Fin N₃) (Fin N₂) ℝ) (k : Fin N₂) (l : Fin N₁) :
    HasDerivAt (fun (x : ℝ) => Ematrix S (A + x • Matrix.single k l (1 : ℝ)) B)
      (-((Bᵀ * (S - B * A)) k l)) 0 := by
  -- rewrite the loss into summands affine in `x`
  have hfun : (fun (x : ℝ) => Ematrix S (A + x • Matrix.single k l (1 : ℝ)) B)
      = (fun x => (∑ i, ∑ j,
          ((S i j - (B * A) i j) - x * (B * Matrix.single k l (1 : ℝ)) i j) ^ 2) / 2) := by
    funext x
    unfold Ematrix
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [mulB_add_smul_apply]; ring
  rw [hfun]
  -- assemble the derivative via the nested sum, with clean per-term values
  have hD := (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
      HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
        hasDerivAt_sq_affine (S i j - (B * A) i j)
          ((B * Matrix.single k l (1 : ℝ)) i j)).div_const 2
  -- match the target derivative value
  rw [show ((∑ i, ∑ j, -2 * (B * Matrix.single k l (1 : ℝ)) i j * (S i j - (B * A) i j)) / 2 : ℝ)
      = -((Bᵀ * (S - B * A)) k l) from ?_] at hD
  · simpa only [Finset.sum_apply] using hD
  · have hj : ∀ i : Fin N₃,
        (∑ j, -2 * (B * Matrix.single k l (1 : ℝ)) i j * (S i j - (B * A) i j))
          = -2 * ((S i l - (B * A) i l) * B i k) := by
      intro i
      rw [Finset.sum_eq_single l (fun j _ hjl => by rw [mul_single_sel]; simp [hjl]) (by simp),
        mul_single_sel, if_pos rfl]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hj i), ← Finset.mul_sum,
      show ((Bᵀ * (S - B * A)) k l) = ∑ i, (S i l - (B * A) i l) * B i k from ?_]
    · ring
    · rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl
        (fun i _ => by rw [Matrix.transpose_apply, Matrix.sub_apply, mul_comm])

/-- `single k l 1 * A` selects row `l`: its `(i,j)` entry is `A l j` when
`i = k` and `0` otherwise. -/
private lemma single_mul_sel (A : Matrix (Fin N₂) (Fin N₁) ℝ) (k : Fin N₃) (l : Fin N₂)
    (i : Fin N₃) (j : Fin N₁) :
    (Matrix.single k l (1 : ℝ) * A) i j = if i = k then A l j else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single l (fun p _ hp => by simp [Ne.symm hp]) (by simp)]
  simp [eq_comm]

/-- Entry of `(B + x • single k l 1) * A`, separating the `x`-linear part. -/
private lemma add_smul_single_mul_apply (B : Matrix (Fin N₃) (Fin N₂) ℝ)
    (A : Matrix (Fin N₂) (Fin N₁) ℝ) (k : Fin N₃) (l : Fin N₂) (x : ℝ) (i : Fin N₃) (j : Fin N₁) :
    ((B + x • Matrix.single k l (1 : ℝ)) * A) i j
      = (B * A) i j + x * (Matrix.single k l (1 : ℝ) * A) i j := by
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

/-- Entry partial of `E` in the second layer:
`∂E/∂Wᵇₖₗ = −((Σ³¹ − Wᵇ Wᵃ) Wᵃᵀ)ₖₗ` (the `b`-component of `−∇E`, Saxe Eq. `wb_avg`). -/
theorem hasDerivAt_Ematrix_snd (S : Matrix (Fin N₃) (Fin N₁) ℝ)
    (A : Matrix (Fin N₂) (Fin N₁) ℝ) (B : Matrix (Fin N₃) (Fin N₂) ℝ) (k : Fin N₃) (l : Fin N₂) :
    HasDerivAt (fun (x : ℝ) => Ematrix S A (B + x • Matrix.single k l (1 : ℝ)))
      (-(((S - B * A) * Aᵀ) k l)) 0 := by
  have hfun : (fun (x : ℝ) => Ematrix S A (B + x • Matrix.single k l (1 : ℝ)))
      = (fun x => (∑ i, ∑ j,
          ((S i j - (B * A) i j) - x * (Matrix.single k l (1 : ℝ) * A) i j) ^ 2) / 2) := by
    funext x
    unfold Ematrix
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [add_smul_single_mul_apply]; ring
  rw [hfun]
  have hD := (HasDerivAt.sum fun i (_ : i ∈ Finset.univ) =>
      HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
        hasDerivAt_sq_affine (S i j - (B * A) i j)
          ((Matrix.single k l (1 : ℝ) * A) i j)).div_const 2
  rw [show ((∑ i, ∑ j, -2 * (Matrix.single k l (1 : ℝ) * A) i j * (S i j - (B * A) i j)) / 2 : ℝ)
      = -(((S - B * A) * Aᵀ) k l) from ?_] at hD
  · simpa only [Finset.sum_apply] using hD
  · have hik : (∑ i, ∑ j, -2 * (Matrix.single k l (1 : ℝ) * A) i j * (S i j - (B * A) i j))
        = ∑ j, -2 * ((S k j - (B * A) k j) * A l j) := by
      rw [Finset.sum_eq_single k]
      · exact Finset.sum_congr rfl
          (fun j _ => by rw [single_mul_sel, if_pos rfl]; ring)
      · exact fun i _ hi => Finset.sum_eq_zero
          (fun j _ => by rw [single_mul_sel, if_neg hi]; ring)
      · simp
    rw [hik, ← Finset.mul_sum,
      show ((S - B * A) * Aᵀ) k l = ∑ j, (S k j - (B * A) k j) * A l j from ?_]
    · ring
    · rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl
        (fun j _ => by rw [Matrix.transpose_apply, Matrix.sub_apply])

/-- Per-entry gradient flow on the network square loss `E` with timescale `τ`:
each weight entry's velocity is `−1/τ` times its partial of `E`. -/
structure IsMatrixGradFlow (τ : ℝ) (S : Matrix (Fin N₃) (Fin N₁) ℝ)
    (Wa : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ) (Wb : ℝ → Matrix (Fin N₃) (Fin N₂) ℝ) : Prop where
  ha : ∀ t k l, HasDerivAt (fun s => Wa s k l)
        (-(deriv (fun (x : ℝ) => Ematrix S (Wa t + x • Matrix.single k l (1 : ℝ)) (Wb t)) 0) / τ) t
  hb : ∀ t k l, HasDerivAt (fun s => Wb s k l)
        (-(deriv (fun (x : ℝ) => Ematrix S (Wa t) (Wb t + x • Matrix.single k l (1 : ℝ))) 0) / τ) t

/-- **Matrix dynamics of the three-layer network (Saxe Eq. `wb_avg`).** Per-entry
gradient flow on the network square loss `E` is the matrix flow
`τ Ẇᵃ = Wᵇᵀ(Σ³¹ − Wᵇ Wᵃ)`, `τ Ẇᵇ = (Σ³¹ − Wᵇ Wᵃ)Wᵃᵀ`. -/
theorem matrixFlow_of_gradFlow {τ : ℝ} {S : Matrix (Fin N₃) (Fin N₁) ℝ}
    {Wa : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ} {Wb : ℝ → Matrix (Fin N₃) (Fin N₂) ℝ}
    (h : IsMatrixGradFlow τ S Wa Wb) (t : ℝ) :
    HasDerivAt Wa ((1 / τ) • ((Wb t)ᵀ * (S - Wb t * Wa t))) t ∧
      HasDerivAt Wb ((1 / τ) • ((S - Wb t * Wa t) * (Wa t)ᵀ)) t := by
  -- bundle the per-entry flows into matrix-valued derivatives (`hasDerivAt_pi`, via defeq)
  refine ⟨hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun l => ?_,
      hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun l => ?_⟩
  · have hflow := h.ha t k l
    rw [(hasDerivAt_Ematrix_fst S (Wa t) (Wb t) k l).deriv] at hflow
    rw [Matrix.smul_apply, smul_eq_mul,
      show (1 / τ) * ((Wb t)ᵀ * (S - Wb t * Wa t)) k l
        = -(-((Wb t)ᵀ * (S - Wb t * Wa t)) k l) / τ by ring]
    exact hflow
  · have hflow := h.hb t k l
    rw [(hasDerivAt_Ematrix_snd S (Wa t) (Wb t) k l).deriv] at hflow
    rw [Matrix.smul_apply, smul_eq_mul,
      show (1 / τ) * ((S - Wb t * Wa t) * (Wa t)ᵀ) k l
        = -(-((S - Wb t * Wa t) * (Wa t)ᵀ) k l) / τ by ring]
    exact hflow

end DlnDynamics
