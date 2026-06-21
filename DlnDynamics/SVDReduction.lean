import DlnDynamics.MatrixFlow
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Mul

/-!
# SVD change of variables for the three-layer matrix flow (Phase B)

Layer-3 **Phase B** (Saxe §1.1): the orthogonal change of variables that decouples
the modes. Take a singular value decomposition `Σ³¹ = U S Vᵀ` of the input–output
correlation matrix (with `U`, `V` orthogonal) **as a hypothesis** (`IsSVD`); the SVD
*existence* is Phase E and is deferred. Substituting `Wᵃ = W̄ᵃ Vᵀ`, `Wᵇ = U W̄ᵇ`
(equivalently `W̄ᵃ = Wᵃ V`, `W̄ᵇ = Uᵀ Wᵇ`) turns the matrix gradient flow `wb_avg`
(`MatrixFlow.matrixFlow_of_gradFlow`) into the decoupled flow `wbo_dyn`:

`τ Ẇ̄ᵃ = W̄ᵇᵀ (S − W̄ᵇ W̄ᵃ)`,  `τ Ẇ̄ᵇ = (S − W̄ᵇ W̄ᵃ) W̄ᵃᵀ`.

The change of variables needs only orthogonality (`UᵀU = 1`, `VᵀV = 1`); the reverse
identities `UUᵀ = 1`, `VVᵀ = 1` follow for square `U`, `V` (`mul_eq_one_comm`).

The target correlation matrix `Σ³¹` is named `Sg` in the Lean source (the glyph `Σ`
is a reserved token).

This module provides:

* `trace_transpose_mul_self` — `(Mᵀ M).trace = ∑ᵢⱼ Mᵢⱼ²` (Frobenius squared as a trace);
* `sum_sq_mul_orthogonal` — Frobenius orthogonal invariance `∑ᵢⱼ (U M Vᵀ)ᵢⱼ² = ∑ᵢⱼ Mᵢⱼ²`;
* `Ematrix_orthogonal_invariant` — the network loss is preserved by the change of variables;
* `HasDerivAt.matrix_mul_const` / `HasDerivAt.const_matrix_mul` — derivative through a
  constant matrix factor;
* `IsSVD` — the SVD hypothesis interface, with derived `hUU`, `hVV`;
* `change_of_vars_a` / `change_of_vars_b` — the flow-value identities;
* `wbo_dyn` / `wbo_dyn_of_gradFlow` — the decoupled flow in the SVD basis (Saxe Eq. `wbo_dyn`).
-/

namespace DlnDynamics

open Matrix

variable {N₁ N₂ N₃ : ℕ}

/-! ## Frobenius norm as a trace, and orthogonal invariance -/

/-- The squared Frobenius norm as a trace: `(Mᵀ * M).trace = ∑ᵢⱼ (M i j)²`. -/
theorem trace_transpose_mul_self (M : Matrix (Fin N₃) (Fin N₁) ℝ) :
    (Mᵀ * M).trace = ∑ i, ∑ j, (M i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [pow_two]))

/-- **Frobenius orthogonal invariance.** For orthogonal `U` (`Uᵀ U = 1`) and `V`
(`Vᵀ V = 1`), conjugation leaves the sum of squared entries unchanged:
`∑ᵢⱼ ((U M Vᵀ) i j)² = ∑ᵢⱼ (M i j)²`. Proof: write both as traces of the Gram
matrix, then cancel by cyclicity (`trace_mul_comm`/`trace_mul_cycle`) and `= 1`. -/
theorem sum_sq_mul_orthogonal (U : Matrix (Fin N₃) (Fin N₃) ℝ)
    (M : Matrix (Fin N₃) (Fin N₁) ℝ) (V : Matrix (Fin N₁) (Fin N₁) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    ∑ i, ∑ j, ((U * M * Vᵀ) i j) ^ 2 = ∑ i, ∑ j, (M i j) ^ 2 := by
  have hNNt : (U * M * Vᵀ) * (U * M * Vᵀ)ᵀ = U * (M * Mᵀ) * Uᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        show (U * M * Vᵀ) * (V * (Mᵀ * Uᵀ)) = U * M * (Vᵀ * V) * Mᵀ * Uᵀ from by
          simp only [Matrix.mul_assoc],
        hV, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [← trace_transpose_mul_self (U * M * Vᵀ), ← trace_transpose_mul_self M,
      Matrix.trace_mul_comm, hNNt, Matrix.trace_mul_cycle, hU, Matrix.one_mul,
      Matrix.trace_mul_comm]

/-! ## The network loss is invariant under the change of variables -/

/-- The network square loss is unchanged by the orthogonal change of variables:
`E(Σ³¹, W̄ᵃ Vᵀ, U W̄ᵇ) = E(S, W̄ᵃ, W̄ᵇ)` when `Σ³¹ = U S Vᵀ`. -/
theorem Ematrix_orthogonal_invariant
    (Sg S : Matrix (Fin N₃) (Fin N₁) ℝ) (U : Matrix (Fin N₃) (Fin N₃) ℝ)
    (V : Matrix (Fin N₁) (Fin N₁) ℝ) (Wba : Matrix (Fin N₂) (Fin N₁) ℝ)
    (Wbb : Matrix (Fin N₃) (Fin N₂) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hfact : Sg = U * S * Vᵀ) :
    Ematrix Sg (Wba * Vᵀ) (U * Wbb) = Ematrix S Wba Wbb := by
  have hmat : Sg - (U * Wbb) * (Wba * Vᵀ) = U * (S - Wbb * Wba) * Vᵀ := by
    rw [hfact, Matrix.mul_sub, Matrix.sub_mul,
        show (U * Wbb) * (Wba * Vᵀ) = U * (Wbb * Wba) * Vᵀ from by simp only [Matrix.mul_assoc]]
  have hL : (∑ i, ∑ j, (Sg i j - ((U * Wbb) * (Wba * Vᵀ)) i j) ^ 2)
      = ∑ i, ∑ j, ((U * (S - Wbb * Wba) * Vᵀ) i j) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [← Matrix.sub_apply, hmat]))
  have hR : (∑ i, ∑ j, (S i j - (Wbb * Wba) i j) ^ 2)
      = ∑ i, ∑ j, ((S - Wbb * Wba) i j) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [Matrix.sub_apply]))
  unfold Ematrix
  rw [hL, hR, sum_sq_mul_orthogonal U (S - Wbb * Wba) V hU hV]

/-! ## Derivative through a constant matrix factor -/

/-- Right-multiplication by a constant matrix commutes with `HasDerivAt`. -/
theorem HasDerivAt.matrix_mul_const {f : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ}
    {f' : Matrix (Fin N₂) (Fin N₁) ℝ} {t : ℝ} (hf : HasDerivAt f f' t)
    (C : Matrix (Fin N₁) (Fin N₃) ℝ) :
    HasDerivAt (fun s => f s * C) (f' * C) t := by
  refine hasDerivAt_pi.2 (fun k => hasDerivAt_pi.2 (fun l => ?_))
  have hentry : ∀ m, HasDerivAt (fun s => f s k m) (f' k m) t :=
    fun m => hasDerivAt_pi.1 (hasDerivAt_pi.1 hf k) m
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun m (_ : m ∈ Finset.univ) => (hentry m).mul_const (C m l))
  have hfun : (fun s => (f s * C) k l) = ∑ m, (fun s => f s k m * C m l) := by
    funext s; simp only [Matrix.mul_apply, Finset.sum_apply]
  have hval : (f' * C) k l = ∑ m, f' k m * C m l := by rw [Matrix.mul_apply]
  rw [hfun, hval]; exact hsum

/-- Left-multiplication by a constant matrix commutes with `HasDerivAt`. -/
theorem HasDerivAt.const_matrix_mul {f : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ}
    {f' : Matrix (Fin N₂) (Fin N₁) ℝ} {t : ℝ} (hf : HasDerivAt f f' t)
    (C : Matrix (Fin N₃) (Fin N₂) ℝ) :
    HasDerivAt (fun s => C * f s) (C * f') t := by
  refine hasDerivAt_pi.2 (fun k => hasDerivAt_pi.2 (fun l => ?_))
  have hentry : ∀ m, HasDerivAt (fun s => f s m l) (f' m l) t :=
    fun m => hasDerivAt_pi.1 (hasDerivAt_pi.1 hf m) l
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun m (_ : m ∈ Finset.univ) => HasDerivAt.const_mul (C k m) (hentry m))
  have hfun : (fun s => (C * f s) k l) = ∑ m, (fun s => C k m * f s m l) := by
    funext s; simp only [Matrix.mul_apply, Finset.sum_apply]
  have hval : (C * f') k l = ∑ m, C k m * f' m l := by rw [Matrix.mul_apply]
  rw [hfun, hval]; exact hsum

/-! ## The SVD hypothesis interface -/

/-- An SVD of `Σ³¹` (`Sg`): orthogonal `U`, `V` and `Sg = U S Vᵀ`. `S` is left general
here (its diagonal structure is used downstream in Phase C). This is the *hypothesis*
discharged by SVD existence (Phase E). -/
structure IsSVD (Sg : Matrix (Fin N₃) (Fin N₁) ℝ) (U : Matrix (Fin N₃) (Fin N₃) ℝ)
    (S : Matrix (Fin N₃) (Fin N₁) ℝ) (V : Matrix (Fin N₁) (Fin N₁) ℝ) : Prop where
  hU : Uᵀ * U = 1
  hV : Vᵀ * V = 1
  hfact : Sg = U * S * Vᵀ

namespace IsSVD

variable {Sg S : Matrix (Fin N₃) (Fin N₁) ℝ} {U : Matrix (Fin N₃) (Fin N₃) ℝ}
  {V : Matrix (Fin N₁) (Fin N₁) ℝ}

/-- For square orthogonal `U`, `Uᵀ U = 1` gives `U Uᵀ = 1`. -/
theorem hUU (h : IsSVD Sg U S V) : U * Uᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h.hU

/-- For square orthogonal `V`, `Vᵀ V = 1` gives `V Vᵀ = 1`. -/
theorem hVV (h : IsSVD Sg U S V) : V * Vᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp h.hV

end IsSVD

/-! ## The flow-value identities -/

/-- The `a`-component of the flow in SVD coordinates:
`Wᵇᵀ (Σ³¹ − Wᵇ Wᵃ) V = W̄ᵇᵀ (S − W̄ᵇ W̄ᵃ)` with `W̄ᵃ = Wᵃ V`, `W̄ᵇ = Uᵀ Wᵇ`. -/
theorem change_of_vars_a {Sg S : Matrix (Fin N₃) (Fin N₁) ℝ} {U : Matrix (Fin N₃) (Fin N₃) ℝ}
    {V : Matrix (Fin N₁) (Fin N₁) ℝ} (h : IsSVD Sg U S V)
    (Wa : Matrix (Fin N₂) (Fin N₁) ℝ) (Wb : Matrix (Fin N₃) (Fin N₂) ℝ) :
    Wbᵀ * (Sg - Wb * Wa) * V = (Uᵀ * Wb)ᵀ * (S - (Uᵀ * Wb) * (Wa * V)) := by
  rw [h.hfact, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub]
  congr 1
  · rw [show Wbᵀ * (U * S * Vᵀ) * V = Wbᵀ * U * S * (Vᵀ * V) from by simp only [Matrix.mul_assoc],
        h.hV, Matrix.mul_one]
  · rw [show Wbᵀ * (Wb * Wa) * V = Wbᵀ * Wb * Wa * V from by simp only [Matrix.mul_assoc],
        show Wbᵀ * U * ((Uᵀ * Wb) * (Wa * V)) = Wbᵀ * (U * Uᵀ) * Wb * Wa * V from by
          simp only [Matrix.mul_assoc],
        h.hUU, Matrix.mul_one]

/-- The `b`-component of the flow in SVD coordinates:
`Uᵀ (Σ³¹ − Wᵇ Wᵃ) Wᵃᵀ = (S − W̄ᵇ W̄ᵃ) W̄ᵃᵀ` with `W̄ᵃ = Wᵃ V`, `W̄ᵇ = Uᵀ Wᵇ`. -/
theorem change_of_vars_b {Sg S : Matrix (Fin N₃) (Fin N₁) ℝ} {U : Matrix (Fin N₃) (Fin N₃) ℝ}
    {V : Matrix (Fin N₁) (Fin N₁) ℝ} (h : IsSVD Sg U S V)
    (Wa : Matrix (Fin N₂) (Fin N₁) ℝ) (Wb : Matrix (Fin N₃) (Fin N₂) ℝ) :
    Uᵀ * (Sg - Wb * Wa) * Waᵀ = (S - (Uᵀ * Wb) * (Wa * V)) * (Wa * V)ᵀ := by
  rw [h.hfact, Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
  congr 1
  · rw [show Uᵀ * (U * S * Vᵀ) * Waᵀ = (Uᵀ * U) * S * (Vᵀ * Waᵀ) from by simp only [Matrix.mul_assoc],
        h.hU, Matrix.one_mul]
  · rw [show Uᵀ * (Wb * Wa) * Waᵀ = Uᵀ * Wb * Wa * Waᵀ from by simp only [Matrix.mul_assoc],
        show (Uᵀ * Wb) * (Wa * V) * (Vᵀ * Waᵀ) = Uᵀ * Wb * Wa * (V * Vᵀ) * Waᵀ from by
          simp only [Matrix.mul_assoc],
        h.hVV, Matrix.mul_one]

/-! ## The decoupled flow in the SVD basis (`wbo_dyn`) -/

/-- **Change of variables on the flow.** Given an SVD `Σ³¹ = U S Vᵀ` and the matrix
flow `wb_avg` for `Wᵃ, Wᵇ`, the barred coordinates `W̄ᵃ = Wᵃ V`, `W̄ᵇ = Uᵀ Wᵇ` satisfy
the decoupled flow `wbo_dyn` (Saxe Eq. `wbo_dyn`). -/
theorem wbo_dyn {Sg S : Matrix (Fin N₃) (Fin N₁) ℝ} {U : Matrix (Fin N₃) (Fin N₃) ℝ}
    {V : Matrix (Fin N₁) (Fin N₁) ℝ} (h : IsSVD Sg U S V) {τ : ℝ}
    {Wa : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ} {Wb : ℝ → Matrix (Fin N₃) (Fin N₂) ℝ} {t : ℝ}
    (hWa : HasDerivAt Wa ((1 / τ) • ((Wb t)ᵀ * (Sg - Wb t * Wa t))) t)
    (hWb : HasDerivAt Wb ((1 / τ) • ((Sg - Wb t * Wa t) * (Wa t)ᵀ)) t) :
    HasDerivAt (fun s => Wa s * V)
        ((1 / τ) • ((Uᵀ * Wb t)ᵀ * (S - (Uᵀ * Wb t) * (Wa t * V)))) t ∧
      HasDerivAt (fun s => Uᵀ * Wb s)
        ((1 / τ) • ((S - (Uᵀ * Wb t) * (Wa t * V)) * (Wa t * V)ᵀ)) t := by
  refine ⟨?_, ?_⟩
  · have hd := HasDerivAt.matrix_mul_const hWa V
    rw [Matrix.smul_mul, change_of_vars_a h (Wa t) (Wb t)] at hd
    exact hd
  · have hd := HasDerivAt.const_matrix_mul hWb Uᵀ
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, change_of_vars_b h (Wa t) (Wb t)] at hd
    exact hd

/-- **Decoupled SVD dynamics from gradient descent (Saxe Eq. `wbo_dyn`).** Composing
Phase A (`matrixFlow_of_gradFlow`) with the change of variables: per-entry gradient
flow on the network loss, written in the SVD basis, is the decoupled flow
`τ Ẇ̄ᵃ = W̄ᵇᵀ(S − W̄ᵇ W̄ᵃ)`, `τ Ẇ̄ᵇ = (S − W̄ᵇ W̄ᵃ) W̄ᵃᵀ`. -/
theorem wbo_dyn_of_gradFlow {Sg S : Matrix (Fin N₃) (Fin N₁) ℝ}
    {U : Matrix (Fin N₃) (Fin N₃) ℝ} {V : Matrix (Fin N₁) (Fin N₁) ℝ} (h : IsSVD Sg U S V)
    {τ : ℝ} {Wa : ℝ → Matrix (Fin N₂) (Fin N₁) ℝ} {Wb : ℝ → Matrix (Fin N₃) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb) (t : ℝ) :
    HasDerivAt (fun s => Wa s * V)
        ((1 / τ) • ((Uᵀ * Wb t)ᵀ * (S - (Uᵀ * Wb t) * (Wa t * V)))) t ∧
      HasDerivAt (fun s => Uᵀ * Wb s)
        ((1 / τ) • ((S - (Uᵀ * Wb t) * (Wa t * V)) * (Wa t * V)ᵀ)) t := by
  obtain ⟨hWa, hWb⟩ := matrixFlow_of_gradFlow hflow t
  exact wbo_dyn h hWa hWb

end DlnDynamics
