import DlnDynamics.SVDReduction
import DlnDynamics.ModeDynamics

/-!
# SVD existence for the three-layer matrix flow (Phase E)

Layer-3 **Phase E**: *discharge* the SVD hypothesis `IsSVD` that Phase B
(`SVDReduction.lean`) carries as a given. We **construct** a singular value
decomposition `Σ³¹ = U S Vᵀ` of the (square) input–output correlation matrix from
Mathlib's Hermitian spectral theorem, so the downstream chain
(`wbo_dyn_of_gradFlow`, `ModeDynamics`, `ManifoldInvariance`) can be instantiated
without assuming an SVD.

## Scope: square, full-rank

The headline `exists_isSVD_of_isUnit` builds the SVD for **invertible** square
`Sg : Matrix (Fin N) (Fin N) ℝ`. Full rank is exactly what lets us write the left
factor explicitly as `U = Sg V (diagonal σ)⁻¹` — every singular value is positive,
so no orthonormal *completion* of `U` is needed. This is the square shape every
formalized consumer uses (`U V : Matrix (Fin N)(Fin N) ℝ`, `S = diagonal σ`).

The construction, mirroring the numeric check `scripts/check_svd_existence.py`:

* `G := Sgᵀ Sg` is Hermitian positive definite (`posDef_transpose_mul_self_of_isUnit`);
* the spectral theorem gives `G = V (diagonal d) Vᵀ` with `V` orthogonal and
  eigenvalues `d i > 0` (`real_spectral`, `eigenvectorMatrix_orthogonal`);
* `σ i := √(d i) > 0`, and `U := Sg V (diagonal σ)⁻¹` is orthogonal by pure matrix
  algebra: `Uᵀ U = σ⁻¹ Vᵀ (Sgᵀ Sg) V σ⁻¹ = σ⁻¹ D σ⁻¹ = 1`;
* `U (diagonal σ) Vᵀ = Sg V Vᵀ = Sg` (`isSVD_of_spectral`).

**Deferred (E3, general/rank-deficient case).** When `Sg` is singular some `σ i = 0`,
and `U`'s columns for those modes must be completed to an orthonormal basis via
`Orthonormal.exists_orthonormalBasis_extension` (with `Fin N ↔ {σ>0} ↔ complement`
reindexing and a `Matrix ↔ EuclideanSpace` bridge). That is a separate HIGH-risk
milestone and is **not** attempted here; `exists_isSVD_of_isUnit` is the honest,
gap-free full-rank discharge.
-/

namespace DlnDynamics

open Matrix

variable {N : ℕ}

/-! ## The Gram matrix `Sgᵀ Sg` is Hermitian positive (semi)definite -/

/-- `Sgᵀ Sg` is positive semidefinite (real specialization of
`Matrix.posSemidef_conjTranspose_mul_self`). -/
theorem posSemidef_transpose_mul_self (Sg : Matrix (Fin N) (Fin N) ℝ) :
    (Sgᵀ * Sg).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self Sg
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- For invertible `Sg`, the Gram matrix `Sgᵀ Sg` is positive definite. Positive
semidefiniteness plus `det (Sgᵀ Sg) = (det Sg)² ≠ 0` gives positive definiteness via
`PosSemidef.posDef_iff_det_ne_zero`. -/
theorem posDef_transpose_mul_self_of_isUnit (Sg : Matrix (Fin N) (Fin N) ℝ)
    (hSg : IsUnit Sg.det) : (Sgᵀ * Sg).PosDef := by
  rw [(posSemidef_transpose_mul_self Sg).posDef_iff_det_ne_zero, det_mul, det_transpose]
  exact mul_ne_zero hSg.ne_zero hSg.ne_zero

/-! ## Real spectral theorem in plain matrix form -/

/-- The eigenvector matrix of a real Hermitian matrix is orthogonal: `Vᵀ V = 1`.
Real specialization of `Unitary.coe_star_mul_self` (`star = ᵀ` over `ℝ`). -/
theorem eigenvectorMatrix_orthogonal {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) = 1 := by
  have h := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- **Real spectral theorem**, plain matrix form: a real Hermitian `A` factors as
`A = V (diagonal eigenvalues) Vᵀ` with `V := eigenvectorUnitary` orthogonal.
Unfolds Mathlib's `conjStarAlgAut`/`star`/`RCLike.ofReal` form to `*` and `ᵀ`. -/
theorem real_spectral {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) :
    A = (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * diagonal hA.eigenvalues *
      (↑hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)ᵀ := by
  have hof : (RCLike.ofReal ∘ hA.eigenvalues : Fin N → ℝ) = hA.eigenvalues := by funext i; simp
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hof, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

/-! ## SVD from a positive spectral decomposition of the Gram matrix -/

/-- **SVD from a positive spectral decomposition.** Given orthogonal `V`
(`Vᵀ V = 1`, `V Vᵀ = 1`), a strictly positive spectrum `d`, and
`Sgᵀ Sg = V (diagonal d) Vᵀ`, the left factor `U := Sg V (diagonal σ)⁻¹`
(with `σ i = √(d i)`, written as the pointwise-inverse diagonal) yields an SVD
`Sg = U (diagonal σ) Vᵀ`. The two nontrivial fields are pure matrix-cancellation
algebra (`Vᵀ V = 1`, `V Vᵀ = 1`, and the scalar `σ⁻¹ d σ⁻¹ = 1`). -/
theorem isSVD_of_spectral (Sg V : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ)
    (hVtV : Vᵀ * V = 1) (hVVt : V * Vᵀ = 1) (hgram : Sgᵀ * Sg = V * diagonal d * Vᵀ)
    (hd : ∀ i, 0 < d i) :
    IsSVD Sg (Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹))
      (diagonal (fun i => Real.sqrt (d i))) V := by
  have hne : ∀ i, Real.sqrt (d i) ≠ 0 := fun i => (Real.sqrt_pos.mpr (hd i)).ne'
  have hsq : ∀ i, Real.sqrt (d i) * Real.sqrt (d i) = d i :=
    fun i => Real.mul_self_sqrt (hd i).le
  -- the diagonal scalar `σ⁻¹ d σ⁻¹ = 1`
  have hscal : ∀ i, (Real.sqrt (d i))⁻¹ * d i * (Real.sqrt (d i))⁻¹ = 1 := by
    intro i
    have h1 : (Real.sqrt (d i))⁻¹ * (Real.sqrt (d i))⁻¹ = (d i)⁻¹ := by rw [← mul_inv, hsq i]
    rw [mul_right_comm, h1, inv_mul_cancel₀ (hd i).ne']
  -- `(diagonal σ)⁻¹ (diagonal σ) = 1`
  have hcollapse : diagonal (fun i => (Real.sqrt (d i))⁻¹) * diagonal (fun i => Real.sqrt (d i)) = 1 := by
    rw [diagonal_mul_diagonal,
      show (fun i => (Real.sqrt (d i))⁻¹ * Real.sqrt (d i)) = (fun _ : Fin N => (1 : ℝ)) from by
        funext i; exact inv_mul_cancel₀ (hne i)]
    simp [diagonal_one]
  refine { hU := ?_, hV := hVtV, hfact := ?_ }
  · -- `Uᵀ U = σ⁻¹ Vᵀ (Sgᵀ Sg) V σ⁻¹ = σ⁻¹ (Vᵀ V) D (Vᵀ V) σ⁻¹ = σ⁻¹ D σ⁻¹ = 1`
    show (Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹))ᵀ *
      (Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹)) = 1
    rw [show (Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹))ᵀ *
            (Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹))
          = diagonal (fun i => (Real.sqrt (d i))⁻¹) * Vᵀ * (Sgᵀ * Sg) *
            (V * diagonal (fun i => (Real.sqrt (d i))⁻¹)) from by
        simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc], hgram]
    rw [show diagonal (fun i => (Real.sqrt (d i))⁻¹) * Vᵀ * (V * diagonal d * Vᵀ) *
            (V * diagonal (fun i => (Real.sqrt (d i))⁻¹))
          = diagonal (fun i => (Real.sqrt (d i))⁻¹) * (Vᵀ * V) * diagonal d * (Vᵀ * V) *
            diagonal (fun i => (Real.sqrt (d i))⁻¹) from by
        simp only [Matrix.mul_assoc], hVtV]
    simp only [Matrix.mul_one, diagonal_mul_diagonal]
    rw [show (fun i => (Real.sqrt (d i))⁻¹ * d i * (Real.sqrt (d i))⁻¹) = (fun _ : Fin N => (1 : ℝ))
          from by funext i; exact hscal i]
    simp [diagonal_one]
  · -- `U (diagonal σ) Vᵀ = Sg V (σ⁻¹ σ) Vᵀ = Sg (V Vᵀ) = Sg`
    show Sg = Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹) *
      diagonal (fun i => Real.sqrt (d i)) * Vᵀ
    rw [show Sg * V * diagonal (fun i => (Real.sqrt (d i))⁻¹) *
            diagonal (fun i => Real.sqrt (d i)) * Vᵀ
          = Sg * V * (diagonal (fun i => (Real.sqrt (d i))⁻¹) *
            diagonal (fun i => Real.sqrt (d i))) * Vᵀ from by simp only [Matrix.mul_assoc],
        hcollapse, Matrix.mul_one,
        show Sg * V * Vᵀ = Sg * (V * Vᵀ) from by simp only [Matrix.mul_assoc], hVVt, Matrix.mul_one]

/-! ## The headline: SVD existence for invertible square `Sg` -/

/-- **SVD existence (square, full-rank).** Every invertible square real matrix `Sg`
admits a singular value decomposition `Sg = U (diagonal σ) Vᵀ` with `U`, `V`
orthogonal — i.e. the `IsSVD` hypothesis of Phase B is *discharged* for full-rank
`Sg`. Constructed from the spectral theorem on `Sgᵀ Sg` (positive definite). -/
theorem exists_isSVD_of_isUnit (Sg : Matrix (Fin N) (Fin N) ℝ) (hSg : IsUnit Sg.det) :
    ∃ (U V : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ), IsSVD Sg U (diagonal σ) V := by
  have hpd := posDef_transpose_mul_self_of_isUnit Sg hSg
  have hH := hpd.isHermitian
  set V : Matrix (Fin N) (Fin N) ℝ := (↑hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) with hVdef
  refine ⟨Sg * V * diagonal (fun i => (Real.sqrt (hH.eigenvalues i))⁻¹),
    V, fun i => Real.sqrt (hH.eigenvalues i), ?_⟩
  have hVtV : Vᵀ * V = 1 := eigenvectorMatrix_orthogonal hH
  exact isSVD_of_spectral Sg V hH.eigenvalues hVtV
    ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hVtV)
    (real_spectral hH) (fun i => hpd.eigenvalues_pos i)

/-! ## End-to-end: the SVD hypothesis discharged on the full-rank regime -/

/-- **Mode dynamics from gradient descent, with no SVD assumed (Saxe Eq. `a_dyn`/`b_dyn`).**
For an *invertible* square correlation matrix `Sg`, per-entry gradient descent on the
network loss obeys the decoupled mode dynamics `a_dyn`/`b_dyn` in *some* SVD coordinate
frame. This composes Phase E (`exists_isSVD_of_isUnit`) with the Phase B–C chain
(`a_dyn_of_gradFlow`/`b_dyn_of_gradFlow`), *discharging* the `IsSVD` hypothesis those
results carried — the honest end-to-end statement on the full-rank regime. -/
theorem exists_mode_dynamics_of_gradFlow_of_isUnit {N₂ : ℕ}
    (Sg : Matrix (Fin N) (Fin N) ℝ) (hSg : IsUnit Sg.det)
    {τ : ℝ} {Wa : ℝ → Matrix (Fin N₂) (Fin N) ℝ} {Wb : ℝ → Matrix (Fin N) (Fin N₂) ℝ}
    (hflow : IsMatrixGradFlow τ Sg Wa Wb) :
    ∃ (U V : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ), IsSVD Sg U (diagonal σ) V ∧
      (∀ t α, HasDerivAt (fun s => aMode (Wa s * V) α)
        ((1 / τ) • ((σ α - bMode (Uᵀ * Wb t) α ⬝ᵥ aMode (Wa t * V) α) • bMode (Uᵀ * Wb t) α
          - ∑ γ ∈ Finset.univ.erase α,
              (bMode (Uᵀ * Wb t) γ ⬝ᵥ aMode (Wa t * V) α) • bMode (Uᵀ * Wb t) γ)) t) ∧
      (∀ t α, HasDerivAt (fun s => bMode (Uᵀ * Wb s) α)
        ((1 / τ) • ((σ α - aMode (Wa t * V) α ⬝ᵥ bMode (Uᵀ * Wb t) α) • aMode (Wa t * V) α
          - ∑ γ ∈ Finset.univ.erase α,
              (aMode (Wa t * V) γ ⬝ᵥ bMode (Uᵀ * Wb t) α) • aMode (Wa t * V) γ)) t) := by
  obtain ⟨U, V, σ, hsvd⟩ := exists_isSVD_of_isUnit Sg hSg
  exact ⟨U, V, σ, hsvd,
    fun t α => a_dyn_of_gradFlow rfl hsvd hflow t α,
    fun t α => b_dyn_of_gradFlow rfl hsvd hflow t α⟩

end DlnDynamics
