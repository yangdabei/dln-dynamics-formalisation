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

## Scope: every square real matrix

`exists_isSVD`: **any** square real `Sg : Matrix (Fin N) (Fin N) ℝ` admits an SVD
`Sg = U (diagonal σ) Vᵀ` with `U`,`V` orthogonal — the `IsSVD` hypothesis is fully
discharged (no invertibility needed). This is the square shape every formalized
consumer uses (`U V : Matrix (Fin N)(Fin N) ℝ`, `S = diagonal σ`).

Two constructions of the right factor share the same spectral start
(`G := Sgᵀ Sg` Hermitian PSD; `G = V (diagonal d) Vᵀ` with `V` orthogonal,
eigenvalues `d i ≥ 0`; `σ i := √(d i)`):

* **Full rank** (`exists_isSVD_of_isUnit`, explicit). For invertible `Sg` every
  `σ i > 0`, so the left factor is the *explicit* `U := Sg V (diagonal σ)⁻¹`,
  orthogonal by pure matrix algebra `Uᵀ U = σ⁻¹ (Vᵀ V) D (Vᵀ V) σ⁻¹ = 1`
  (`isSVD_of_spectral`).
* **General** (`exists_isSVD`, via `column_completion`). With `A := Sg V` one has
  `Aᵀ A = diagonal (σ²)`, so the columns of `A` at the `σ i > 0` modes, normalized,
  are orthonormal; `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` completes
  them to an orthonormal basis indexed by `Fin N` (no manual reindexing), whose matrix
  `U` satisfies `U (diagonal σ) = A`, hence `Sg = U (diagonal σ) Vᵀ`. Columns at the
  `σ i = 0` modes are the free completion (`A`'s column there is `0`).

Numeric check: `scripts/check_svd_existence.py` (stdlib + Jacobi), full-rank and singular.
-/

namespace DlnDynamics

open Matrix
open scoped RealInnerProductSpace

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

/-! ## General case: orthonormal completion of the left factor -/

/-- **Column completion.** If the columns of `A` have Gram matrix `Aᵀ A = diagonal (σ²)`
(`σ i ≥ 0`), then `A = U (diagonal σ)` for some orthogonal `U`. The `σ i > 0` columns of
`A`, normalized, are orthonormal (their inner products are the off-diagonal Gram entries,
all `0`); `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` completes them to an
orthonormal basis of `EuclideanSpace ℝ (Fin N)` indexed by `Fin N` (agreeing on the
`σ i > 0` modes — no manual reindexing). Its matrix `U` is orthogonal
(`toMatrix_orthonormalBasis_mem_unitary`) and satisfies `U (diagonal σ) = A`: at `σ j > 0`
the `j`-th column is `σ j⁻¹ A·ⱼ`, and at `σ j = 0` both sides vanish (`A·ⱼ = 0`, since its
squared norm is the Gram diagonal entry `σ j² = 0`). This is the heart of the
rank-deficient SVD: the zero-singular-value columns of `U` are the *free* completion. -/
theorem column_completion (A : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hAA : Aᵀ * A = diagonal (fun i => σ i ^ 2)) :
    ∃ U : Matrix (Fin N) (Fin N) ℝ, Uᵀ * U = 1 ∧ U * diagonal σ = A := by
  classical
  -- normalized candidate columns (in Euclidean coordinates), orthonormal on `{σ > 0}`
  have horth : Orthonormal ℝ (Set.restrict {j | 0 < σ j}
      (fun j => (WithLp.equiv 2 (Fin N → ℝ)).symm (fun i => (σ j)⁻¹ * A i j))) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.restrict_apply]
    rw [show (⟪(WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (σ i)⁻¹ * A k i),
              (WithLp.equiv 2 (Fin N → ℝ)).symm (fun k => (σ j)⁻¹ * A k j)⟫)
          = ∑ k, ((σ i)⁻¹ * A k i) * ((σ j)⁻¹ * A k j) from by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]]
    have hsum : ∑ k, ((σ i)⁻¹ * A k i) * ((σ j)⁻¹ * A k j)
        = (σ i)⁻¹ * (σ j)⁻¹ * (Aᵀ * A) i j := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by simp [Matrix.transpose_apply]; ring)
    rw [hsum, hAA, diagonal_apply]
    by_cases h : i = j
    · subst h
      have hne : σ i ≠ 0 := ne_of_gt hi
      have h1 : (if i = i then σ i ^ 2 else (0 : ℝ)) = σ i ^ 2 := if_pos rfl
      have h2 : (if (⟨i, hi⟩ : {j | 0 < σ j}) = ⟨i, hj⟩ then (1 : ℝ) else 0) = 1 := if_pos rfl
      rw [h1, h2]; field_simp
    · rw [if_neg (by simpa [Subtype.ext_iff] using h), if_neg (by simpa using h)]
      simp
  -- extend to a full orthonormal basis of `Fin N`, and read off its matrix
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  refine ⟨(EuclideanSpace.basisFun (Fin N) ℝ).toBasis.toMatrix ⇑b, ?_, ?_⟩
  · -- `Uᵀ U = 1` from unitary membership of a change-of-orthonormal-basis matrix
    have hmem := (EuclideanSpace.basisFun (Fin N) ℝ).toMatrix_orthonormalBasis_mem_unitary b
    rw [Matrix.mem_unitaryGroup_iff'] at hmem
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hmem
  · -- `U (diagonal σ) = A`, column by column
    ext i j
    rw [Matrix.mul_diagonal,
      show ((EuclideanSpace.basisFun (Fin N) ℝ).toBasis.toMatrix ⇑b) i j = (b j) i from rfl]
    by_cases h : 0 < σ j
    · rw [hb j h, show ((WithLp.equiv 2 (Fin N → ℝ)).symm
            (fun i => (σ j)⁻¹ * A i j)) i = (σ j)⁻¹ * A i j from rfl]
      field_simp [ne_of_gt h]
    · -- `σ j = 0` ⇒ column `j` of `A` is zero
      have hσj : σ j = 0 := le_antisymm (not_lt.mp h) (hσ j)
      rw [hσj, mul_zero]
      have hdiagjj : (Aᵀ * A) j j = 0 := by simp [hAA, hσj]
      have hsumsq : ∑ k, A k j * A k j = 0 := by
        rw [← hdiagjj, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.transpose_apply])
      have hnn : ∀ k ∈ (Finset.univ : Finset (Fin N)), 0 ≤ A k j * A k j :=
        fun k _ => mul_self_nonneg _
      exact (mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsumsq i
        (Finset.mem_univ i))).symm

/-- **SVD existence (any square real matrix).** Every square real `Sg` admits a singular
value decomposition `Sg = U (diagonal σ) Vᵀ` with `U`,`V` orthogonal — the `IsSVD`
hypothesis of Phase B is *discharged unconditionally*. With `V` the eigenvector matrix of
`Sgᵀ Sg` and `σ i = √(eigenvalue i)`, the right factor `A := Sg V` has `Aᵀ A = diagonal (σ²)`,
so `column_completion` produces an orthogonal `U` with `U (diagonal σ) = Sg V`, whence
`Sg = U (diagonal σ) Vᵀ`. Generalizes `exists_isSVD_of_isUnit` to the rank-deficient case. -/
theorem exists_isSVD (Sg : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (U V : Matrix (Fin N) (Fin N) ℝ) (σ : Fin N → ℝ), IsSVD Sg U (diagonal σ) V := by
  have hpsd := posSemidef_transpose_mul_self Sg
  have hH := hpsd.isHermitian
  set V : Matrix (Fin N) (Fin N) ℝ := (↑hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) with hVdef
  have hVtV : Vᵀ * V = 1 := eigenvectorMatrix_orthogonal hH
  have hVVt : V * Vᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hVtV
  have hgram : Sgᵀ * Sg = V * diagonal hH.eigenvalues * Vᵀ := real_spectral hH
  have hd : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hpsd.eigenvalues_nonneg i
  have hσsq : (fun i => Real.sqrt (hH.eigenvalues i) ^ 2) = hH.eigenvalues := by
    funext i; exact Real.sq_sqrt (hd i)
  -- `(Sg V)ᵀ (Sg V) = Vᵀ (Sgᵀ Sg) V = (Vᵀ V) D (Vᵀ V) = diagonal (σ²)`
  have hAA : (Sg * V)ᵀ * (Sg * V) = diagonal (fun i => Real.sqrt (hH.eigenvalues i) ^ 2) := by
    rw [hσsq, Matrix.transpose_mul,
      show Vᵀ * Sgᵀ * (Sg * V) = Vᵀ * (Sgᵀ * Sg) * V from by simp only [Matrix.mul_assoc]]
    conv_lhs => rw [hgram]
    rw [show Vᵀ * (V * diagonal hH.eigenvalues * Vᵀ) * V
          = (Vᵀ * V) * diagonal hH.eigenvalues * (Vᵀ * V) from by simp only [Matrix.mul_assoc]]
    simp only [hVtV, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨U, hUU, hUd⟩ :=
    column_completion (Sg * V) (fun i => Real.sqrt (hH.eigenvalues i)) (fun _ => Real.sqrt_nonneg _) hAA
  refine ⟨U, V, fun i => Real.sqrt (hH.eigenvalues i), { hU := hUU, hV := hVtV, hfact := ?_ }⟩
  rw [hUd, Matrix.mul_assoc, hVVt, Matrix.mul_one]

/-! ## End-to-end: the SVD hypothesis discharged -/

/-- **Mode dynamics from gradient descent, with no SVD assumed (Saxe Eq. `a_dyn`/`b_dyn`).**
For *any* square correlation matrix `Sg`, per-entry gradient descent on the network loss
obeys the decoupled mode dynamics `a_dyn`/`b_dyn` in *some* SVD coordinate frame. This
composes Phase E (`exists_isSVD`) with the Phase B–C chain
(`a_dyn_of_gradFlow`/`b_dyn_of_gradFlow`), *discharging* the `IsSVD` hypothesis those
results carried — the honest, unconditional end-to-end statement. -/
theorem exists_mode_dynamics_of_gradFlow {N₂ : ℕ}
    (Sg : Matrix (Fin N) (Fin N) ℝ)
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
  obtain ⟨U, V, σ, hsvd⟩ := exists_isSVD Sg
  exact ⟨U, V, σ, hsvd,
    fun t α => a_dyn_of_gradFlow rfl hsvd hflow t α,
    fun t α => b_dyn_of_gradFlow rfl hsvd hflow t α⟩

end DlnDynamics
