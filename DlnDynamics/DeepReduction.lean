import DlnDynamics.DeepMatrixFlow
import DlnDynamics.DeepDynamics

/-!
# Depth-`N` reduction: change of variables + mode extraction (Phases B–C)

Connects the `N_l`-layer matrix flow `multilayer_dyn` (`DeepMatrixFlow.lean`, Phase A)
to the scalar `IsDeepFlow` (`DeepDynamics.lean`). Under the decoupling initial
conditions — orthogonal frames `Rₗ` with `R₀ = V`, `R_m = U` an SVD `Σ³¹ = U S Vᵀ`,
and each weight matrix diagonal in those frames, `Wₗ(t) = R₍ₗ₊₁₎ diag(aₗ(t)) Rₗᵀ` —
the products telescope (`prodDesc_telescope`), and `multilayer_dyn` decouples into one
copy of `IsDeepFlow` per mode `α`, with mode strength `s = σ α`.

Per the project's staging (cf. `InvariantManifold.lean`), the diagonal-in-frame form
is taken as a hypothesis for all `t`; its forward-invariance in time is a separate
ODE-uniqueness statement (deferred).
-/

namespace DlnDynamics

open Matrix

variable {n m : ℕ}

/-- Product of diagonal matrices is the diagonal of the entrywise products. -/
lemma prodDesc_diagonal (d : Fin m → Fin n → ℝ) :
    prodDesc (fun i => diagonal (d i)) = diagonal (fun α => ∏ i, d i α) := by
  induction m with
  | zero => simp [prodDesc_zero]
  | succ k ih =>
    rw [prodDesc_succ, ih (fun i => d i.castSucc), Matrix.diagonal_mul_diagonal]
    congr 1
    funext α
    rw [Fin.prod_univ_castSucc]
    simp [mul_comm]

/-- `belowProd` recursion: `∏_{i<l+1} = Wₗ · ∏_{i<l}` (peel the new bottom factor). -/
lemma belowProd_succ {k : ℕ} (W : Fin (k + 1) → Matrix (Fin n) (Fin n) ℝ) (i : Fin k) :
    belowProd W i.succ = W i.castSucc * belowProd W i.castSucc := by
  unfold belowProd
  have hi := i.isLt
  have h1 : (k + 1) - (i.succ : ℕ) = k - (i : ℕ) := by rw [Fin.val_succ]; omega
  have h2 : (k + 1) - (i.castSucc : ℕ) = k - (i : ℕ) + 1 := by rw [Fin.val_castSucc]; omega
  have hlt : k - (i : ℕ) < ((List.ofFn W).reverse).length := by simp
  rw [h1, h2, ← List.cons_getElem_drop_succ (h := hlt), List.prod_cons]
  congr 1
  rw [List.getElem_reverse, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [List.length_ofFn, Fin.val_castSucc]
  omega

/-- `belowProd W l = 1` at the bottom layer (`l = 0`, no layers below). -/
lemma belowProd_zero {m : ℕ} (W : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) :
    belowProd W 0 = 1 := by
  unfold belowProd
  simp only [Fin.val_zero, Nat.sub_zero]
  rw [List.drop_eq_nil_of_le (by simp), List.prod_nil]

/-- `Iio (i+1) = insert i (Iio i)` for `Fin`. -/
private lemma Iio_succ_eq {m : ℕ} (i : Fin m) :
    Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
  ext x
  simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff, Fin.val_succ,
    Fin.val_castSucc]
  omega

/-- **Sub-range telescoping, below.** Under the diagonal change of variables, the
prefix product `∏_{i<l} Wᵢ` telescopes to `Rₗ · diag(∏_{i<l} aᵢ) · R₀ᵀ`. -/
lemma belowProd_factored {m : ℕ} (R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin m → Fin n → ℝ) (hR : ∀ j, (R j)ᵀ * R j = 1) (l : Fin m) :
    belowProd (fun i => R i.succ * diagonal (a i) * (R i.castSucc)ᵀ) l
      = R l.castSucc * diagonal (fun α => ∏ i ∈ Finset.Iio l, a i α) * (R 0)ᵀ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := l.isLt; omega⟩
  induction l using Fin.induction with
  | zero =>
    rw [belowProd_zero]
    have hIio0 : Finset.Iio (0 : Fin (k + 1)) = ∅ := by
      ext x
      simp only [Finset.mem_Iio, Finset.notMem_empty, iff_false, not_lt]
      exact Fin.zero_le x
    rw [hIio0]
    simp only [Finset.prod_empty, Fin.castSucc_zero', Matrix.diagonal_one, Matrix.mul_one]
    exact ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hR 0)).symm
  | succ i ih =>
    rw [belowProd_succ, ih]
    have hC : (R (i.castSucc).castSucc)ᵀ * R (i.castSucc).castSucc = 1 := hR _
    have hdiag : diagonal (fun α => ∏ j ∈ Finset.Iio i.succ, a j α)
        = diagonal (a i.castSucc) * diagonal (fun α => ∏ j ∈ Finset.Iio i.castSucc, a j α) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext α
      rw [Iio_succ_eq, Finset.prod_insert (by simp)]
    rw [show (i.castSucc).succ = (i.succ).castSucc from (Fin.castSucc_succ i).symm, hdiag]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R (i.castSucc).castSucc)ᵀ (R (i.castSucc).castSucc), hC,
      Matrix.one_mul]

/-- `aboveProd` recursion: `∏_{i>l} = ∏_{i>l+1} · W_{l+1}` (peel the new top factor). -/
lemma aboveProd_succ {k : ℕ} (W : Fin (k + 1) → Matrix (Fin n) (Fin n) ℝ) (i : Fin k) :
    aboveProd W i.castSucc = aboveProd W i.succ * W i.succ := by
  unfold aboveProd
  have hi := i.isLt
  have h1 : (k + 1) - 1 - (i.castSucc : ℕ) = (k - 1 - (i : ℕ)) + 1 := by rw [Fin.val_castSucc]; omega
  have h2 : (k + 1) - 1 - (i.succ : ℕ) = k - 1 - (i : ℕ) := by rw [Fin.val_succ]; omega
  have hlt : k - 1 - (i : ℕ) < ((List.ofFn W).reverse).length := by simp; omega
  rw [h1, h2, List.prod_take_succ _ _ hlt]
  congr 1
  rw [List.getElem_reverse, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp only [List.length_ofFn, Fin.val_succ]
  omega

/-- `Ioi i = insert (i+1) (Ioi (i+1))` for `Fin`. -/
private lemma Ioi_castSucc_eq {m : ℕ} (i : Fin m) :
    Finset.Ioi i.castSucc = insert i.succ (Finset.Ioi i.succ) := by
  ext x
  simp only [Finset.mem_Ioi, Finset.mem_insert, Fin.lt_def, Fin.ext_iff, Fin.val_succ,
    Fin.val_castSucc]
  omega

/-- **Sub-range telescoping, above.** Under the diagonal change of variables, the
suffix product `∏_{i>l} Wᵢ` telescopes to `R_m · diag(∏_{i>l} aᵢ) · R₍ₗ₊₁₎ᵀ`. -/
lemma aboveProd_factored {m : ℕ} (R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin m → Fin n → ℝ) (hR : ∀ j, (R j)ᵀ * R j = 1) (l : Fin m) :
    aboveProd (fun i => R i.succ * diagonal (a i) * (R i.castSucc)ᵀ) l
      = R (Fin.last m) * diagonal (fun α => ∏ i ∈ Finset.Ioi l, a i α) * (R l.succ)ᵀ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by have := l.isLt; omega⟩
  induction l using Fin.reverseInduction with
  | last =>
    have habz : aboveProd (fun i => R i.succ * diagonal (a i) * (R i.castSucc)ᵀ) (Fin.last k) = 1 := by
      unfold aboveProd
      rw [show (k + 1) - 1 - ((Fin.last k : Fin (k + 1)) : ℕ) = 0 from by simp [Fin.val_last]]
      simp
    rw [habz]
    have hIoiLast : Finset.Ioi (Fin.last k) = ∅ := by
      ext x
      simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, not_lt]
      exact Fin.le_last x
    rw [hIoiLast]
    simp only [Finset.prod_empty, Matrix.diagonal_one, Matrix.mul_one]
    rw [show (Fin.last k).succ = Fin.last (k + 1) from Fin.succ_last k]
    exact ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hR _)).symm
  | cast i ih =>
    rw [aboveProd_succ, ih]
    have hD : (R (i.succ).succ)ᵀ * R (i.succ).succ = 1 := hR _
    have hdiag : diagonal (fun α => ∏ j ∈ Finset.Ioi i.castSucc, a j α)
        = diagonal (fun α => ∏ j ∈ Finset.Ioi i.succ, a j α) * diagonal (a i.succ) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext α
      rw [Ioi_castSucc_eq, Finset.prod_insert (by simp), mul_comm]
    rw [Fin.castSucc_succ i, hdiag]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R (i.succ).succ)ᵀ (R (i.succ).succ), hD, Matrix.one_mul]

/-- **Full-product telescoping** under the diagonal change of variables:
`∏ᵢ Wᵢ = R_m · diag(∏ᵢ aᵢ) · R₀ᵀ` (combine `prodDesc_telescope` with `prodDesc_diagonal`). -/
lemma prodDesc_factored {m : ℕ} (R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (a : Fin m → Fin n → ℝ) (hR : ∀ j, (R j)ᵀ * R j = 1) :
    prodDesc (fun i => R i.succ * diagonal (a i) * (R i.castSucc)ᵀ)
      = R (Fin.last m) * diagonal (fun α => ∏ i, a i α) * (R 0)ᵀ := by
  rw [prodDesc_telescope R (fun i => diagonal (a i)) hR, prodDesc_diagonal]

/-- Derivative extraction: differentiate a fixed `(p,q)` entry of `A · M(t) · B`
through the constant factors `A`, `B`. -/
lemma hasDerivAt_conj_apply {M : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {M' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (h : HasDerivAt M M' t)
    (A B : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) :
    HasDerivAt (fun s => (A * M s * B) p q) ((A * M' * B) p q) t := by
  have hexp : ∀ (N : Matrix (Fin n) (Fin n) ℝ),
      (A * N * B) p q = ∑ y, ∑ x, A p x * N x y * B y q := fun N => by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
  have hfeq : (fun s => ∑ y, ∑ x, A p x * (M s) x y * B y q)
      = (∑ y, ∑ x, fun s => A p x * (M s) x y * B y q) := by
    funext s; simp only [Finset.sum_apply]
  rw [show (fun s => (A * M s * B) p q) = (fun s => ∑ y, ∑ x, A p x * (M s) x y * B y q) from
      funext fun s => hexp (M s), hexp M', hfeq]
  exact HasDerivAt.sum (fun y (_ : y ∈ Finset.univ) =>
    HasDerivAt.sum (fun x (_ : x ∈ Finset.univ) =>
      ((hasDerivAt_pi.1 (hasDerivAt_pi.1 h x) y).const_mul (A p x)).mul_const (B y q)))

/-- `∏_{i≠l} = (∏_{i<l})·(∏_{i>l})`: the erased product splits at `l`. -/
lemma prod_erase_split {m : ℕ} (f : Fin m → ℝ) (l : Fin m) :
    ∏ i ∈ Finset.univ.erase l, f i = (∏ i ∈ Finset.Iio l, f i) * (∏ i ∈ Finset.Ioi l, f i) := by
  rw [show Finset.univ.erase l = Finset.Iio l ∪ Finset.Ioi l from by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
        Finset.mem_univ, and_true]
      exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim (fun hlt => hlt.ne) (fun hgt => hgt.ne')⟩,
    Finset.prod_union (by
      simp only [Finset.disjoint_left, Finset.mem_Iio, Finset.mem_Ioi]
      exact fun x hx hx' => absurd hx (not_lt.mpr hx'.le))]

/-- **Mode decoupling (orthogonal cancellation).** Conjugating the matrix-flow
velocity by the layer's frames collapses it, via `prodDesc/aboveProd/belowProd`
telescoping and the orthogonality of `R`, to a *diagonal* matrix whose `α`-th entry
is the scalar deep-flow velocity of mode `α`. -/
lemma flowval_conj {R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ} (hR : ∀ j, (R j)ᵀ * R j = 1)
    (σ : Fin n → ℝ) (b : Fin m → Fin n → ℝ) (l : Fin m) :
    (R l.succ)ᵀ * ((aboveProd (fun i => R i.succ * diagonal (b i) * (R i.castSucc)ᵀ) l)ᵀ *
        (R (Fin.last m) * diagonal σ * (R 0)ᵀ -
          prodDesc (fun i => R i.succ * diagonal (b i) * (R i.castSucc)ᵀ)) *
        (belowProd (fun i => R i.succ * diagonal (b i) * (R i.castSucc)ᵀ) l)ᵀ) * R l.castSucc
      = diagonal (fun α => (∏ i ∈ Finset.Ioi l, b i α) * (σ α - ∏ i, b i α) *
          (∏ i ∈ Finset.Iio l, b i α)) := by
  rw [aboveProd_factored R b hR l, belowProd_factored R b hR l, prodDesc_factored R b hR]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  rw [show R (Fin.last m) * diagonal σ * (R 0)ᵀ
          - R (Fin.last m) * diagonal (fun α => ∏ i, b i α) * (R 0)ᵀ
        = R (Fin.last m) * diagonal (fun α => σ α - ∏ i, b i α) * (R 0)ᵀ from by
      rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (R l.succ)ᵀ (R l.succ), hR l.succ, Matrix.one_mul,
    ← Matrix.mul_assoc (R (Fin.last m))ᵀ (R (Fin.last m)), hR (Fin.last m), Matrix.one_mul,
    ← Matrix.mul_assoc (R 0)ᵀ (R 0), hR 0, Matrix.one_mul,
    hR l.castSucc, Matrix.mul_one,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext α
  ring

/-- **Depth-`N` reduction (Phases B–C), end to end.** Network gradient descent on the
deep loss (`IsDeepMatrixGradFlow`), under the decoupling change of variables
`Wₗ(t) = R₍ₗ₊₁₎ diag(aₗ(t)) Rₗᵀ` with orthogonal frames `Rₗ` and an SVD
`Σ³¹ = R_m diag(σ) R₀ᵀ`, reduces — mode by mode — to the scalar deep flow
`IsDeepFlow` of `DeepDynamics.lean`: for each mode `α`, the layer mode-strengths
`aₗ(·) α` obey `τ ȧ = (s − ∏ aᵢ)·∏_{i≠l} aᵢ` with `s = σ α`. Composing with `deep_dyn`
gives the depth-`N` law on the symmetric submanifold from the matrix dynamics. -/
theorem isDeepFlow_of_gradFlow {τ : ℝ} {R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ}
    (hR : ∀ j, (R j)ᵀ * R j = 1) {σ : Fin n → ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S = R (Fin.last m) * diagonal σ * (R 0)ᵀ)
    {a : Fin m → ℝ → Fin n → ℝ} {W : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ l t, W l t = R l.succ * diagonal (a l t) * (R l.castSucc)ᵀ)
    (hgrad : IsDeepMatrixGradFlow τ S W) (α : Fin n) :
    IsDeepFlow (σ α) τ (fun l t => a l t α) where
  ha := fun l t => by
    have hWfun : (fun i => W i t) = (fun i => R i.succ * diagonal (a i t) * (R i.castSucc)ᵀ) :=
      funext (fun i => hW i t)
    have hextract : ∀ s, ((R l.succ)ᵀ * W l s * R l.castSucc) α α = a l s α := by
      intro s
      rw [hW l s, show (R l.succ)ᵀ * (R l.succ * diagonal (a l s) * (R l.castSucc)ᵀ) * R l.castSucc
            = diagonal (a l s) from by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (R l.succ)ᵀ (R l.succ), hR l.succ, Matrix.one_mul, hR l.castSucc,
            Matrix.mul_one], Matrix.diagonal_apply_eq]
    have hderiv := hasDerivAt_conj_apply (multilayerFlow_of_gradFlow hgrad l t)
      ((R l.succ)ᵀ) (R l.castSucc) α α
    rw [show (fun s => ((R l.succ)ᵀ * W l s * R l.castSucc) α α) = (fun t => a l t α) from
        funext hextract] at hderiv
    rw [show (((R l.succ)ᵀ * ((1 / τ) • ((aboveProd (fun i => W i t) l)ᵀ *
            (S - prodDesc (fun i => W i t)) * (belowProd (fun i => W i t) l)ᵀ)) * R l.castSucc) α α)
          = (σ α - ∏ i, a i t α) * (∏ i ∈ Finset.univ.erase l, a i t α) / τ from by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hWfun, hS,
          flowval_conj hR σ (fun i => a i t) l, Matrix.diagonal_apply_eq,
          prod_erase_split (fun i => a i t α) l]
        ring] at hderiv
    exact hderiv

/-- **End-to-end depth-`N` law from the matrix dynamics.** Composing the reduction
`isDeepFlow_of_gradFlow` with `deep_dyn_of_deepFlow`: `N_l`-layer gradient descent in
the decoupling frames, restricted to a mode `α` whose layer strengths coincide
(`aₗ(t) α = c(t)`, the symmetric submanifold) and stay positive, makes the overall
mode strength `u = cᵐ` obey Saxe Eq. `deep_dyn`
`τ u' = (N_l−1) u^{2−2/(N_l−1)}(σ_α − u)`. -/
theorem deep_dyn_of_gradFlow {τ : ℝ} (hm : 1 ≤ m)
    {R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ} (hR : ∀ j, (R j)ᵀ * R j = 1) {σ : Fin n → ℝ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S = R (Fin.last m) * diagonal σ * (R 0)ᵀ)
    {a : Fin m → ℝ → Fin n → ℝ} {W : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ l t, W l t = R l.succ * diagonal (a l t) * (R l.castSucc)ᵀ)
    (hgrad : IsDeepMatrixGradFlow τ S W) (α : Fin n) {c : ℝ → ℝ}
    (hsym : ∀ l t, a l t α = c t) (hpos : ∀ t, 0 < c t) (t : ℝ) :
    HasDerivAt (fun r => c r ^ m)
      ((m : ℝ) * (c t ^ m) ^ (2 - 2 / (m : ℝ)) * (σ α - c t ^ m) / τ) t :=
  deep_dyn_of_deepFlow hm (isDeepFlow_of_gradFlow hR hS hW hgrad α) hsym hpos t

end DlnDynamics
