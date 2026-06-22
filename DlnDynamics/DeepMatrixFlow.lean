import DlnDynamics.Basic

/-!
# Matrix gradient flow of the deep (`N_l`-layer) linear network (depth-`N` Phase A)

The depth-`N` analog of `MatrixFlow.lean`. A linear network with `N_l` layers has
`m = N_l − 1` weight matrices `W₀,…,W_{m-1}` (here all square `n×n`). With whitened
inputs (`Σ¹¹ = I`) the population square loss is

`E(W) = ½ ‖Σ³¹ − W_{m-1} ⋯ W₀‖²_F`,

the product taken in descending order (`prodDesc`). This module derives Saxe
Eq. `multilayer_dyn` — the matrix gradient flow

`τ Ẇₗ = (∏_{i>l} Wᵢ)ᵀ (Σ³¹ − ∏ᵢ Wᵢ) (∏_{i<l} Wᵢ)ᵀ`

— from per-entry gradient descent on `E`. The two prefix/suffix products are
`aboveProd` (`∏_{i>l} Wᵢ`) and `belowProd` (`∏_{i<l} Wᵢ`); the key structural fact
is the **product split** `prodDesc (update W l V) = aboveProd W l · V · belowProd W l`,
which makes the loss affine in the perturbation of one layer, so the 3-layer
entry-derivative technique (directional derivative along `Matrix.single k j 1`,
squared-affine) applies through the unified bilinear lemma
`hasDerivAt_loss_layer`: `∂/∂X ½‖S − A X B‖² = −Aᵀ(S − A X B)Bᵀ`.

This is depth-`N` **Phase A**. Phases B–C (the `Rₗ` change of variables decoupling
the modes, reducing to the scalar `IsDeepFlow` of `DeepDynamics.lean`) build on it.
-/

namespace DlnDynamics

open Matrix

variable {n m : ℕ}

/-- Descending ordered product `W_{m-1} · W_{m-2} · … · W₀` of a family of square
matrices indexed by layers `Fin m`. (Matrix `*` is non-commutative, so this is a
`List.prod`, not a `Finset.prod`.) -/
def prodDesc (W : Fin m → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (List.ofFn W).reverse.prod

@[simp] lemma prodDesc_zero (W : Fin 0 → Matrix (Fin n) (Fin n) ℝ) : prodDesc W = 1 := by
  simp [prodDesc]

/-- Peel the top layer: `prodDesc W = W_{m} · prodDesc (W ∘ castSucc)`. -/
lemma prodDesc_succ {m : ℕ} (W : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) :
    prodDesc W = W (Fin.last m) * prodDesc (fun i : Fin m => W i.castSucc) := by
  simp only [prodDesc, List.ofFn_succ', List.concat_eq_append, List.reverse_concat',
    List.prod_cons]

/-- **Telescoping conjugation** (the change-of-variables core for Phase B).
Conjugating each factor `W̄ᵢ` by `R₍ᵢ₊₁₎ · _ · Rᵢᵀ` and taking the descending
product cancels every interior orthogonal `R`, leaving only the end caps:
`∏ (R₍ᵢ₊₁₎ W̄ᵢ Rᵢᵀ) = R_{m} · (∏ W̄ᵢ) · R₀ᵀ`. With `R₀ = V`, `R_m = U` and an SVD
`Σ³¹ = U S Vᵀ` this is what decouples the deep modes. -/
lemma prodDesc_telescope {m : ℕ} (R : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Wb : Fin m → Matrix (Fin n) (Fin n) ℝ) (hR : ∀ j, (R j)ᵀ * R j = 1) :
    prodDesc (fun i : Fin m => R i.succ * Wb i * (R i.castSucc)ᵀ)
      = R (Fin.last m) * prodDesc Wb * (R 0)ᵀ := by
  induction m with
  | zero =>
    simp only [prodDesc_zero, mul_one]
    exact ((Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp (hR 0)).symm
  | succ k ih =>
    rw [prodDesc_succ (fun i : Fin (k + 1) => R i.succ * Wb i * (R i.castSucc)ᵀ),
      prodDesc_succ Wb]
    have key := ih (fun j : Fin (k + 1) => R j.castSucc) (fun i : Fin k => Wb i.castSucc)
      (fun j => hR j.castSucc)
    simp only [Fin.castSucc_succ] at key
    rw [key, Fin.succ_last, Fin.castSucc_zero']
    have hCC := hR (Fin.last k).castSucc
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (R (Fin.last k).castSucc)ᵀ (R (Fin.last k).castSucc), hCC,
      Matrix.one_mul]

/-- `∏_{i>l} Wᵢ` in descending order: the product of the layers *above* `l`. -/
def aboveProd (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  ((List.ofFn W).reverse.take (m - 1 - (l : ℕ))).prod

/-- `∏_{i<l} Wᵢ` in descending order: the product of the layers *below* `l`. -/
def belowProd (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  ((List.ofFn W).reverse.drop (m - (l : ℕ))).prod

/-- `List.ofFn` of an updated family is the list with one entry `set`. -/
lemma ofFn_update_eq_set (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    List.ofFn (Function.update W l V) = (List.ofFn W).set (l : ℕ) V := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply, Fin.ext_iff]
    by_cases hil : i = (l : ℕ)
    · simp [hil]
    · simp [hil, Ne.symm hil]

/-- Reversing commutes with `set` (reflecting the index). -/
lemma reverse_set {α : Type*} (L : List α) (i : ℕ) (a : α) (hi : i < L.length) :
    (L.set i a).reverse = L.reverse.set (L.length - 1 - i) a := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.length_reverse, List.length_set] at h1
    simp only [List.getElem_reverse, List.getElem_set, List.length_set]
    by_cases hj : i = L.length - 1 - j
    · rw [if_pos hj, if_pos (by omega)]
    · rw [if_neg hj, if_neg (by omega)]

/-- **Product split.** Replacing layer `l` by `V` and taking the descending product
factors as `aboveProd · V · belowProd` (the layers above and below `l` are
untouched). The crux structural lemma behind Phase A. -/
lemma prodDesc_update (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    prodDesc (Function.update W l V) = aboveProd W l * V * belowProd W l := by
  have hl : (l : ℕ) < m := l.isLt
  unfold prodDesc aboveProd belowProd
  rw [ofFn_update_eq_set, reverse_set _ _ _ (by rw [List.length_ofFn]; exact hl), List.prod_set]
  simp only [List.length_reverse, List.length_ofFn]
  rw [if_pos (by omega), show m - 1 - (l : ℕ) + 1 = m - (l : ℕ) by omega]

/-! ## The unified bilinear entry-derivative

Both 3-layer partials of `MatrixFlow` are instances of one fact: the entry partial
of `½‖S − A X B‖²` in `X` is `−Aᵀ(S − A X B)Bᵀ`. With `A = aboveProd`, `B = belowProd`
this gives every layer's partial. -/

/-- `A · single k j 1` picks column `k` of `A` into column `j`. -/
private lemma mul_single_col (A : Matrix (Fin n) (Fin n) ℝ) (k j : Fin n) (p x : Fin n) :
    (A * Matrix.single k j (1 : ℝ)) p x = if x = j then A p k else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp [eq_comm]

/-- `(A · single k j 1 · B)ₚ_q = Aₚₖ · B_jq`. -/
private lemma single_sandwich_apply (A B : Matrix (Fin n) (Fin n) ℝ) (k j p q : Fin n) :
    (A * Matrix.single k j (1 : ℝ) * B) p q = A p k * B j q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [mul_single_col, if_pos rfl]
  · intro x _ hx; rw [mul_single_col, if_neg hx, zero_mul]
  · intro h; simp at h

/-- Entry of `A · (X + x • single k j 1) · B`, separating the `x`-linear part. -/
private lemma mul_add_smul_sandwich_apply (A X B : Matrix (Fin n) (Fin n) ℝ) (k j : Fin n)
    (x : ℝ) (p q : Fin n) :
    (A * (X + x • Matrix.single k j (1 : ℝ)) * B) p q
      = (A * X * B) p q + x * (A * Matrix.single k j (1 : ℝ) * B) p q := by
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]

/-- Derivative at `0` of a squared affine function `x ↦ (c − x d)²`. -/
private lemma hasDerivAt_sq_affine (c d : ℝ) :
    HasDerivAt (fun x : ℝ => (c - x * d) ^ 2) (-2 * d * c) 0 := by
  have h1 : HasDerivAt (fun x : ℝ => c - x * d) (-d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_sub c
  have h2 := h1.mul h1
  simp only [pow_two]
  rw [show (-2 * d * c : ℝ) = (-d) * (c - 0 * d) + (c - 0 * d) * (-d) by ring]
  exact h2

/-- The Frobenius assembly: `(Aᵀ M Bᵀ)ₖⱼ = ∑ₚ ∑_q Aₚₖ Mₚ_q B_jq`. -/
private lemma transpose_sandwich_apply (A M B : Matrix (Fin n) (Fin n) ℝ) (k j : Fin n) :
    (Aᵀ * M * Bᵀ) k j = ∑ p, ∑ q, A p k * M p q * B j q := by
  rw [Matrix.mul_apply,
    show (∑ x, (Aᵀ * M) k x * Bᵀ x j) = ∑ x, ∑ p, Aᵀ k p * M p x * Bᵀ x j from
      Finset.sum_congr rfl (fun x _ => by rw [Matrix.mul_apply, Finset.sum_mul]),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.transpose_apply, Matrix.transpose_apply]

/-- **Unified bilinear entry-derivative.** The directional derivative at `0` of
`x ↦ ½‖S − A (X + x·single k j 1) B‖²` is `−(Aᵀ(S − A X B)Bᵀ)ₖⱼ`. Instantiating
`A = aboveProd`, `X = Wₗ`, `B = belowProd` gives each layer's loss partial. -/
theorem hasDerivAt_loss_layer (S A X B : Matrix (Fin n) (Fin n) ℝ) (k j : Fin n) :
    HasDerivAt
      (fun x : ℝ => (∑ p, ∑ q, (S p q - (A * (X + x • Matrix.single k j (1 : ℝ)) * B) p q) ^ 2) / 2)
      (-((Aᵀ * (S - A * X * B) * Bᵀ) k j)) 0 := by
  have hfun :
      (fun x : ℝ => (∑ p, ∑ q, (S p q - (A * (X + x • Matrix.single k j (1 : ℝ)) * B) p q) ^ 2) / 2)
        = (fun x => (∑ p, ∑ q,
            ((S p q - (A * X * B) p q) - x * (A * Matrix.single k j (1 : ℝ) * B) p q) ^ 2) / 2) := by
    funext x
    congr 1
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [mul_add_smul_sandwich_apply]; ring
  rw [hfun]
  have hD := (HasDerivAt.sum fun p (_ : p ∈ Finset.univ) =>
      HasDerivAt.sum fun q (_ : q ∈ Finset.univ) =>
        hasDerivAt_sq_affine (S p q - (A * X * B) p q)
          ((A * Matrix.single k j (1 : ℝ) * B) p q)).div_const 2
  rw [show ((∑ p, ∑ q, -2 * (A * Matrix.single k j (1 : ℝ) * B) p q * (S p q - (A * X * B) p q)) / 2 : ℝ)
      = -((Aᵀ * (S - A * X * B) * Bᵀ) k j) from ?_] at hD
  · simpa only [Finset.sum_apply] using hD
  · rw [transpose_sandwich_apply]
    simp only [single_sandwich_apply, Matrix.sub_apply]
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring

/-! ## Phase A: the matrix gradient flow `multilayer_dyn` -/

/-- Deep network square loss with whitened inputs (`Σ¹¹ = I`):
`E(W) = ½ ∑ᵢⱼ (Σ³¹ − W_{m-1}⋯W₀)ᵢⱼ²`. -/
noncomputable def Edeep (S : Matrix (Fin n) (Fin n) ℝ)
    (W : Fin m → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∑ i, ∑ j, (S i j - (prodDesc W) i j) ^ 2) / 2

/-- The descending product split at any layer (special case `V = Wₗ` of
`prodDesc_update`): `prodDesc W = aboveProd W l · Wₗ · belowProd W l`. -/
lemma prodDesc_split (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m) :
    prodDesc W = aboveProd W l * W l * belowProd W l := by
  conv_lhs => rw [← Function.update_eq_self l W]
  rw [prodDesc_update]

/-- Entry partial of the deep loss `E` in layer `l`:
`∂E/∂(Wₗ)ₖⱼ = −(aboveProdᵀ (Σ³¹ − ∏W) belowProdᵀ)ₖⱼ` (the `l`-component of `−∇E`,
Saxe Eq. `multilayer_dyn`), as the directional derivative along `single k j 1`. -/
theorem hasDerivAt_Edeep_layer (S : Matrix (Fin n) (Fin n) ℝ)
    (W : Fin m → Matrix (Fin n) (Fin n) ℝ) (l : Fin m) (k j : Fin n) :
    HasDerivAt (fun x : ℝ => Edeep S (Function.update W l (W l + x • Matrix.single k j (1 : ℝ))))
      (-(((aboveProd W l)ᵀ * (S - prodDesc W) * (belowProd W l)ᵀ) k j)) 0 := by
  have hfun : (fun x : ℝ => Edeep S (Function.update W l (W l + x • Matrix.single k j (1 : ℝ))))
      = (fun x => (∑ p, ∑ q,
          (S p q - (aboveProd W l * (W l + x • Matrix.single k j (1 : ℝ)) * belowProd W l) p q) ^ 2)
          / 2) := by
    funext x
    unfold Edeep
    rw [prodDesc_update]
  rw [hfun]
  have key := hasDerivAt_loss_layer S (aboveProd W l) (W l) (belowProd W l) k j
  rw [← prodDesc_split] at key
  exact key

/-- Per-entry gradient flow on the deep network square loss `E` with timescale `τ`:
each weight entry's velocity is `−1/τ` times its partial of `E`. -/
structure IsDeepMatrixGradFlow (τ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (W : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ) : Prop where
  h : ∀ (l : Fin m) (t : ℝ) (k j : Fin n), HasDerivAt (fun s => W l s k j)
        (-(deriv (fun (x : ℝ) => Edeep S
            (Function.update (fun i => W i t) l (W l t + x • Matrix.single k j (1 : ℝ)))) 0) / τ) t

/-- **Matrix dynamics of the deep linear network (Saxe Eq. `multilayer_dyn`).**
Per-entry gradient flow on the deep square loss `E` is the matrix flow
`τ Ẇₗ = (∏_{i>l} Wᵢ)ᵀ (Σ³¹ − ∏ᵢ Wᵢ) (∏_{i<l} Wᵢ)ᵀ`, with the prefix/suffix products
written `aboveProd`/`belowProd`. -/
theorem multilayerFlow_of_gradFlow {τ : ℝ} {S : Matrix (Fin n) (Fin n) ℝ}
    {W : Fin m → ℝ → Matrix (Fin n) (Fin n) ℝ} (h : IsDeepMatrixGradFlow τ S W) (l : Fin m)
    (t : ℝ) :
    HasDerivAt (W l) ((1 / τ) • ((aboveProd (fun i => W i t) l)ᵀ *
      (S - prodDesc (fun i => W i t)) * (belowProd (fun i => W i t) l)ᵀ)) t := by
  refine hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun j => ?_
  have hflow := h.h l t k j
  rw [(hasDerivAt_Edeep_layer S (fun i => W i t) l k j).deriv] at hflow
  rw [Matrix.smul_apply, smul_eq_mul,
    show (1 / τ) * ((aboveProd (fun i => W i t) l)ᵀ * (S - prodDesc (fun i => W i t)) *
        (belowProd (fun i => W i t) l)ᵀ) k j
      = -(-(((aboveProd (fun i => W i t) l)ᵀ * (S - prodDesc (fun i => W i t)) *
        (belowProd (fun i => W i t) l)ᵀ) k j)) / τ by ring]
  exact hflow

end DlnDynamics
