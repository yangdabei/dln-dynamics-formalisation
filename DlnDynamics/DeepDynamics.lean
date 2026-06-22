import DlnDynamics.Basic

/-!
# Deeper multilayer dynamics — the depth-`N` law (Saxe Eq. `deep_dyn`)

This module formalizes the headline result of Saxe §"Deeper multilayer dynamics".
A linear network with `N_l` layers has `m = N_l − 1` weight matrices.  Under the
decoupling initial conditions (output singular vectors of layer `l` are the input
singular vectors of layer `l+1`), each connectivity mode is described by `m`
scalars `a₁,…,aₘ` performing gradient descent on the energy (the analog of the
two-layer `ab_2en`)

`E(a₁,…,aₘ) = (1/2τ) (s − ∏ᵢ aᵢ)²`,

so each layer scalar obeys `τ aₗ' = (s − ∏ᵢ aᵢ)·∏_{i≠l} aᵢ` (`IsDeepFlow`).

This module provides:

* `IsDeepFlow` — the `m`-scalar gradient-flow system on the deep energy;
* `IsDeepSymFlow` — the reduced scalar flow `τ a' = (s − aᵐ) aᵐ⁻¹` on the
  symmetric submanifold `a₁ = ⋯ = aₘ`;
* `deepFlow_conserved` / `deepFlow_conserved_eq` — the conserved quantities
  `aᵢ² − aⱼ²` arising from the energetic scaling symmetry (Saxe §"Deeper
  multilayer dynamics"; the depth-`N` analog of `ab_conserved`);
* `isDeepSymFlow_of_symmetric` — the algebraic reduction onto the symmetric
  submanifold;
* `deepSym_hasDerivAt` / `deep_dyn` — the **depth-`N` law** (Saxe Eq. `deep_dyn`):
  the overall mode strength `u = ∏ᵢ aᵢ = aᵐ` obeys the generalized logistic
  `τ u' = (N_l − 1) u^{2 − 2/(N_l−1)} (s − u)`.

For `m = 2` (`N_l = 3`) this specializes to the two-layer `sigmoidal_dyn`
`τ u' = 2 u (s − u)`.

Forward-invariance *in time* of the symmetric submanifold (that equal initial
layer scalars stay equal) is an ODE-uniqueness statement, the depth-`N` analog of
`ManifoldInvariance.lean`; it is deferred.  Here the reduction is established
algebraically: *if* the layer scalars coincide at each time, the common scalar
obeys the reduced flow and the strength obeys `deep_dyn`.
-/

namespace DlnDynamics

open Finset

/-- The `m`-scalar gradient-flow system for one connectivity mode of an
`N_l`-layer linear network with `m = N_l − 1` weight matrices.  The layer scalars
`a₁,…,aₘ` perform gradient descent on the deep energy
`E(a) = (1/2τ)(s − ∏ᵢ aᵢ)²`, giving
`τ aₗ' = (s − ∏ᵢ aᵢ) · ∏_{i≠l} aᵢ` (derivative isolated on the left, `τ ≠ 0`). -/
structure IsDeepFlow (s τ : ℝ) {m : ℕ} (a : Fin m → ℝ → ℝ) : Prop where
  ha : ∀ l t, HasDerivAt (a l)
    ((s - ∏ i, a i t) * (∏ i ∈ univ.erase l, a i t) / τ) t

/-- The reduced scalar dynamics on the symmetric submanifold `a₁ = ⋯ = aₘ = a`:
the common layer scalar obeys `τ a' = (s − aᵐ) aᵐ⁻¹`.  This is the per-layer
reduction underlying the depth-`N` law `deep_dyn`. -/
structure IsDeepSymFlow (s τ : ℝ) (m : ℕ) (a : ℝ → ℝ) : Prop where
  ha : ∀ t, HasDerivAt a ((s - a t ^ m) * a t ^ (m - 1) / τ) t

/-- Along the deep flow, `aᵢ aᵢ'` is the same for every layer `i`, namely
`(s − P)·P/τ` with `P = ∏ aₖ`, because `(∏_{k≠i} aₖ)·aᵢ = P`.  Hence the
time-derivative of `aᵢ² − aⱼ²` vanishes: it is a constant of motion (Saxe: the
conserved quantities `aᵢ² − aⱼ²` of the deep energy, the depth-`N` analog of
`ab_conserved`). -/
theorem deepFlow_conserved {s τ : ℝ} {m : ℕ} {a : Fin m → ℝ → ℝ}
    (h : IsDeepFlow s τ a) (i j : Fin m) (t : ℝ) :
    HasDerivAt (fun r => a i r ^ 2 - a j r ^ 2) 0 t := by
  have hsub := ((h.ha i t).mul (h.ha i t)).sub ((h.ha j t).mul (h.ha j t))
  have hPi : (∏ k ∈ univ.erase i, a k t) * a i t = ∏ k, a k t :=
    Finset.prod_erase_mul _ _ (mem_univ i)
  have hPj : (∏ k ∈ univ.erase j, a k t) * a j t = ∏ k, a k t :=
    Finset.prod_erase_mul _ _ (mem_univ j)
  have hval :
      (s - ∏ k, a k t) * (∏ k ∈ univ.erase i, a k t) / τ * a i t +
          a i t * ((s - ∏ k, a k t) * (∏ k ∈ univ.erase i, a k t) / τ) -
        ((s - ∏ k, a k t) * (∏ k ∈ univ.erase j, a k t) / τ * a j t +
          a j t * ((s - ∏ k, a k t) * (∏ k ∈ univ.erase j, a k t) / τ)) = 0 := by
    rw [show
        (s - ∏ k, a k t) * (∏ k ∈ univ.erase i, a k t) / τ * a i t +
            a i t * ((s - ∏ k, a k t) * (∏ k ∈ univ.erase i, a k t) / τ) -
          ((s - ∏ k, a k t) * (∏ k ∈ univ.erase j, a k t) / τ * a j t +
            a j t * ((s - ∏ k, a k t) * (∏ k ∈ univ.erase j, a k t) / τ)) =
          2 * (s - ∏ k, a k t) / τ * ((∏ k ∈ univ.erase i, a k t) * a i t) -
            2 * (s - ∏ k, a k t) / τ * ((∏ k ∈ univ.erase j, a k t) * a j t) from by
        ring, hPi, hPj, sub_self]
  rw [hval] at hsub
  have heq : (fun r => a i r ^ 2 - a j r ^ 2) = a i * a i - a j * a j := by
    funext r; simp only [Pi.sub_apply, Pi.mul_apply, pow_two]
  rw [heq]
  exact hsub

/-- The constant-of-motion form: `aᵢ(t)² − aⱼ(t)² = aᵢ(0)² − aⱼ(0)²`. -/
theorem deepFlow_conserved_eq {s τ : ℝ} {m : ℕ} {a : Fin m → ℝ → ℝ}
    (h : IsDeepFlow s τ a) (i j : Fin m) (t : ℝ) :
    a i t ^ 2 - a j t ^ 2 = a i 0 ^ 2 - a j 0 ^ 2 := by
  have hdiff : Differentiable ℝ (fun r => a i r ^ 2 - a j r ^ 2) := fun x =>
    (deepFlow_conserved h i j x).differentiableAt
  have hzero : ∀ x, deriv (fun r => a i r ^ 2 - a j r ^ 2) x = 0 := fun x =>
    (deepFlow_conserved h i j x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

/-- Algebraic reduction onto the symmetric submanifold: if every layer scalar
coincides with a common `c` at each time, then `c` obeys the reduced scalar flow
`IsDeepSymFlow` (`τ c' = (s − cᵐ) cᵐ⁻¹`).  Uses `∏ᵢ c = cᵐ` and
`∏_{i≠l} c = cᵐ⁻¹`. -/
theorem isDeepSymFlow_of_symmetric {s τ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    {a : Fin m → ℝ → ℝ} {c : ℝ → ℝ} (h : IsDeepFlow s τ a)
    (hsym : ∀ i t, a i t = c t) : IsDeepSymFlow s τ m c where
  ha := fun t => by
    have l : Fin m := ⟨0, hm⟩
    have hac : a l = c := funext (fun r => hsym l r)
    have hP : (∏ i, a i t) = c t ^ m := by
      rw [Finset.prod_congr rfl (fun i _ => hsym i t), Finset.prod_const, card_univ,
        Fintype.card_fin]
    have hPe : (∏ i ∈ univ.erase l, a i t) = c t ^ (m - 1) := by
      rw [Finset.prod_congr rfl (fun i _ => hsym i t), Finset.prod_const,
        Finset.card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin]
    have key := h.ha l t
    rw [hP, hPe, hac] at key
    exact key

/-- **Depth-`N` law, Nat-power form** (Saxe Eq. `deep_dyn`).  On the symmetric
submanifold, the overall mode strength `u = aᵐ` obeys
`τ u' = m · aᵐ⁻¹·aᵐ⁻¹ · (s − aᵐ) = m · a^{2(m−1)} · (s − u)`. -/
theorem deepSym_hasDerivAt {s τ : ℝ} {m : ℕ} {a : ℝ → ℝ}
    (h : IsDeepSymFlow s τ m a) (t : ℝ) :
    HasDerivAt (fun r => a r ^ m)
      ((m : ℝ) * (s - a t ^ m) * a t ^ (2 * (m - 1)) / τ) t := by
  have key := (h.ha t).pow m
  have hpow : a t ^ (m - 1) * a t ^ (m - 1) = a t ^ (2 * (m - 1)) := by
    rw [← pow_add, two_mul]
  rw [show (m : ℝ) * a t ^ (m - 1) * ((s - a t ^ m) * a t ^ (m - 1) / τ)
        = (m : ℝ) * (s - a t ^ m) * (a t ^ (m - 1) * a t ^ (m - 1)) / τ from by ring,
    hpow] at key
  exact key

/-- Bridge from the Nat-power exponent `a^{2(m−1)}` to the real-power form
`(aᵐ)^{2 − 2/m}` of the paper, valid for `0 < a`, `1 ≤ m`. -/
theorem rpow_bridge {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    (a ^ m : ℝ) ^ (2 - 2 / (m : ℝ)) = a ^ (2 * (m - 1)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : (m : ℝ) * (2 - 2 / (m : ℝ)) = ((2 * (m - 1) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hm]
    field_simp
  rw [← Real.rpow_natCast a m, ← Real.rpow_mul ha.le, hexp, Real.rpow_natCast]

/-- **Depth-`N` law** (Saxe Eq. `deep_dyn`), in the paper's exact real-power form.
On the symmetric submanifold with positive layer scalars, the overall mode
strength `u = aᵐ` obeys the generalization of the logistic `sigmoidal_dyn`:

`τ u' = (N_l − 1) · u^{2 − 2/(N_l−1)} · (s − u)`,  with `m = N_l − 1`.

For `m = 2` (`N_l = 3`) the exponent `2 − 2/2 = 1` recovers `τ u' = 2 u (s − u)`. -/
theorem deep_dyn {s τ : ℝ} {m : ℕ} (hm : 1 ≤ m) {a : ℝ → ℝ}
    (h : IsDeepSymFlow s τ m a) (hpos : ∀ t, 0 < a t) (t : ℝ) :
    HasDerivAt (fun r => a r ^ m)
      ((m : ℝ) * (a t ^ m) ^ (2 - 2 / (m : ℝ)) * (s - a t ^ m) / τ) t := by
  rw [show (m : ℝ) * (a t ^ m) ^ (2 - 2 / (m : ℝ)) * (s - a t ^ m) / τ
        = (m : ℝ) * (s - a t ^ m) * a t ^ (2 * (m - 1)) / τ from by
      rw [rpow_bridge (hpos t) hm]; ring]
  exact deepSym_hasDerivAt h t

/-- End-to-end depth-`N` law from the full gradient flow: if the `m` layer
scalars of a `IsDeepFlow` mode coincide (positive symmetric submanifold), their
common product `u = cᵐ` obeys `deep_dyn`. -/
theorem deep_dyn_of_deepFlow {s τ : ℝ} {m : ℕ} (hm : 1 ≤ m)
    {a : Fin m → ℝ → ℝ} {c : ℝ → ℝ} (h : IsDeepFlow s τ a)
    (hsym : ∀ i t, a i t = c t) (hpos : ∀ t, 0 < c t) (t : ℝ) :
    HasDerivAt (fun r => c r ^ m)
      ((m : ℝ) * (c t ^ m) ^ (2 - 2 / (m : ℝ)) * (s - c t ^ m) / τ) t :=
  deep_dyn hm (isDeepSymFlow_of_symmetric hm h hsym) hpos t

/-- Consistency cross-check with the two-layer development: at `m = 2`
(`N_l = 3`) the depth-`N` law `deepSym_hasDerivAt` reduces to the logistic
`sigmoidal_dyn` `τ u' = 2 u (s − u)` with `u = a²`, matching the reduced two-mode
dynamics of `Basic`/`ClosedForm`. -/
theorem deepSym_hasDerivAt_two {s τ : ℝ} {a : ℝ → ℝ} (h : IsDeepSymFlow s τ 2 a)
    (t : ℝ) :
    HasDerivAt (fun r => a r ^ 2) (2 * a t ^ 2 * (s - a t ^ 2) / τ) t := by
  have key := deepSym_hasDerivAt h t
  norm_num at key
  rw [show (2 : ℝ) * (s - a t ^ 2) * a t ^ 2 / τ
        = 2 * a t ^ 2 * (s - a t ^ 2) / τ by ring] at key
  exact key

end DlnDynamics
