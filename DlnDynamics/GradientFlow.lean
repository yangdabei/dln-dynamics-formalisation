import DlnDynamics.Basic

/-!
# `IsABFlow` is the gradient flow of the per-mode square loss

Saxe Eq. `ab_dyn` is posited in `DlnDynamics.Basic`. The paper (Eq. `ab_2en`)
notes that this two-mode system *arises from gradient descent* on the per-mode
error `E(a,b) = ½ (s − a b)²`. This module makes that precise: with timescale
`τ`, the gradient flow `τ a' = −∂ₐL`, `τ b' = −∂_b L` of

`L s a b = ½ (s − a b)²`

is exactly `IsABFlow s τ a b`. This turns `IsABFlow` from a hypothesis into a
*derived* consequence of gradient flow.

This module provides:

* `L` — the per-mode square loss (Saxe Eq. `ab_2en`, modulo the `1/τ` prefactor,
  which we carry in the flow timescale instead);
* `hasDerivAt_L_fst`, `hasDerivAt_L_snd` — the partial derivatives
  `∂ₐL = −b (s − a b)`, `∂_b L = −a (s − a b)`;
* `IsABGradFlow` — the per-coordinate gradient-flow predicate;
* `isABFlow_of_gradFlow` — gradient flow of `L` is `IsABFlow` (Eq. `ab_2en` ⇒
  Eq. `ab_dyn`).
-/

namespace DlnDynamics

/-- Per-mode square-loss energy `L(a,b) = ½ (s − a b)²` (Saxe Eq. `ab_2en`,
modulo the `1/τ` prefactor, which we carry in the flow timescale). -/
noncomputable def L (s a b : ℝ) : ℝ := (s - a * b) ^ 2 / 2

/-- Partial derivative of `L` in its first slot: `∂ₐ L = −b (s − a b)`
(the `a`-component of `−∇E` in Saxe Eq. `ab_dyn`). -/
theorem hasDerivAt_L_fst (s a₀ b₀ : ℝ) :
    HasDerivAt (fun x => L s x b₀) (-b₀ * (s - a₀ * b₀)) a₀ := by
  have h1 : HasDerivAt (fun x => s - x * b₀) (-(1 * b₀)) a₀ :=
    ((hasDerivAt_id a₀).mul_const b₀).const_sub s
  have h2 := (h1.mul h1).div_const 2
  simp only [L, pow_two]
  rw [show (-b₀ * (s - a₀ * b₀))
      = (-(1 * b₀) * (s - a₀ * b₀) + (s - a₀ * b₀) * -(1 * b₀)) / 2 by ring]
  exact h2

/-- Partial derivative of `L` in its second slot: `∂_b L = −a (s − a b)`
(the `b`-component of `−∇E` in Saxe Eq. `ab_dyn`). -/
theorem hasDerivAt_L_snd (s a₀ b₀ : ℝ) :
    HasDerivAt (fun y => L s a₀ y) (-a₀ * (s - a₀ * b₀)) b₀ := by
  have h1 : HasDerivAt (fun y => s - a₀ * y) (-(a₀ * 1)) b₀ :=
    ((hasDerivAt_id b₀).const_mul a₀).const_sub s
  have h2 := (h1.mul h1).div_const 2
  simp only [L, pow_two]
  rw [show (-a₀ * (s - a₀ * b₀))
      = (-(a₀ * 1) * (s - a₀ * b₀) + (s - a₀ * b₀) * -(a₀ * 1)) / 2 by ring]
  exact h2

/-- Per-coordinate gradient flow on the per-mode square loss `L` with timescale
`τ`: each weight's velocity is `−1/τ` times its partial derivative of `L`,
`τ a' = −∂ₐ L` and `τ b' = −∂_b L` (the gradient-descent form behind Saxe
Eq. `ab_dyn`, cf. Eq. `ab_2en`). -/
structure IsABGradFlow (s τ : ℝ) (a b : ℝ → ℝ) : Prop where
  ha : ∀ t, HasDerivAt a (-(deriv (fun x => L s x (b t)) (a t)) / τ) t
  hb : ∀ t, HasDerivAt b (-(deriv (fun y => L s (a t) y) (b t)) / τ) t

/-- The posited two-mode flow `IsABFlow` (Saxe Eq. `ab_dyn`) is exactly the
gradient flow of the per-mode square loss `L` (Eq. `ab_2en`):
`∂ₐL = −b(s − a b)` gives `τ a' = −∂ₐL = b(s − a b)`, and symmetrically for `b`. -/
theorem isABFlow_of_gradFlow {s τ : ℝ} {a b : ℝ → ℝ}
    (h : IsABGradFlow s τ a b) : IsABFlow s τ a b := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hd := (hasDerivAt_L_fst s (a t) (b t)).deriv
    have hflow := h.ha t
    rw [hd] at hflow
    rwa [show -(-b t * (s - a t * b t)) / τ = b t * (s - a t * b t) / τ by ring] at hflow
  · have hd := (hasDerivAt_L_snd s (a t) (b t)).deriv
    have hflow := h.hb t
    rw [hd] at hflow
    rwa [show -(-a t * (s - a t * b t)) / τ = a t * (s - a t * b t) / τ by ring] at hflow

end DlnDynamics
