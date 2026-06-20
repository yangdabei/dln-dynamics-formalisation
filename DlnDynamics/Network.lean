import DlnDynamics.GradientFlow

/-!
# Deriving the per-mode loss from the one-mode network

The per-mode square loss `L s a b = ½ (s − a b)²` of `DlnDynamics.GradientFlow`
is itself the empirical square error of a single mode of the linear network.
For one input–output mode, the network maps a scalar input `xμ` to the prediction
`ŷμ = a b xμ` (input → hidden via `a`, hidden → output via `b`), and learning
minimizes the summed squared error over the `P` training examples.

With **whitened inputs** `∑μ xμ² = 1` (Saxe's `Σ¹¹ = I` assumption) and
**mode correlation** `∑μ xμ yμ = s`, the empirical loss reduces to `L` up to an
additive constant independent of the weights:

`Lsq a b = L s a b + c`,  `c = ½ ∑μ yμ² − ½ s²`.

Since `c` is constant in `(a, b)`, the gradient flow of `Lsq` has the same
velocity field as that of `L`, so it too produces `IsABFlow` (Saxe Eq. `ab_dyn`).

This module provides:

* `Lsq` — the one-mode network's empirical square loss;
* `Lsq_eq` — the reduction `Lsq a b = L s a b + const` (Saxe Eq. `ab_2en`);
* `hasDerivAt_Lsq_fst`, `hasDerivAt_Lsq_snd` — its partial derivatives coincide
  with those of `L` (the constant drops out);
* `isABFlow_of_networkGradFlow` — gradient flow of the network's square loss is
  `IsABFlow`.
-/

namespace DlnDynamics

open Finset

variable {P : ℕ}

/-- Empirical square loss of one mode of the linear network: with prediction
`ŷμ = a b xμ` on inputs `x` and targets `y`, this is `½ ∑μ (yμ − a b xμ)²`. -/
noncomputable def Lsq (a b : ℝ) (x y : Fin P → ℝ) : ℝ :=
  (∑ μ, (y μ - a * b * x μ) ^ 2) / 2

/-- With whitened inputs `∑ xμ² = 1` and mode correlation `∑ xμ yμ = s`, the
one-mode network square loss reduces to the per-mode loss `L` plus a constant
independent of the weights (Saxe Eq. `ab_2en`):
`Lsq a b = L s a b + (½ ∑ yμ² − ½ s²)`. -/
theorem Lsq_eq (s a b : ℝ) (x y : Fin P → ℝ)
    (hx : ∑ μ, (x μ) ^ 2 = 1) (hxy : ∑ μ, x μ * y μ = s) :
    Lsq a b x y = L s a b + ((∑ μ, (y μ) ^ 2) / 2 - s ^ 2 / 2) := by
  have key : ∑ μ, (y μ - a * b * x μ) ^ 2
      = (∑ μ, (y μ) ^ 2) - 2 * (a * b) * (∑ μ, x μ * y μ)
        + (a * b) ^ 2 * (∑ μ, (x μ) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun μ _ => by ring)
  unfold Lsq L
  rw [key, hx, hxy]
  ring

/-- The partial derivative of the network loss in `a` matches that of `L`:
`∂ₐ Lsq = −b (s − a b)` (the additive constant from `Lsq_eq` drops out). -/
theorem hasDerivAt_Lsq_fst (s a₀ b₀ : ℝ) (x y : Fin P → ℝ)
    (hx : ∑ μ, (x μ) ^ 2 = 1) (hxy : ∑ μ, x μ * y μ = s) :
    HasDerivAt (fun a => Lsq a b₀ x y) (-b₀ * (s - a₀ * b₀)) a₀ := by
  have heq : (fun a => Lsq a b₀ x y)
      = (fun a => L s a b₀ + ((∑ μ, (y μ) ^ 2) / 2 - s ^ 2 / 2)) := by
    funext a; exact Lsq_eq s a b₀ x y hx hxy
  rw [heq]
  exact (hasDerivAt_L_fst s a₀ b₀).add_const _

/-- The partial derivative of the network loss in `b` matches that of `L`:
`∂_b Lsq = −a (s − a b)`. -/
theorem hasDerivAt_Lsq_snd (s a₀ b₀ : ℝ) (x y : Fin P → ℝ)
    (hx : ∑ μ, (x μ) ^ 2 = 1) (hxy : ∑ μ, x μ * y μ = s) :
    HasDerivAt (fun b => Lsq a₀ b x y) (-a₀ * (s - a₀ * b₀)) b₀ := by
  have heq : (fun b => Lsq a₀ b x y)
      = (fun b => L s a₀ b + ((∑ μ, (y μ) ^ 2) / 2 - s ^ 2 / 2)) := by
    funext b; exact Lsq_eq s a₀ b x y hx hxy
  rw [heq]
  exact (hasDerivAt_L_snd s a₀ b₀).add_const _

/-- **Network derivation of the two-mode dynamics.** If the scalar projections
`a, b` follow gradient flow on the one-mode network's empirical square loss
`Lsq` with timescale `τ`, under whitened inputs (`∑ xμ² = 1`) and mode
correlation `∑ xμ yμ = s`, then they obey `IsABFlow s τ a b` (Saxe Eq. `ab_dyn`).
This realizes `IsABFlow` as gradient descent on the network's loss. -/
theorem isABFlow_of_networkGradFlow {s τ : ℝ} {a b : ℝ → ℝ}
    (x y : Fin P → ℝ) (hx : ∑ μ, (x μ) ^ 2 = 1) (hxy : ∑ μ, x μ * y μ = s)
    (ha : ∀ t, HasDerivAt a (-(deriv (fun a' => Lsq a' (b t) x y) (a t)) / τ) t)
    (hb : ∀ t, HasDerivAt b (-(deriv (fun b' => Lsq (a t) b' x y) (b t)) / τ) t) :
    IsABFlow s τ a b := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hd := (hasDerivAt_Lsq_fst s (a t) (b t) x y hx hxy).deriv
    have hflow := ha t
    rw [hd] at hflow
    rwa [show -(-b t * (s - a t * b t)) / τ = b t * (s - a t * b t) / τ by ring]
      at hflow
  · have hd := (hasDerivAt_Lsq_snd s (a t) (b t) x y hx hxy).deriv
    have hflow := hb t
    rw [hd] at hflow
    rwa [show -(-a t * (s - a t * b t)) / τ = a t * (s - a t * b t) / τ by ring]
      at hflow

end DlnDynamics
