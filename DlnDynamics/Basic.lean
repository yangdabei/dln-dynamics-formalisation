import Mathlib

/-!
# Core definitions for the two-mode learning dynamics

Definitions and basic facts for the exact learning dynamics of a deep linear
network along a single decoupled input–output mode, following

* A. Saxe, J. McClelland, S. Ganguli, *Exact solutions to the nonlinear dynamics
  of learning in deep linear neural networks*, ICLR 2014, arXiv:1312.6120.

We work with a single mode of strength `s`, learning timescale `τ`, and the
scalar projections `a b : ℝ → ℝ` of the two weight layers onto that mode.

This module provides:

* `IsABFlow` — the coupled two-mode gradient-flow system (Saxe Eq. `ab_dyn`);
* `denom`, `uf` — the denominator and the closed-form sigmoidal solution
  (Saxe Eq. `u_soln`);
* `denom_pos` — strict positivity of the denominator on the paper's regime
  `0 < u₀ < s`, the basic fact every downstream proof relies on.
-/

namespace DlnDynamics

/-- The coupled two-mode gradient-flow system (Saxe Eq. `ab_dyn`):
`τ a' = b (s − a b)` and `τ b' = a (s − a b)`, written with the derivative
isolated on the left (valid for `τ ≠ 0`). Here `a b : ℝ → ℝ` are the scalar
projections of the two weight layers onto a single input–output mode of
strength `s`, and `τ` is the learning timescale. -/
structure IsABFlow (s τ : ℝ) (a b : ℝ → ℝ) : Prop where
  ha : ∀ t, HasDerivAt a (b t * (s - a t * b t) / τ) t
  hb : ∀ t, HasDerivAt b (a t * (s - a t * b t) / τ) t

/-- Denominator of the closed-form solution: `e^{2 s t / τ} − 1 + s / u₀`. -/
noncomputable def denom (s τ u₀ : ℝ) (t : ℝ) : ℝ :=
  Real.exp (2 * s * t / τ) - 1 + s / u₀

/-- The closed-form sigmoidal solution `u_f` of the reduced mode dynamics
(Saxe Eq. `u_soln`):
`u_f(t) = s · e^{2 s t / τ} / (e^{2 s t / τ} − 1 + s / u₀)`,
where `u₀ = u_f(0)` is the initial overlap `a(0) b(0)`. -/
noncomputable def uf (s τ u₀ : ℝ) (t : ℝ) : ℝ :=
  s * Real.exp (2 * s * t / τ) / denom s τ u₀ t

/-- On the paper's regime `0 < u₀ < s` the denominator of the closed-form
solution is strictly positive for all `t`: indeed `e^{2 s t / τ} > 0` and
`s / u₀ > 1`, so `e^{2 s t / τ} − 1 + s / u₀ > 0`. -/
theorem denom_pos (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (t : ℝ) :
    0 < denom s τ u₀ t := by
  have hexp : 0 < Real.exp (2 * s * t / τ) := Real.exp_pos _
  have hsu : 1 < s / u₀ := (one_lt_div hu₀).mpr hlt
  unfold denom
  linarith

end DlnDynamics
