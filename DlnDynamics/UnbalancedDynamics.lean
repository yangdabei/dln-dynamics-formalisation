import DlnDynamics.Conservation

/-!
# Unbalanced (hyperbolic) mode dynamics (Saxe Appendix A, `hyper_dyn`)

The main text solves the balanced slice `a = b`, where `u = ab` obeys the logistic
`sigmoidal_dyn` `τ u' = 2u(s − u)`. Appendix A treats the general case `a ≠ b`, where
the trajectory follows the hyperbola `a² − b² = c₀` (a constant of motion,
`ab_conserved_eq`).

Tracking `u = ab` directly (rather than the paper's hyperbolic-angle `θ`, whose stated
relations in the appendix carry factor-of-2 typos), the product rule gives the clean,
exact dynamics

`τ u' = (a² + b²)(s − u) = √(c₀² + 4u²)·(s − u)`,

the hyperbolic generalization of `sigmoidal_dyn`: setting `c₀ = 0` (the balanced slice)
recovers `τ u' = 2u(s − u)`.
-/

namespace DlnDynamics

/-- **Unbalanced mode dynamics** (Saxe Appendix A `hyper_dyn`). For the general
two-mode flow `IsABFlow` (no `a = b` assumption), the overlap `u = ab` obeys
`τ u' = (a² + b²)(s − u)` — the product rule applied to `ab`. -/
theorem hyperbolic_dyn {s τ : ℝ} {a b : ℝ → ℝ} (h : IsABFlow s τ a b) (t : ℝ) :
    HasDerivAt (fun r => a r * b r) ((a t ^ 2 + b t ^ 2) * (s - a t * b t) / τ) t := by
  have hmul := (h.ha t).mul (h.hb t)
  rw [show b t * (s - a t * b t) / τ * b t + a t * (a t * (s - a t * b t) / τ)
        = (a t ^ 2 + b t ^ 2) * (s - a t * b t) / τ from by ring] at hmul
  exact hmul

/-- The unbalanced dynamics in explicit hyperbolic form, using the conserved
`c₀ = a² − b²`: `τ u' = √(c₀² + 4u²)(s − u)`. The balanced case `c₀ = 0` recovers
`sigmoidal_dyn` `τ u' = 2u(s − u)`. -/
theorem hyperbolic_dyn_sqrt {s τ : ℝ} {a b : ℝ → ℝ} (h : IsABFlow s τ a b) (t : ℝ) :
    HasDerivAt (fun r => a r * b r)
      (Real.sqrt ((a 0 ^ 2 - b 0 ^ 2) ^ 2 + 4 * (a t * b t) ^ 2) * (s - a t * b t) / τ) t := by
  have hconv : a t ^ 2 + b t ^ 2
      = Real.sqrt ((a 0 ^ 2 - b 0 ^ 2) ^ 2 + 4 * (a t * b t) ^ 2) := by
    rw [← ab_conserved_eq h t,
      show (a t ^ 2 - b t ^ 2) ^ 2 + 4 * (a t * b t) ^ 2 = (a t ^ 2 + b t ^ 2) ^ 2 from by ring,
      Real.sqrt_sq (by positivity)]
  rw [← hconv]
  exact hyperbolic_dyn h t

end DlnDynamics
