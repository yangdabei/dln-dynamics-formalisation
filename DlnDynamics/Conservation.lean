import DlnDynamics.Basic

/-!
# Conservation of `a² − b²`

Along the coupled flow `IsABFlow` (Saxe Eq. `ab_dyn`) the quantity `a² − b²` is a
constant of motion. In Saxe §1.3 this is read off from the scaling symmetry
`a ↦ λ a`, `b ↦ b / λ` via Noether's theorem; here we prove it directly by
differentiating: `d/dt (a² − b²) = 2 a a' − 2 b b' = (2/τ)·a b (s − a b) −
(2/τ)·a b (s − a b) = 0`.

The hyperbola `a² − b² = const` is exactly the invariant manifold on which the
balanced reduction `a = b` of Saxe Eq. `sigmoidal_dyn` takes place.
-/

namespace DlnDynamics

/-- The time derivative of `a² − b²` vanishes along the flow (Saxe §1.3):
`a² − b²` is a constant of motion. -/
theorem ab_conserved {s τ : ℝ} {a b : ℝ → ℝ} (h : IsABFlow s τ a b) (t : ℝ) :
    HasDerivAt (fun r => a r ^ 2 - b r ^ 2) 0 t := by
  -- `HasDerivAt.mul`/`.sub` give the product-rule derivative; it vanishes by `ring`.
  have hsub := ((h.ha t).mul (h.ha t)).sub ((h.hb t).mul (h.hb t))
  rw [show
      b t * (s - a t * b t) / τ * a t + a t * (b t * (s - a t * b t) / τ) -
        (a t * (s - a t * b t) / τ * b t + b t * (a t * (s - a t * b t) / τ)) = (0 : ℝ) by
      ring] at hsub
  -- the combinators build the function at `Pi` level (`a * a - b * b`); bridge to `^2`
  have heq : (fun r => a r ^ 2 - b r ^ 2) = a * a - b * b := by
    funext r; simp only [Pi.sub_apply, Pi.mul_apply, pow_two]
  rw [heq]
  exact hsub

/-- The constant-of-motion form: `a(t)² − b(t)² = a(0)² − b(0)²` for all `t`. -/
theorem ab_conserved_eq {s τ : ℝ} {a b : ℝ → ℝ} (h : IsABFlow s τ a b) (t : ℝ) :
    a t ^ 2 - b t ^ 2 = a 0 ^ 2 - b 0 ^ 2 := by
  have hdiff : Differentiable ℝ (fun r => a r ^ 2 - b r ^ 2) := fun x =>
    (ab_conserved h x).differentiableAt
  have hzero : ∀ x, deriv (fun r => a r ^ 2 - b r ^ 2) x = 0 := fun x =>
    (ab_conserved h x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero t 0

end DlnDynamics
