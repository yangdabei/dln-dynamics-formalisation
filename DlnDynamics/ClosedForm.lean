import DlnDynamics.Basic

/-!
# The closed-form solution solves the reduced mode ODE

On the balanced slice `a = b`, with `u = a b`, the per-mode dynamics reduce to
the logistic ODE (Saxe Eq. `sigmoidal_dyn`)

`τ u' = 2 u (s − u)`.

This module shows the closed form `uf` (Saxe Eq. `u_soln`) is a genuine solution:

* `uf_zero` — the initial condition `u_f(0) = u₀`;
* `uf_hasDerivAt` — `u_f` satisfies the ODE, i.e. `u_f'(t) = (2/τ) u_f(t) (s − u_f(t))`.

Both hold on the paper's regime `0 < u₀ < s`, `0 < τ`.
-/

namespace DlnDynamics

/-- The closed form satisfies the initial condition `u_f(0) = u₀`. -/
theorem uf_zero (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) : uf s τ u₀ 0 = u₀ := by
  have hDne : denom s τ u₀ 0 ≠ 0 := (denom_pos s τ u₀ hu₀ hlt 0).ne'
  have hune : u₀ ≠ 0 := hu₀.ne'
  unfold uf
  rw [div_eq_iff hDne]
  unfold denom
  rw [show 2 * s * 0 / τ = 0 by ring, Real.exp_zero]
  field_simp
  ring

/-- The closed form `u_f` solves the reduced logistic ODE
`τ u' = 2 u (s − u)` (Saxe Eq. `sigmoidal_dyn`), stated as
`u_f'(t) = (2/τ) u_f(t) (s − u_f(t))`.

We build the quotient-rule derivative of `u_f = N / D` with
`N = s e^{2 s t / τ}`, `D = denom`, then rewrite the target derivative into that
quotient form (a rational identity that closes by `field_simp; ring`, keeping
`D = denom` folded as an opaque nonzero atom) and discharge by `HasDerivAt.div`. -/
theorem uf_hasDerivAt (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (hτ : 0 < τ)
    (t : ℝ) :
    HasDerivAt (uf s τ u₀) ((2 / τ) * uf s τ u₀ t * (s - uf s τ u₀ t)) t := by
  have hτne : τ ≠ 0 := hτ.ne'
  have hDne : denom s τ u₀ t ≠ 0 := (denom_pos s τ u₀ hu₀ hlt t).ne'
  -- derivative of the inner linear map `r ↦ 2 s r / τ`
  have hg : HasDerivAt (fun r => 2 * s * r / τ) (2 * s / τ) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * s)).div_const τ
  -- numerator `N r = s e^{2 s r / τ}`
  have hN : HasDerivAt (fun r => s * Real.exp (2 * s * r / τ))
      (s * (Real.exp (2 * s * t / τ) * (2 * s / τ))) t := (hg.exp).const_mul s
  -- denominator `D r = denom s τ u₀ r`, kept folded
  have hD : HasDerivAt (fun r => denom s τ u₀ r)
      (Real.exp (2 * s * t / τ) * (2 * s / τ)) t := by
    unfold denom
    exact ((hg.exp).sub_const 1).add_const (s / u₀)
  -- rewrite the target into the exact quotient-rule derivative `(N'D − ND')/D²`,
  -- then `HasDerivAt.div` matches up to defeq (`uf = N / D`)
  rw [show (2 / τ) * uf s τ u₀ t * (s - uf s τ u₀ t) =
      (s * (Real.exp (2 * s * t / τ) * (2 * s / τ)) * denom s τ u₀ t -
        s * Real.exp (2 * s * t / τ) * (Real.exp (2 * s * t / τ) * (2 * s / τ))) /
        denom s τ u₀ t ^ 2 by
    unfold uf; field_simp]
  exact hN.div hD hDne

end DlnDynamics
