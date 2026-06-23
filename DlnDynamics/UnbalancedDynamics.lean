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

Separating variables in this hyperbolic dynamics gives the **unbalanced learning-time
integral** (`unbalancedLearningTime_integral`), the `a ≠ b` analogue of Saxe Eq. `u_int`:

`∫_{u₀}^{u_f} du / (√(c₀² + 4u²)(s − u))
   = (1/√(c₀² + 4s²)) (arsinh((c₀²+4s u₀)/(2|c₀|(u₀−s))) − arsinh((c₀²+4s u_f)/(2|c₀|(u_f−s))))`,

so `t = τ · (that)` is the time for the overlap `u = ab` to travel from `u₀` to `u_f`. The
antiderivative is `unbalancedAntideriv`; its derivative is checked in
`hasDerivAt_unbalancedAntideriv` (the inverse-hyperbolic-sine `arsinh` handles either sign
of `c₀` uniformly). The balanced case `c₀ = 0` is `learningTime_integral`.
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

/-- Antiderivative of the separated unbalanced integrand `1/(√(c₀² + 4u²)(s − u))`
(Saxe Appendix A). With the conserved `c₀ = a² − b² ≠ 0`,
`F(u) = −arsinh((c₀² + 4 s u)/(2|c₀|(u − s))) / √(c₀² + 4 s²)`. The inverse hyperbolic
sine handles either sign of `c₀` uniformly (the `2|c₀|` inside makes `F` a genuine
antiderivative regardless of `sign c₀`). -/
noncomputable def unbalancedAntideriv (s c₀ u : ℝ) : ℝ :=
  -(Real.arsinh ((c₀ ^ 2 + 4 * s * u) / (2 * |c₀| * (u - s))) / Real.sqrt (c₀ ^ 2 + 4 * s ^ 2))

/-- `unbalancedAntideriv` is an antiderivative of the separated unbalanced integrand:
for `c₀ ≠ 0` and `x < s`, its derivative is `1/(√(c₀² + 4x²)(s − x))` (Saxe Appendix A).
This is the `a ≠ b` analogue of the logistic antiderivative behind `learningTime_integral`. -/
lemma hasDerivAt_unbalancedAntideriv {s c₀ : ℝ} (hc₀ : c₀ ≠ 0) {x : ℝ} (hxs : x < s) :
    HasDerivAt (unbalancedAntideriv s c₀)
      (1 / (Real.sqrt (c₀ ^ 2 + 4 * x ^ 2) * (s - x))) x := by
  have hsx : 0 < s - x := by linarith
  have hxsne : x - s ≠ 0 := sub_ne_zero.mpr (ne_of_lt hxs)
  have hcs : 0 < c₀ ^ 2 + 4 * s ^ 2 := by positivity
  have hcx : 0 < c₀ ^ 2 + 4 * x ^ 2 := by positivity
  have hP : 0 < Real.sqrt (c₀ ^ 2 + 4 * s ^ 2) := Real.sqrt_pos.mpr hcs
  have hQ : 0 < Real.sqrt (c₀ ^ 2 + 4 * x ^ 2) := Real.sqrt_pos.mpr hcx
  have habs : 0 < |c₀| := abs_pos.mpr hc₀
  have h2abs : (0 : ℝ) < 2 * |c₀| := mul_pos (by norm_num) habs
  have hden_ne : 2 * |c₀| * (x - s) ≠ 0 := mul_ne_zero h2abs.ne' hxsne
  -- the inner argument `z(u) = (c₀² + 4 s u)/(2|c₀|(u − s))` and its quotient-rule derivative
  have hnum : HasDerivAt (fun u => c₀ ^ 2 + 4 * s * u) (4 * s) x := by
    simpa using ((hasDerivAt_id x).const_mul (4 * s)).const_add (c₀ ^ 2)
  have hden : HasDerivAt (fun u => 2 * |c₀| * (u - s)) (2 * |c₀|) x := by
    simpa using ((hasDerivAt_id x).sub_const s).const_mul (2 * |c₀|)
  have hz := hnum.div hden hden_ne
  -- compose with `arsinh`, divide by `√(c₀² + 4s²)`, negate
  have harsinh := (Real.hasDerivAt_arsinh
      ((c₀ ^ 2 + 4 * s * x) / (2 * |c₀| * (x - s)))).comp x hz
  have hF := (harsinh.div_const (Real.sqrt (c₀ ^ 2 + 4 * s ^ 2))).neg
  -- simplify the quotient-rule velocity `Z'` (no `|c₀|² = c₀²` needed here)
  have hZ' : (4 * s * (2 * |c₀| * (x - s)) - (c₀ ^ 2 + 4 * s * x) * (2 * |c₀|))
        / (2 * |c₀| * (x - s)) ^ 2
      = -(Real.sqrt (c₀ ^ 2 + 4 * s ^ 2)) ^ 2 / (2 * |c₀| * (x - s) ^ 2) := by
    rw [Real.sq_sqrt hcs.le]
    have : |c₀| ≠ 0 := habs.ne'
    field_simp
    ring
  -- the nested square root collapses: `√(1 + z²) = √(c₀²+4s²)·√(c₀²+4x²)/(2|c₀|(s−x))`
  have hsqrt1z : Real.sqrt (1 + ((c₀ ^ 2 + 4 * s * x) / (2 * |c₀| * (x - s))) ^ 2)
      = Real.sqrt (c₀ ^ 2 + 4 * s ^ 2) * Real.sqrt (c₀ ^ 2 + 4 * x ^ 2) / (2 * |c₀| * (s - x)) := by
    rw [show (1 : ℝ) + ((c₀ ^ 2 + 4 * s * x) / (2 * |c₀| * (x - s))) ^ 2
          = (Real.sqrt (c₀ ^ 2 + 4 * s ^ 2) * Real.sqrt (c₀ ^ 2 + 4 * x ^ 2)
              / (2 * |c₀| * (s - x))) ^ 2 from ?_]
    · exact Real.sqrt_sq (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c₀)) hsx.le))
    · rw [show (Real.sqrt (c₀ ^ 2 + 4 * s ^ 2) * Real.sqrt (c₀ ^ 2 + 4 * x ^ 2)
              / (2 * |c₀| * (s - x))) ^ 2
            = (c₀ ^ 2 + 4 * s ^ 2) * (c₀ ^ 2 + 4 * x ^ 2) / (2 * |c₀| * (s - x)) ^ 2 from by
              rw [div_pow, mul_pow, Real.sq_sqrt hcs.le, Real.sq_sqrt hcx.le],
          show (2 * |c₀| * (s - x)) ^ 2 = 4 * c₀ ^ 2 * (s - x) ^ 2 from by
            rw [mul_pow, mul_pow, sq_abs]; ring,
          div_pow,
          show (2 * |c₀| * (x - s)) ^ 2 = 4 * c₀ ^ 2 * (x - s) ^ 2 from by
            rw [mul_pow, mul_pow, sq_abs]; ring]
      have hc2 : c₀ ≠ 0 := hc₀
      field_simp
      ring
  -- retarget the combinator velocity to the integrand `1/(√(c₀²+4x²)(s−x))`
  rw [show (1 : ℝ) / (Real.sqrt (c₀ ^ 2 + 4 * x ^ 2) * (s - x))
        = -((Real.sqrt (1 + ((c₀ ^ 2 + 4 * s * x) / (2 * |c₀| * (x - s))) ^ 2))⁻¹
            * ((4 * s * (2 * |c₀| * (x - s)) - (c₀ ^ 2 + 4 * s * x) * (2 * |c₀|))
                / (2 * |c₀| * (x - s)) ^ 2)
            / Real.sqrt (c₀ ^ 2 + 4 * s ^ 2)) from ?_]
  · exact hF
  · rw [hsqrt1z, hZ']
    have h1 : |c₀| ≠ 0 := habs.ne'
    have h2 : s - x ≠ 0 := hsx.ne'
    field_simp
    ring

/-- **Unbalanced learning-time integral** (Saxe Appendix A, the `a ≠ b` analogue of
Eq. `u_int`). Separating the hyperbolic dynamics `hyperbolic_dyn_sqrt`
`τ u' = √(c₀² + 4u²)(s − u)` (with the conserved `c₀ = a² − b² ≠ 0`) and integrating gives

`∫_{u₀}^{u_f} du / (√(c₀² + 4u²)(s − u))
   = (1/√(c₀² + 4s²)) (arsinh((c₀²+4 s u₀)/(2|c₀|(u₀−s))) − arsinh((c₀²+4 s u_f)/(2|c₀|(u_f−s))))`.

Multiplying by `τ` gives the time for the overlap `u = ab` to travel from `u₀` to `u_f`.
The balanced limit `c₀ = 0` is `learningTime_integral`. -/
theorem unbalancedLearningTime_integral {s c₀ : ℝ} (hc₀ : c₀ ≠ 0) {u₀ u_f : ℝ}
    (hf : u₀ ≤ u_f) (hfs : u_f < s) :
    ∫ u in u₀..u_f, 1 / (Real.sqrt (c₀ ^ 2 + 4 * u ^ 2) * (s - u))
      = (1 / Real.sqrt (c₀ ^ 2 + 4 * s ^ 2))
        * (Real.arsinh ((c₀ ^ 2 + 4 * s * u₀) / (2 * |c₀| * (u₀ - s)))
           - Real.arsinh ((c₀ ^ 2 + 4 * s * u_f) / (2 * |c₀| * (u_f - s)))) := by
  have hderiv : ∀ x ∈ Set.uIcc u₀ u_f, HasDerivAt (unbalancedAntideriv s c₀)
      (1 / (Real.sqrt (c₀ ^ 2 + 4 * x ^ 2) * (s - x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hf] at hx
    exact hasDerivAt_unbalancedAntideriv hc₀ (lt_of_le_of_lt hx.2 hfs)
  have hint : IntervalIntegrable (fun u => 1 / (Real.sqrt (c₀ ^ 2 + 4 * u ^ 2) * (s - u)))
      MeasureTheory.volume u₀ u_f := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact Continuous.continuousOn (by fun_prop)
    · intro x hx
      rw [Set.uIcc_of_le hf] at hx
      have hsx : 0 < s - x := by linarith [hx.2]
      exact (mul_pos (Real.sqrt_pos.mpr (by positivity)) hsx).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [unbalancedAntideriv]
  ring

end DlnDynamics
