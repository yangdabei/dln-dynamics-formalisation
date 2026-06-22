import DlnDynamics.Basic

/-!
# The learning timescale (Saxe Eqs. `u_int`, asymptotics)

The closed form `uf` (Saxe Eq. `u_soln`) describes the time course of a mode's
strength. This module formalizes the two time-equation facts of Saxe §"time course":

* `uf_tendsto_atTop` — the sigmoid asymptotes to the fixed point: `u_f(t) → s` as
  `t → ∞` (the product of weight magnitudes converges to the correlation strength);
* `learningTime_integral` — the separable learning-time integral (Saxe Eq. `u_int`):
  `∫_{u₀}^{u_f} du / (2u(s−u)) = (1/2s) ln(u_f(s−u₀)/(u₀(s−u_f)))`,
  so `t = τ · (that)` is the time to travel from `u₀` to `u_f`.

All on the paper's regime `0 < u₀ < s`, `0 < τ`.
-/

namespace DlnDynamics

open Filter Topology

/-- `uf` written with a *decaying* exponential, isolating the `t → ∞` behaviour:
`u_f(t) = s / (1 + (s/u₀ − 1) e^{−2 s t / τ})`. -/
lemma uf_eq_div_one_add (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (t : ℝ) :
    uf s τ u₀ t = s / (1 + (s / u₀ - 1) * Real.exp (-(2 * s * t / τ))) := by
  have hexp : Real.exp (2 * s * t / τ) ≠ 0 := (Real.exp_pos _).ne'
  have hd : denom s τ u₀ t ≠ 0 := (denom_pos s τ u₀ hu₀ hlt t).ne'
  have hkey : 1 + (s / u₀ - 1) * Real.exp (-(2 * s * t / τ))
      = denom s τ u₀ t * Real.exp (-(2 * s * t / τ)) := by
    unfold denom
    rw [Real.exp_neg]
    field_simp
    ring
  unfold uf
  rw [hkey, Real.exp_neg]
  field_simp

/-- **Asymptotics of the learning curve** (Saxe §"time course"): the mode strength
`u_f(t)` approaches the fixed point `s` as `t → ∞`. -/
theorem uf_tendsto_atTop (s τ u₀ : ℝ) (hu₀ : 0 < u₀) (hlt : u₀ < s) (hτ : 0 < τ) :
    Tendsto (uf s τ u₀) atTop (𝓝 s) := by
  -- the exponent `−2 s t / τ → −∞`, so `e^{−2 s t / τ} → 0`
  have hs : 0 < s := hu₀.trans hlt
  have hslope : Tendsto (fun t : ℝ => 2 * s * t / τ) atTop atTop := by
    have heq : (fun t : ℝ => 2 * s * t / τ) = fun t => (2 * s / τ) * t := by funext t; ring
    rw [heq]
    exact Tendsto.const_mul_atTop (by positivity) tendsto_id
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-(2 * s * t / τ))) atTop (𝓝 0) := by
    simp only [Real.exp_neg]
    exact (Real.tendsto_exp_atTop.comp hslope).inv_tendsto_atTop
  have hdenom : Tendsto (fun t : ℝ => 1 + (s / u₀ - 1) * Real.exp (-(2 * s * t / τ)))
      atTop (𝓝 1) := by
    have := (hexp0.const_mul (s / u₀ - 1)).const_add 1
    simpa using this
  have hlim : Tendsto (fun t : ℝ => s / (1 + (s / u₀ - 1) * Real.exp (-(2 * s * t / τ))))
      atTop (𝓝 (s / 1)) := tendsto_const_nhds.div hdenom one_ne_zero
  rw [div_one] at hlim
  exact hlim.congr (fun t => (uf_eq_div_one_add s τ u₀ hu₀ hlt t).symm)

/-- **Learning-time integral** (Saxe Eq. `u_int`): the separable integral of the
reduced logistic, with antiderivative `(1/2s)(ln u − ln(s − u))`,
`∫_{u₀}^{u_f} du/(2u(s − u)) = (1/2s) ln(u_f(s − u₀) / (u₀(s − u_f)))`.
Multiplying by `τ` gives the time `t` for the mode strength to travel from `u₀` to
`u_f` along the closed-form solution `uf`. -/
theorem learningTime_integral (s u₀ u_f : ℝ) (hu₀ : 0 < u₀) (hf : u₀ ≤ u_f) (hfs : u_f < s) :
    ∫ u in u₀..u_f, 1 / (2 * u * (s - u))
      = (1 / (2 * s)) * Real.log (u_f * (s - u₀) / (u₀ * (s - u_f))) := by
  have hs : 0 < s := hu₀.trans_le (hf.trans hfs.le)
  have hufpos : 0 < u_f := hu₀.trans_le hf
  have hsu0 : 0 < s - u₀ := by linarith [hu₀.trans_le (hf.trans hfs.le)]
  have hsuf : 0 < s - u_f := by linarith
  set F : ℝ → ℝ := fun u => (1 / (2 * s)) * (Real.log u - Real.log (s - u)) with hF
  have hderiv : ∀ x ∈ Set.uIcc u₀ u_f, HasDerivAt F (1 / (2 * x * (s - x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hf] at hx
    have hxpos : 0 < x := hu₀.trans_le hx.1
    have hsx : 0 < s - x := by linarith [hx.2]
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxpos.ne'
    have h2 : HasDerivAt (fun u => Real.log (s - u)) ((s - x)⁻¹ * (0 - 1)) x :=
      (Real.hasDerivAt_log hsx.ne').comp x ((hasDerivAt_const x s).sub (hasDerivAt_id x))
    have h3 := (h1.sub h2).const_mul (1 / (2 * s))
    have hxne := hxpos.ne'
    have hsxne := hsx.ne'
    have hsne := hs.ne'
    rw [hF, show (1 : ℝ) / (2 * x * (s - x)) = 1 / (2 * s) * (x⁻¹ - (s - x)⁻¹ * (0 - 1)) from by
      field_simp; ring]
    exact h3
  have hint : IntervalIntegrable (fun u => 1 / (2 * u * (s - u))) MeasureTheory.volume u₀ u_f := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
      ((continuous_const.mul continuous_id).mul (continuous_const.sub continuous_id)).continuousOn
    intro x hx
    rw [Set.uIcc_of_le hf] at hx
    have hxpos : 0 < x := hu₀.trans_le hx.1
    have hsx : 0 < s - x := by linarith [hx.2]
    show 2 * x * (s - x) ≠ 0
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [hF]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hufpos.ne' hsu0.ne',
    Real.log_mul hu₀.ne' hsuf.ne']
  ring

end DlnDynamics

