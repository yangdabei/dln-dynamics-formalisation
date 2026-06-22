import DlnDynamics.Basic

/-!
# The infinite-depth limit (Saxe Eqs. `inf_dyn`, `inf_tc`)

As the network depth `N_l → ∞`, the depth-`N` law `deep_dyn`
`τ u' = (N_l−1) u^{2−2/(N_l−1)} (s − u)` (`DeepDynamics.deep_dyn`) approaches the
infinite-depth dynamics (Saxe Eq. `inf_dyn`)

`τ u' = N_l u² (s − u)`,

because the per-mode nonlinearity `u^{2−2/(N_l−1)} → u²` (`deepNonlinearity_tendsto`).
This module also evaluates the associated learning-time integral (Saxe Eq. `inf_tc`):

`∫_{u₀}^{u_f} du / (u² (s − u)) = (1/s²) ln(u_f(s−u₀)/(u₀(s−u_f))) + 1/(s u₀) − 1/(s u_f)`,

so `t = (τ/N_l) · (that)`.

All on the paper's regime `0 < u₀ < s`.
-/

namespace DlnDynamics

open Filter Topology

/-- **The `inf_dyn` nonlinearity emerges from `deep_dyn` as `N_l → ∞`.** For a fixed
mode strength `u > 0`, the depth-`N` nonlinearity `u^{2 − 2/(N_l−1)}` tends to `u²` as
the depth `m = N_l − 1 → ∞` — i.e. `deep_dyn` limits to Saxe Eq. `inf_dyn`. -/
theorem deepNonlinearity_tendsto (u : ℝ) (hu : 0 < u) :
    Tendsto (fun m : ℕ => u ^ (2 - 2 / (m : ℝ))) atTop (𝓝 (u ^ 2)) := by
  have hexp : Tendsto (fun m : ℕ => 2 - 2 / (m : ℝ)) atTop (𝓝 2) := by
    have h0 : Tendsto (fun m : ℕ => 2 / (m : ℝ)) atTop (𝓝 0) := by
      have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (2 : ℝ)
      simpa only [mul_one_div, mul_zero] using this
    simpa using tendsto_const_nhds.sub h0
  have hcont : Tendsto (fun e : ℝ => u ^ e) (𝓝 2) (𝓝 (u ^ (2 : ℝ))) :=
    (Real.continuousAt_const_rpow hu.ne').tendsto
  have := hcont.comp hexp
  rwa [show u ^ (2 : ℝ) = u ^ 2 from by rw [← Real.rpow_natCast u 2]; norm_num] at this

/-- **Infinite-depth learning-time integral** (Saxe Eq. `inf_tc`): the separable
integral of `inf_dyn`, with antiderivative `(1/s²)(ln u − ln(s − u)) − 1/(s u)`,
`∫_{u₀}^{u_f} du/(u²(s − u)) = (1/s²) ln(u_f(s−u₀)/(u₀(s−u_f))) + 1/(s u₀) − 1/(s u_f)`.
Multiplying by `τ/N_l` gives the infinite-depth learning time. -/
theorem infLearningTime_integral (s u₀ u_f : ℝ) (hu₀ : 0 < u₀) (hf : u₀ ≤ u_f) (hfs : u_f < s) :
    ∫ u in u₀..u_f, 1 / (u ^ 2 * (s - u))
      = (1 / s ^ 2) * Real.log (u_f * (s - u₀) / (u₀ * (s - u_f)))
        + 1 / (s * u₀) - 1 / (s * u_f) := by
  have hs : 0 < s := hu₀.trans_le (hf.trans hfs.le)
  have hufpos : 0 < u_f := hu₀.trans_le hf
  have hsu0 : 0 < s - u₀ := by linarith [hu₀.trans_le (hf.trans hfs.le)]
  have hsuf : 0 < s - u_f := by linarith
  set F : ℝ → ℝ := fun u => (1 / s ^ 2) * (Real.log u - Real.log (s - u)) - 1 / s * u⁻¹ with hF
  have hderiv : ∀ x ∈ Set.uIcc u₀ u_f, HasDerivAt F (1 / (x ^ 2 * (s - x))) x := by
    intro x hx
    rw [Set.uIcc_of_le hf] at hx
    have hxpos : 0 < x := hu₀.trans_le hx.1
    have hsx : 0 < s - x := by linarith [hx.2]
    have hxne := hxpos.ne'
    have hsxne := hsx.ne'
    have hsne := hs.ne'
    have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxne
    have h2 : HasDerivAt (fun u => Real.log (s - u)) ((s - x)⁻¹ * (0 - 1)) x :=
      (Real.hasDerivAt_log hsxne).comp x ((hasDerivAt_const x s).sub (hasDerivAt_id x))
    have h3 := ((h1.sub h2).const_mul (1 / s ^ 2)).sub ((hasDerivAt_inv hxne).const_mul (1 / s))
    rw [hF, show (1 : ℝ) / (x ^ 2 * (s - x))
          = 1 / s ^ 2 * (x⁻¹ - (s - x)⁻¹ * (0 - 1)) - 1 / s * -(x ^ 2)⁻¹ from by
        field_simp; ring]
    exact h3
  have hint : IntervalIntegrable (fun u => 1 / (u ^ 2 * (s - u))) MeasureTheory.volume u₀ u_f := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
      (((continuous_pow 2).mul (continuous_const.sub continuous_id)).continuousOn)
    intro x hx
    rw [Set.uIcc_of_le hf] at hx
    have hxpos : 0 < x := hu₀.trans_le hx.1
    have hsx : 0 < s - x := by linarith [hx.2]
    show x ^ 2 * (s - x) ≠ 0
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [hF]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hufpos.ne' hsu0.ne',
    Real.log_mul hu₀.ne' hsuf.ne']
  field_simp
  ring

end DlnDynamics
