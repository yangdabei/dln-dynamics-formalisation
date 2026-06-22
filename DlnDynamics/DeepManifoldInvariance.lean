import DlnDynamics.DeepDynamics
import DlnDynamics.ManifoldInvariance

/-!
# Forward-invariance of the depth-`N` symmetric submanifold

The depth-`N` law `deep_dyn` (`DeepDynamics.lean`) and the reduction
`deep_dyn_of_gradFlow` (`DeepReduction.lean`) take the symmetric-submanifold condition
`aₗ(t) = c(t)` (all layer scalars equal) as a hypothesis *for all `t`*. This module
discharges it from an *initial* condition `aₗ(0) = c(0)`, via ODE uniqueness — the
depth-`N` scalar analog of `ManifoldInvariance` (whose abstract `eq_of_autonomous_ode`
is reused here).

The `m`-scalar deep flow `IsDeepFlow` is an autonomous polynomial ODE `ȧ = deepField a`
on `Fin m → ℝ`. The symmetric vector `(c,…,c)` (with `c` solving the reduced scalar flow
`IsDeepSymFlow`) is also a solution; agreeing at `t = 0`, uniqueness forces
`aₗ(t) = c(t)` for all `l, t` (`deep_manifold_invariant`).
-/

namespace DlnDynamics

open Finset

variable {m : ℕ}

/-- The autonomous vector field of the `m`-scalar deep flow `IsDeepFlow`:
`(deepField a)ₗ = (s − ∏ᵢ aᵢ)·(∏_{i≠l} aᵢ)/τ`. A polynomial, hence `C^∞`. -/
noncomputable def deepField (s τ : ℝ) (m : ℕ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun v l => (s - ∏ i, v i) * (∏ i ∈ univ.erase l, v i) / τ

/-- The deep field is `C^∞` (it is a polynomial in the coordinates). -/
theorem deepField_contDiff (s τ : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (deepField s τ m) := by
  unfold deepField
  apply contDiff_pi.2
  intro l
  apply ContDiff.div_const
  exact (contDiff_const.sub (contDiff_prod (fun i _ => contDiff_pi.1 contDiff_id i))).mul
    (contDiff_prod (fun i _ => contDiff_pi.1 contDiff_id i))

/-- **Forward-invariance of the symmetric submanifold.** If the layer scalars of an
`IsDeepFlow` solution all start equal to `c(0)` (with `c` solving the reduced scalar
flow `IsDeepSymFlow`), they stay equal to `c(t)` for all time. ODE uniqueness:
`(aₗ)` and the symmetric `(c,…,c)` solve the same autonomous `C^∞` ODE and agree at
`t = 0`. -/
theorem deep_manifold_invariant {s τ : ℝ} {a : Fin m → ℝ → ℝ} {c : ℝ → ℝ}
    (h : IsDeepFlow s τ a) (hc : IsDeepSymFlow s τ m c) (hinit : ∀ l, a l 0 = c 0) :
    ∀ l t, a l t = c t := by
  have hf : ∀ t, HasDerivAt (fun s => fun l => a l s) (deepField s τ m (fun l => a l t)) t :=
    fun t => hasDerivAt_pi.2 (fun l => h.ha l t)
  have hg : ∀ t, HasDerivAt (fun s => fun _ : Fin m => c s)
      (deepField s τ m (fun _ => c t)) t := by
    intro t
    apply hasDerivAt_pi.2
    intro l
    show HasDerivAt (fun s => c s) (deepField s τ m (fun _ => c t) l) t
    rw [show deepField s τ m (fun _ => c t) l = (s - c t ^ m) * c t ^ (m - 1) / τ from by
      simp only [deepField]
      rw [Finset.prod_const, Finset.prod_const, card_univ, Fintype.card_fin,
        Finset.card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin]]
    exact hc.ha t
  have h0 : (fun l => a l 0) = (fun _ : Fin m => c 0) := funext hinit
  exact fun l t => congrFun (eq_of_autonomous_ode (deepField_contDiff s τ m) hf hg h0 t) l

/-- **Depth-`N` law from an initial symmetric condition.** Combining
`deep_manifold_invariant` with `deep_dyn_of_deepFlow`: an `IsDeepFlow` mode whose layer
strengths start equal to a positive scalar solution `c` of the reduced flow has overall
strength `u = cᵐ` obeying Saxe Eq. `deep_dyn` — needing only the *initial* symmetric
condition `aₗ(0) = c(0)`, not symmetry for all `t`. -/
theorem deep_dyn_of_deepFlow_init {s τ : ℝ} (hm : 1 ≤ m) {a : Fin m → ℝ → ℝ} {c : ℝ → ℝ}
    (h : IsDeepFlow s τ a) (hc : IsDeepSymFlow s τ m c) (hinit : ∀ l, a l 0 = c 0)
    (hpos : ∀ t, 0 < c t) (t : ℝ) :
    HasDerivAt (fun r => c r ^ m)
      ((m : ℝ) * (c t ^ m) ^ (2 - 2 / (m : ℝ)) * (s - c t ^ m) / τ) t :=
  deep_dyn_of_deepFlow hm h (fun i t => deep_manifold_invariant h hc hinit i t) hpos t

end DlnDynamics
