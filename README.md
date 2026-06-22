# DlnDynamics

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the core analytical results of

> A. M. Saxe, J. L. McClelland, S. Ganguli.
> *Exact solutions to the nonlinear dynamics of learning in deep linear neural
> networks.* ICLR 2014. [arXiv:1312.6120](https://arxiv.org/abs/1312.6120).

The compiled paper is included as [`saxe-2014.pdf`](saxe-2014.pdf).

## What is formalized

**Reduced single-mode dynamics.** For one decoupled input–output mode of strength
`s`, learning timescale `τ`, and the scalar weight projections `a, b : ℝ → ℝ`:

| Result | Statement | Saxe ref | Lean |
| --- | --- | --- | --- |
| Two-mode flow | `τ a' = b(s − ab)`, `τ b' = a(s − ab)` | Eq. `ab_dyn` | `IsABFlow` |
| Conservation | `a² − b²` is a constant of motion | §1.3 | `ab_conserved`, `ab_conserved_eq` |
| Closed form | `u_f(t) = s·e^{2st/τ} / (e^{2st/τ} − 1 + s/u₀)` | Eq. `u_soln` | `uf` |
| Reduced ODE | `u_f` solves `τ u' = 2u(s − u)`, with `u_f(0) = u₀` | Eq. `sigmoidal_dyn` | `uf_hasDerivAt`, `uf_zero` |
| Asymptotics | `u_f(t) → s` as `t → ∞` (sigmoid reaches the fixed point) | §"time course" | `uf_tendsto_atTop` |
| Learning time | `∫_{u₀}^{u_f} du/(2u(s−u)) = (1/2s) ln(u_f(s−u₀)/(u₀(s−u_f)))` | Eq. `u_int` | `learningTime_integral` |
| Unbalanced (`a≠b`) | `u = ab` obeys `τ u' = (a²+b²)(s−u) = √(c₀²+4u²)(s−u)`, `c₀ = a²−b²` | App. A `hyper_dyn` | `hyperbolic_dyn`, `hyperbolic_dyn_sqrt` |

(All on the paper's regime `0 < u₀ < s`, `0 < τ`.)

**Derivation from gradient descent.** `IsABFlow` and the matrix dynamics are
derived, not posited:

| Result | Statement | Saxe ref | Lean |
| --- | --- | --- | --- |
| Per-mode loss → ODE | gradient flow of `L = ½(s − ab)²` is `IsABFlow` | Eq. `ab_2en` | `isABFlow_of_gradFlow` |
| Network loss → loss | `½∑(yμ − ab·xμ)² = L + const` (whitening + correlation) | §1 | `Lsq_eq`, `isABFlow_of_networkGradFlow` |
| Matrix flow | grad. descent on `½‖Σ³¹ − WᵇWᵃ‖²` gives `τ Ẇᵃ = Wᵇᵀ(Σ³¹−WᵇWᵃ)`, `τ Ẇᵇ = (Σ³¹−WᵇWᵃ)Wᵃᵀ` | Eq. `wb_avg` | `matrixFlow_of_gradFlow` |
| SVD change of vars | given SVD `Σ³¹ = U S Vᵀ`, the flow decouples: `τ Ẇ̄ᵃ = W̄ᵇᵀ(S−W̄ᵇW̄ᵃ)`, `τ Ẇ̄ᵇ = (S−W̄ᵇW̄ᵃ)W̄ᵃᵀ` | Eq. `wbo_dyn` | `wbo_dyn_of_gradFlow` |
| Mode extraction | `S` diagonal ⇒ per-mode `τ ȧᵅ = (sᵅ−bᵅ·aᵅ)bᵅ − ∑_{γ≠α}(bᵞ·aᵅ)bᵞ` (and `b_dyn`) | Eqs. `a_dyn`, `b_dyn` | `a_dyn`, `b_dyn` |
| Manifold reduction | orthogonal-mode manifold ⇒ competition vanishes ⇒ scalar `τ a' = b(s−ab)` | §"time course", `ab_dyn` | `isABFlow_of_modeFlow` |

**Deeper multilayer dynamics — the depth-`N` law.** For an `N_l`-layer network
with `m = N_l − 1` weight matrices, each connectivity mode is `m` scalars
`a₁,…,aₘ` doing gradient descent on the deep energy `E = (1/2τ)(s − ∏ᵢ aᵢ)²`:

| Result | Statement | Saxe ref | Lean |
| --- | --- | --- | --- |
| Deep flow | `τ aₗ' = (s − ∏ᵢ aᵢ)·∏_{i≠l} aᵢ` | §"deeper", `multilayer_dyn` | `IsDeepFlow` |
| Conservation | `aᵢ² − aⱼ²` is a constant of motion (every depth) | §"deeper" | `deepFlow_conserved`, `deepFlow_conserved_eq` |
| Symmetric reduction | `a₁=⋯=aₘ` ⇒ common scalar obeys `τ a' = (s − aᵐ)aᵐ⁻¹` | §"deeper" | `IsDeepSymFlow`, `isDeepSymFlow_of_symmetric` |
| **Depth-`N` law** | `u = aᵐ` obeys `τ u' = (N_l−1) u^{2−2/(N_l−1)}(s − u)` | Eq. `deep_dyn` | `deep_dyn`, `deepSym_hasDerivAt` |
| `N_l = 3` check | the depth-`N` law collapses to `τ u' = 2u(s − u)` | Eq. `sigmoidal_dyn` | `deepSym_hasDerivAt_two` |
| Deep matrix flow | grad. descent on `½‖Σ³¹ − ∏W‖²` gives `τ Ẇₗ = (∏_{i>l}Wᵢ)ᵀ(Σ³¹−∏W)(∏_{i<l}Wᵢ)ᵀ` | Eq. `multilayer_dyn` | `multilayerFlow_of_gradFlow` |
| Change of vars | `Wₗ = R₍ₗ₊₁₎ diag(aₗ) Rₗᵀ`, orthogonal `Rₗ`, `Σ³¹ = R_m diag(σ) R₀ᵀ`: products telescope | §"deeper" | `prodDesc_telescope`, `aboveProd_factored`, `belowProd_factored` |
| Mode extraction | the matrix flow decouples — each mode `α` obeys the scalar `IsDeepFlow` with `s = σ_α` | §"deeper" | `isDeepFlow_of_gradFlow` |
| End to end | `N_l`-layer grad. descent ⇒ (sym. submanifold) `u = cᵐ` obeys `deep_dyn` | Eqs. `multilayer_dyn`→`deep_dyn` | `deep_dyn_of_gradFlow` |
| Forward-invariance | equal layer scalars at `t=0` stay equal ⇒ `deep_dyn` from an *initial* condition | §"deeper" | `deep_manifold_invariant`, `deep_dyn_of_deepFlow_init` |
| Infinite depth | nonlinearity `u^{2−2/(N_l−1)} → u²` (Eq. `inf_dyn`); learning time `∫du/(u²(s−u))` (Eq. `inf_tc`) | Eqs. `inf_dyn`, `inf_tc` | `deepNonlinearity_tendsto`, `infLearningTime_integral` |

**Scope/honesty.** The matrix flow `wb_avg`, the SVD change of variables `wbo_dyn`
(given an SVD of `Σ³¹` *as a hypothesis*, `IsSVD`), and the per-mode `a_dyn`/`b_dyn`
(diagonal `S`, square case) are established — composed end-to-end as
`a_dyn_of_gradFlow`/`b_dyn_of_gradFlow`. On the orthogonal-mode manifold this reduces to
the scalar `ab_dyn` (`isABFlow_of_modeFlow`, `isABFlow_of_gradFlow_on_manifold`), closing
the chain `network loss → wb_avg → wbo_dyn → a_dyn/b_dyn → ab_dyn` into the conservation
law and closed form of Layers 1–2. The **forward-invariance in time** of the
orthogonal-mode manifold is discharged via ODE uniqueness
(`ManifoldInvariance.lean`), and **SVD existence** for any square `Σ³¹` is
constructed (`SVDExistence.lean`, `exists_isSVD`), so the 3-layer chain is
gap-free end to end. The depth-`N` development is **complete** for equal-size square
layers: the scalar `deep_dyn` + conservation (`DeepDynamics.lean`), the matrix gradient
flow `multilayer_dyn` (`DeepMatrixFlow.lean`, Phase A), and the change of variables +
mode extraction (`DeepReduction.lean`, Phases B–C) compose into `deep_dyn_of_gradFlow`:
`N_l`-layer gradient descent ⇒ (on the symmetric submanifold) the depth-`N` law. The
per-layer diagonal-in-frame form is taken as a hypothesis (the depth-`N` analog of how
`InvariantManifold` takes manifold membership as a hypothesis); its forward-invariance
in time is deferred.

**Deferred** (future work): the unbalanced learning-*time* integral
`∫ du/(√(c₀²+4u²)(s−u))` (Appendix A — the `u`-*dynamics* is done, only the messy
hyperbolic integral remains); and the rectangular-diagonal `Σ³¹` generalization
(non-square SVD reduction; see `PROGRESS.md`). The analytical core of the paper is
otherwise complete.

## Build

```sh
lake exe cache get   # download prebuilt Mathlib oleans (once)
lake build
```

Check there are no proof gaps:

```sh
bash scripts/no_sorry.sh
python3 scripts/check_closed_form.py   # numerical cross-check (pure stdlib)
```

## Layout

```
DlnDynamics.lean               root, imports the modules below
DlnDynamics/Basic.lean         IsABFlow, denom, uf, denom_pos
DlnDynamics/Conservation.lean  ab_conserved, ab_conserved_eq
DlnDynamics/ClosedForm.lean    uf_zero, uf_hasDerivAt
DlnDynamics/GradientFlow.lean  L, IsABGradFlow, isABFlow_of_gradFlow      (Layer 1)
DlnDynamics/Network.lean       Lsq, Lsq_eq, isABFlow_of_networkGradFlow   (Layer 2)
DlnDynamics/MatrixFlow.lean    Ematrix, matrixFlow_of_gradFlow            (Layer 3, Phase A)
DlnDynamics/SVDReduction.lean  IsSVD, sum_sq_mul_orthogonal, wbo_dyn_of_gradFlow  (Layer 3, Phase B)
DlnDynamics/ModeDynamics.lean  aMode/bMode, a_dyn/b_dyn, a_dyn_of_gradFlow (Layer 3, Phase C)
DlnDynamics/InvariantManifold.lean competition_vanishes, isABFlow_of_modeFlow (Layer 3, Phase D opt 1)
DlnDynamics/ManifoldInvariance.lean manifold_forward_invariant            (Layer 3, Phase D opt 3)
DlnDynamics/SVDExistence.lean  exists_isSVD, exists_mode_dynamics_of_gradFlow (Layer 3, Phase E)
DlnDynamics/DeepDynamics.lean  IsDeepFlow, deepFlow_conserved, deep_dyn   (depth-N law, Eq. deep_dyn)
DlnDynamics/DeepMatrixFlow.lean prodDesc, prodDesc_telescope, multilayerFlow_of_gradFlow (depth-N Phase A, Eq. multilayer_dyn)
DlnDynamics/DeepReduction.lean above/belowProd_factored, isDeepFlow_of_gradFlow, deep_dyn_of_gradFlow (depth-N Phases B-C)
DlnDynamics/TimeEquation.lean  uf_tendsto_atTop, learningTime_integral   (learning timescale, Eq. u_int)
DlnDynamics/InfiniteDepth.lean deepNonlinearity_tendsto, infLearningTime_integral (N_l→∞ limit, Eqs. inf_dyn/inf_tc)
DlnDynamics/UnbalancedDynamics.lean hyperbolic_dyn, hyperbolic_dyn_sqrt   (unbalanced a≠b, Appendix A)
DlnDynamics/DeepManifoldInvariance.lean deep_manifold_invariant, deep_dyn_of_deepFlow_init (depth-N forward-invariance)
scripts/no_sorry.sh            sorry / axiom gate (also run in CI)
scripts/check_closed_form.py   numerical sanity check (ODE closed form)
scripts/check_svd_reduction.py numerical sanity check (change of vars + a_dyn)
```
