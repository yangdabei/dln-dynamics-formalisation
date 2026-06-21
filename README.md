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

**Scope/honesty.** The matrix flow `wb_avg`, the SVD change of variables `wbo_dyn`
(given an SVD of `Σ³¹` *as a hypothesis*, `IsSVD`), and the per-mode `a_dyn`/`b_dyn`
(diagonal `S`, square case) are established — composed end-to-end as
`a_dyn_of_gradFlow`/`b_dyn_of_gradFlow`. On the orthogonal-mode manifold this reduces to
the scalar `ab_dyn` (`isABFlow_of_modeFlow`, `isABFlow_of_gradFlow_on_manifold`), closing
the chain `network loss → wb_avg → wbo_dyn → a_dyn/b_dyn → ab_dyn` into the conservation
law and closed form of Layers 1–2. The manifold reduction takes
membership-for-all-time as a hypothesis; the **forward-invariance in time** of the
manifold (Saxe's "remain parallel for all future time") is the one remaining gap in this
chain, an ODE-uniqueness argument (Phase D option 3).

**Deferred** (future work): forward-invariance of the manifold (Phase D option 3) and
**SVD existence** (Phase E, discharging the `IsSVD` hypothesis), plus the
rectangular-diagonal `S` generalization (see `PROGRESS.md`); the `t → ∞` limit
`u_f → s`, ODE uniqueness, and the depth-`N` generalization
`τ u' = (N−1) u^{2−2/(N−1)}(s − u)` (Eq. `deep_dyn`).

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
scripts/no_sorry.sh            sorry / axiom gate (also run in CI)
scripts/check_closed_form.py   numerical sanity check (ODE closed form)
scripts/check_svd_reduction.py numerical sanity check (change of vars + a_dyn)
```
