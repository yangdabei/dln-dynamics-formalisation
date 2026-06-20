# DlnDynamics

A Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the core analytical results of

> A. M. Saxe, J. L. McClelland, S. Ganguli.
> *Exact solutions to the nonlinear dynamics of learning in deep linear neural
> networks.* ICLR 2014. [arXiv:1312.6120](https://arxiv.org/abs/1312.6120).

The compiled paper is included as [`saxe-2014.pdf`](saxe-2014.pdf).

## What is formalized

For a single decoupled input–output mode of strength `s`, learning timescale
`τ`, and the scalar weight projections `a, b : ℝ → ℝ`:

| Result | Statement | Saxe ref | Lean |
| --- | --- | --- | --- |
| Two-mode flow | `τ a' = b(s − ab)`, `τ b' = a(s − ab)` | Eq. `ab_dyn` | `IsABFlow` |
| Conservation | `a² − b²` is a constant of motion | §1.3 | `ab_conserved`, `ab_conserved_eq` |
| Closed form | `u_f(t) = s·e^{2st/τ} / (e^{2st/τ} − 1 + s/u₀)` | Eq. `u_soln` | `uf` |
| Reduced ODE | `u_f` solves `τ u' = 2u(s − u)`, with `u_f(0) = u₀` | Eq. `sigmoidal_dyn` | `uf_hasDerivAt`, `uf_zero` |

All results hold on the paper's regime `0 < u₀ < s`, `0 < τ`.

**Deferred** (future work): the `t → ∞` limit `u_f → s`, ODE uniqueness, and the
depth-`N` generalization `τ u' = (N−1) u^{2−2/(N−1)}(s − u)` (Eq. `deep_dyn`).

## Build

```sh
lake exe cache get   # download prebuilt Mathlib oleans (once)
lake build
```

Check there are no proof gaps:

```sh
bash scripts/no_sorry.sh
python scripts/check_closed_form.py   # numpy numerical cross-check
```

## Layout

```
DlnDynamics.lean               root, imports the three modules
DlnDynamics/Basic.lean         IsABFlow, denom, uf, denom_pos
DlnDynamics/Conservation.lean  ab_conserved, ab_conserved_eq
DlnDynamics/ClosedForm.lean    uf_zero, uf_hasDerivAt
scripts/no_sorry.sh            sorry / axiom gate (also run in CI)
scripts/check_closed_form.py   numerical sanity check
```
