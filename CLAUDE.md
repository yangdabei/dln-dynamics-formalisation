# DlnDynamics — project memory for Claude Code

Lean 4 + Mathlib formalization of the core analytical results of Saxe,
McClelland & Ganguli (2014), *Exact solutions to the nonlinear dynamics of
learning in deep linear neural networks* (arXiv:1312.6120). The compiled paper
is `saxe-2014.pdf` at the repo root.

## Scope (what is formalized)
- `DlnDynamics/Basic.lean` — the two-mode gradient flow `IsABFlow` (Saxe Eq.
  `ab_dyn`), the closed-form solution `uf` (Eq. `u_soln`), and `denom_pos`.
- `DlnDynamics/Conservation.lean` — `a² − b²` is a constant of motion
  (`ab_conserved`, Saxe §1.3).
- `DlnDynamics/ClosedForm.lean` — `uf` solves the reduced logistic ODE
  `τ u' = 2 u (s − u)` (`uf_hasDerivAt`, Eq. `sigmoidal_dyn`) with `uf 0 = u₀`.

Deferred, not yet formalized: the `t → ∞` limit `uf → s`, ODE uniqueness, and the
depth-`N` law (Eq. `deep_dyn`). Do not stub these; add them as real theorems when
the time comes.

## Conventions
- Paper regime `0 < u₀ < s`, `0 < τ` carried explicitly as hypotheses.
- Cite the Saxe equation label (`ab_dyn`, `sigmoidal_dyn`, `u_soln`) in each
  theorem's docstring.
- Skeleton-first: get a correct *statement* compiling before filling the proof.
  A wrong statement is worse than a visible gap.

## House rules
- No `sorry`, `admit`, `native_decide`, or new `axiom`s in committed code.
  `scripts/no_sorry.sh` enforces this and runs in CI.
- Standard Mathlib analysis tactics only; reach for `exact?` / `apply?` / Loogle /
  LeanSearch on lemma lookup. After ~3 failed approaches to a goal, stop and
  reassess rather than thrash.
- Numerically sanity-check any new closed form before proving it
  (`scripts/check_closed_form.py` is the template).

## Build / check
    lake exe cache get      # once: download prebuilt Mathlib oleans
    lake build              # build the library
    bash scripts/no_sorry.sh

`.mcp.json` configures `lean-lsp-mcp` for sub-second incremental goal-state
checking; prefer it over full rebuilds while iterating on a proof.
