# Progress log

Running narrative of the formalization — what got done, what's next. Newest
session at the top. Reusable *lessons* (tactics, Mathlib gotchas, API) live in
`CLAUDE.md`; this file is the *story* and the plan.

## Next session — derive the ODEs from the deep linear net toy model

**Goal: make `IsABFlow` a *derived consequence* of gradient flow on Saxe's deep
linear network, not a posited hypothesis.** Today the repo is a verified theory of
the *reduced ODEs*; the network appears only in docstrings. `IsABFlow` is the seam
to close.

Ladder (do Layer 1 first; it is small and self-contained):

1. **Per-mode loss → ODE.** Define the projected single-mode square loss
   `L a b = ½ (s − a b)²` and prove gradient flow `τ a' = −∂_a L`, `τ b' = −∂_b L`
   (timescale `τ = 1/λ`) gives exactly `IsABFlow s τ a b`:
   `∂_a L = −b (s − a b)` ⇒ `τ a' = b (s − a b)`, and symmetrically for `b`.
   This converts `IsABFlow` from a hypothesis into a theorem for one mode. Use
   `gradient` / `HasGradientAt` (or just `HasDerivAt` in each coordinate) — see the
   forward pointers in `CLAUDE.md`'s API section.

2. **Derive the per-mode loss from the network.** One-mode linear map `ŷ = a b x`,
   square loss with whitened input (`E[x²]=1`), mode correlation `s` ⇒
   `L a b = ½ (s − a b)² + const`. Connects the forward pass + square loss to §1.

3. **(later) Full matrix → SVD reduction.** Factor matrices `W₂₁, W₃₂`, whitening
   `Σ¹¹ = I`, SVD of `Σ³¹`, the change of variables that decouples the modes
   (Saxe §1.1). Needs the symmetric spectral theorem; Mathlib has no SVD
   *factorization* — budget for building it.

**Backburner — the time / asymptotic analysis** (transition/escape-time scaling,
and the `t → ∞` limit `uf → s`). Explicitly deferred; do not start these next
session.

**Tooling note.** Start the session with `lean-lsp-mcp` loaded and run `lake build`
once up front to warm imports, so the sub-second `lean_goal` /
`lean_diagnostic_messages` loop is live. This session ran blind on ~90 s `lake
build` cycles, which is what made the pitfalls below expensive.

## Session 2026-06-20 — bootstrap + Saxe core dynamics

**Done — first formalization, end to end.**
- Repo created (`dln-dynamics-formalisation`, public), Lean 4.31.0 + Mathlib
  v4.31.0 (`math-lax` template). Paper PDF committed; arXiv TeX source gitignored.
- `DlnDynamics/Basic.lean` — `IsABFlow` (coupled two-mode ODE, Eq. `ab_dyn`),
  `denom`, `uf` (closed form, Eq. `u_soln`), `denom_pos`.
- `DlnDynamics/Conservation.lean` — `ab_conserved`, `ab_conserved_eq`
  (`a² − b²` is a constant of motion, §1.3).
- `DlnDynamics/ClosedForm.lean` — `uf_zero`, `uf_hasDerivAt`
  (`uf` solves `τ u' = 2 u (s − u)`, Eq. `sigmoidal_dyn`), regime `0 < u₀ < s`,
  `0 < τ`.
- Verified: clean `lake build`; sorry-free; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for all five theorems; numerical
  cross-check (`scripts/check_closed_form.py`, ODE residual ~1e-9); CI green.
- Tooling: CLAUDE.md (Irving-style workflow + MCP/`lake`-fallback section),
  `.mcp.json` (`lean-lsp-mcp`), `scripts/no_sorry.sh`, CI, README.

**Scope honesty.** This is a verified theory of the *reduced ODEs*. The neural
network is not in the Lean content — `IsABFlow` *posits* the equations rather than
deriving them from a loss gradient. Closing that is next session's goal.

**Pitfalls** (distilled into `CLAUDE.md` → Proof tactics):
- Derivative combinators build the function at the `Pi` level (`a*a`, `c/d`), so
  `convert` fails on the function argument — use `rw` value + `exact` (defeq).
- `convert … using 1` doesn't reliably expose the scalar derivative equation for
  `HasDerivAt`; a bare `_` derivative placeholder fails to synthesize against a
  `def` function; `field_simp` sometimes closes the goal (so a trailing `ring`
  errors "no goals"); `.pow 2` drags in `Nat.cast` noise.
- Ran without the MCP loop — every fix cost a ~90 s rebuild. Grepping Mathlib
  source for exact lemma signatures was what actually unblocked things.
