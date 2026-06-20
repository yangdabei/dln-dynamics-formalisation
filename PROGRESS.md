# Progress log

Running narrative of the formalization — what got done, what's next. Newest
session at the top. Reusable *lessons* (tactics, Mathlib gotchas, API) live in
`CLAUDE.md`; this file is the *story* and the plan.

## Next session — full matrix → SVD mode reduction (Layer 3), or asymptotics

Layers 1–2 below are **done**: `IsABFlow` is now a *derived* consequence of
gradient flow, both on the abstract per-mode loss `L` and on the one-mode
network's empirical square loss `Lsq`. The remaining gap to a true
"derivation from the deep linear network" is Layer 3 — the matrix dynamics and
the SVD change of variables that decouples the modes.

3. **Full matrix → SVD reduction (HARD, deferred).** Saxe §1.1: the matrix flow
   `wb_avg` (`τ Ẇᵃ = Wᵇᵀ(Σ³¹ − WᵇWᵃ)`, `τ Ẇᵇ = (Σ³¹ − WᵇWᵃ)Wᵃᵀ` under `Σ¹¹=I`),
   the SVD `Σ³¹ = U S Vᵀ`, the change of variables `Wᵃ = W̄ᵃ Vᵀ`, `Wᵇ = U W̄ᵇ`
   (Eq. `wbo_dyn`), then the orthogonal/decoupled **invariant manifold**
   (`aᵅ·bᵝ = 0` for `α≠β`) on which the cross-mode competition terms vanish and
   each mode obeys the scalar pair `ab_dyn`. Blockers: Mathlib has **no SVD
   factorization** (only `LinearMap.singularValues`); needs the symmetric spectral
   theorem + the invariant-manifold argument. Budget for building SVD. Until then,
   the honest claim is "gradient flow of the *per-mode* square loss ⇒ `ab_dyn`",
   not the matrix→mode reduction.

**Backburner — the time / asymptotic analysis** (transition/escape-time scaling,
and the `t → ∞` limit `uf → s`). Explicitly deferred.

**Tooling note.** Start the session with `lean-lsp-mcp` loaded and run `lake build`
once up front to warm imports, so the sub-second `lean_goal` /
`lean_diagnostic_messages` loop is live.

## Session 2026-06-20 (cont.) — `IsABFlow` derived from gradient flow + network loss

**Done — closed the "posited ODE" seam for a single mode.** `IsABFlow` is no
longer only a hypothesis; it is now produced by gradient descent.

- `DlnDynamics/GradientFlow.lean` (Layer 1) — per-mode loss `L s a b = ½(s−ab)²`
  (Eq. `ab_2en`), its partials `hasDerivAt_L_fst/_snd` (`∂ₐL = −b(s−ab)`,
  `∂_bL = −a(s−ab)`), the per-coordinate gradient-flow predicate `IsABGradFlow`
  (`τ a' = −∂ₐL`, `τ b' = −∂_bL`), and **`isABFlow_of_gradFlow`**: that flow *is*
  `IsABFlow` (Eq. `ab_2en` ⇒ Eq. `ab_dyn`).
- `DlnDynamics/Network.lean` (Layer 2) — one-mode network square loss
  `Lsq a b = ½ ∑μ (yμ − ab xμ)²`; **`Lsq_eq`**: under whitening `∑xμ²=1` and mode
  correlation `∑xμyμ=s`, `Lsq a b = L s a b + const` (const = `½∑yμ² − ½s²`);
  partials `hasDerivAt_Lsq_fst/_snd` (constant drops via `.add_const`); and
  **`isABFlow_of_networkGradFlow`**: gradient flow on the network's empirical loss
  ⇒ `IsABFlow`.
- Design choices (confirmed with user): per-coordinate `HasDerivAt` partials over
  abstract `gradient` on ℝ² (avoids the inner-product-space-on-a-product wrinkle —
  raw `ℝ×ℝ` carries the sup-norm, not an inner product); finite-sample data
  `x y : Fin P → ℝ` over abstract moments (matches the paper's `∑_μ`).
- Verified: clean `lake build`; sorry-gate green; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for both capstones; numerical
  pre-check of `Lsq = L + const` (max residual ~7e-15 over 10k trials,
  pure-stdlib). `IsABFlow`, and hence `Conservation`/`ClosedForm`, unchanged —
  the new modules sit *above* them and supply `IsABFlow` as a conclusion.

**Scope honesty.** This derives `ab_dyn` from the *per-mode* square loss. The
genuine matrix→mode reduction (SVD, decoupled invariant manifold) is Layer 3 and
remains deferred (no SVD factorization in Mathlib).

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
