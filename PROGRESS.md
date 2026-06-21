# Progress log

Running narrative of the formalization — what got done, what's next. Newest
session at the top. Reusable *lessons* (tactics, Mathlib gotchas, API) live in
`CLAUDE.md`; this file is the *story* and the plan.

## Next session — Phase B (SVD change of variables), then C/D/E

Layers 1–2 and **Layer-3 Phase A are done**: `IsABFlow` is a derived consequence
of gradient flow (scalar `L` and one-mode `Lsq`), and the full three-layer matrix
flow `wb_avg` is derived from gradient descent on `Ematrix` (`MatrixFlow.lean`).
Next is **Phase B** — the orthogonal change of variables `Σ³¹ = U S Vᵀ` (SVD
hypothesized) reducing `Ematrix` to `½‖S − W̄ᵇW̄ᵃ‖²` and `wb_avg` to `wbo_dyn`,
via Frobenius orthogonal invariance. Then C (column extraction → `a_dyn`), D
(invariant manifold → scalar `ab_dyn`), E (SVD existence). See the phased plan
below.

3. **Full matrix → SVD mode reduction (Layer 3, HARD).** Saxe §1.1. Reframed
   so the SVD is *isolated into one hypothesis* (Phase B) and the hard SVD
   *existence* (Phase E) can be built independently / deferred / upstreamed.

   Convention: `Wᵃ = W₂₁ : N₂×N₁` (input→hidden), `Wᵇ = W₃₂ : N₃×N₂`
   (hidden→output), map `y = Wᵇ Wᵃ x`, input correlation `Σ¹¹ = I` (whitening),
   input–output correlation `Σ³¹ : N₃×N₁`. Loss `E = ½‖Σ³¹ − Wᵇ Wᵃ‖²_F`.

   - **Phase A — matrix gradient flow → `wb_avg`** *(DONE)*. `MatrixFlow.lean`:
     `Ematrix` (entrywise `½ ∑ᵢⱼ (Σ³¹ − Wᵇ Wᵃ)ᵢⱼ²`), entry partials
     `hasDerivAt_Ematrix_fst/_snd`, `IsMatrixGradFlow`, and `matrixFlow_of_gradFlow`
     (`τ Ẇᵃ = Wᵇᵀ(Σ³¹ − Wᵇ Wᵃ)`, `τ Ẇᵇ = (Σ³¹ − Wᵇ Wᵃ)Wᵃᵀ`). Entry partials taken
     as directional derivatives along `Matrix.single k l 1`; bundled to the matrix
     ODE via `hasDerivAt_pi` (defeq, not `rw`).
   - **Phase B — orthogonal change of variables → `wbo_dyn`** *(LOW–MEDIUM,
     conceptual heart)*. Take an SVD `Σ³¹ = U S Vᵀ` (U,V orthogonal) **as a
     hypothesis**; substitute `Wᵃ = W̄ᵃ Vᵀ`, `Wᵇ = U W̄ᵇ`. Frobenius norm is
     orthogonally invariant (`‖U M Vᵀ‖_F = ‖M‖_F`, via `trace(MᵀM)` + cyclicity
     `trace_mul_cycle` + `UᵀU=I`, `VᵀV=I`), so `E = ½‖S − W̄ᵇ W̄ᵃ‖²` and the flow
     becomes `τ Ẇ̄ᵃ = W̄ᵇᵀ(S − W̄ᵇ W̄ᵃ)`, `τ Ẇ̄ᵇ = (S − W̄ᵇ W̄ᵃ)W̄ᵃᵀ`.
   - **Phase C — column/row extraction → `a_dyn`** *(MEDIUM)*. `S` diagonal; read
     off the per-mode vector ODEs with the competition sums `∑_{γ≠α} bᵞ(aᵅ·bᵞ)`.
     Index manipulation of `Matrix.mul` entries.
   - **Phase D — decoupled invariant manifold → `ab_dyn` (scalar)** *(HIGH)*. On
     init `aᵅ,bᵅ ∝ rᵅ` (orthonormal), cross dot-products stay 0, competition
     vanishes ⇒ scalar `ab_dyn` (already linked to Layers 1–2). Needs a
     forward-invariance argument for the manifold (ODE-flavored).
   - **Phase E — SVD existence (the build, HIGH, independent).** Discharges
     Phase B's hypothesis. Construct from the Hermitian spectral theorem on
     `G := Mᵀ M`:
       1. `G` Hermitian + PSD (`isHermitian_transpose_mul_self`,
          `posSemidef_conjTranspose_mul_self`); eigenvalues `dᵢ ≥ 0`
          (`eigenvalues_conjTranspose_mul_self_nonneg`).
       2. Spectral theorem `G = V D Vᵀ`, `V = eigenvectorUnitary`, orthogonal
          (`Matrix.IsHermitian.spectral_theorem`, `Analysis/Matrix/Spectrum.lean`).
       3. Singular values `σᵢ = Real.sqrt dᵢ` (scalar sqrt — no matrix sqrt needed).
       4. For `σᵢ>0`, `uᵢ := σᵢ⁻¹ • (M vᵢ)`; orthonormal since
          `⟨Mvᵢ,Mvⱼ⟩ = vᵢᵀ G vⱼ = dⱼ δᵢⱼ` *(MEDIUM)*.
       5. Extend `{uᵢ : σᵢ>0}` to an orthonormal basis of `ℝ^{N₃}`
          (`Orthonormal.exists_orthonormalBasis_extension`); assemble `U`
          *(MEDIUM–HIGH: the reindexing between `Fin m`, the support set, and
          eigenvector indices is the main bookkeeping sink)*.
       6. `M = U Σ Vᵀ` from `M vⱼ = σⱼ uⱼ` (σⱼ=0 ⇒ `Mvⱼ=0` since `‖Mvⱼ‖²=dⱼ=0`),
          i.e. `M V = U Σ`, then right-multiply by `Vᵀ`.
     Statement-design choice to settle skeleton-first: rectangular `Σ` (encode the
     diagonal cleanly — `Real.sqrt`-of-eigenvalues placed on a rect-diagonal) vs.
     the square `N₃=N₁` special case; orthogonality as `Uᵀ U = 1` vs.
     `∈ orthogonalGroup`. Candidate to contribute upstream to Mathlib.

   **Sequencing (chosen):** A → B with the SVD hypothesized. This gives an honest
   "gradient flow on the network loss, rewritten in the SVD basis, decouples"
   result fast; E is tackled independently later. Don't start with E (multi-session
   sink) — it blocks nothing if B carries the SVD as a hypothesis. Until E lands,
   the honest claim stays "given an SVD of Σ³¹, …".

**Backburner — the time / asymptotic analysis** (transition/escape-time scaling,
and the `t → ∞` limit `uf → s`). Explicitly deferred.

**Tooling note.** Start the session with `lean-lsp-mcp` loaded and run `lake build`
once up front to warm imports, so the sub-second `lean_goal` /
`lean_diagnostic_messages` loop is live.

## Session 2026-06-21 — Layer-3 plan + Phase A (matrix flow `wb_avg`)

**Done.**
- Planned Layer 3 in full (phased A–E, SVD isolated into a Phase-B hypothesis;
  detailed SVD-existence build for Phase E). Recorded above; committed `c4dd0a6`.
- **Phase A complete** (`DlnDynamics/MatrixFlow.lean`): derived the three-layer
  matrix flow `wb_avg` from gradient descent on the network square loss `Ematrix`.
  `hasDerivAt_Ematrix_fst/_snd` (entry partials `∂E/∂Wᵃₖₗ = −(Wᵇᵀ(Σ³¹−WᵇWᵃ))ₖₗ`,
  `∂E/∂Wᵇₖₗ = −((Σ³¹−WᵇWᵃ)Wᵃᵀ)ₖₗ`) and the capstone `matrixFlow_of_gradFlow`.
- Verified: clean `lake build` (8565 jobs); sorry-gate green; capstone
  `#print axioms = [propext, Classical.choice, Quot.sound]`.

**Method that worked (matrix calculus without matrix `fderiv`).** Entry partial =
directional derivative of the loss along `Matrix.single k l 1` at `0`, which makes
the loss a sum of squares *affine in `x`* → the Layer-1/2 squared-affine technique
lifts directly (no `Function.update`). Bundle the entrywise time-derivatives into
the matrix ODE via `hasDerivAt_pi` applied in *term mode* (`Matrix`'s normed
instance is `fast_instance% Pi.normedAddCommGroup`, defeq to `Pi` but not
syntactically — so `exact`/`apply` work, `rw` does not). Distilled into CLAUDE.md
(Proof tactics + Matrix API).

**Pitfalls (in CLAUDE.md).** `hasDerivAt_pi` won't `rw` on `Matrix` (instance
mismatch) — apply via defeq; `HasDerivAt.sum` gives sum-of-functions, bridge the
final `exact` with `simpa only [Finset.sum_apply]`; unannotated `x • realMatrix`
defaults the scalar to `ℕ` (`NontriviallyNormedField ℕ`) — write `fun (x : ℝ) =>`
and `single k l (1 : ℝ)`.

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
