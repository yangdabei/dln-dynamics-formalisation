# Progress log

Running narrative of the formalization — what got done, what's next. Newest
session at the top. Reusable *lessons* (tactics, Mathlib gotchas, API) live in
`CLAUDE.md`; this file is the *story* and the plan.

## Session 2026-06-22 — Phase E DONE (SVD existence, square full-rank case)

**Done.** `DlnDynamics/SVDExistence.lean` — *constructs* a singular value decomposition,
discharging the `IsSVD` hypothesis that Phase B carried. Full chain gap-free (`#print axioms`
= `[propext, Classical.choice, Quot.sound]`), `lake build` clean, no `sorry`.

**Scope: square, full-rank** (user-confirmed). `exists_isSVD_of_isUnit`: every *invertible*
square real `Sg` admits `Sg = U (diagonal σ) Vᵀ` with `U`,`V` orthogonal. Full rank is exactly
what lets the left factor be written explicitly — `U := Sg V (diagonal σ)⁻¹`, no orthonormal
completion (the basis-extension sink) needed. This is the square shape every consumer uses
(`ModeDynamics`, `ManifoldInvariance` all fix `U V : Matrix (Fin N)(Fin N) ℝ`, `S = diagonal σ`).

The construction (each step a named lemma, mirroring the standard proof + the numeric check):
- **Gram PD** (`posSemidef_transpose_mul_self`, `posDef_transpose_mul_self_of_isUnit`): `Sgᵀ Sg`
  is Hermitian PSD (`posSemidef_conjTranspose_mul_self` + `conjTranspose = transpose` over ℝ),
  and PD since `det(Sgᵀ Sg)=(det Sg)²≠0` via `PosSemidef.posDef_iff_det_ne_zero`.
- **Real spectral adapter** (`real_spectral`, `eigenvectorMatrix_orthogonal`): unfold Mathlib's
  `spectral_theorem` (`conjStarAlgAut`/`unitaryGroup`/`RCLike.ofReal` form) to plain
  `Sgᵀ Sg = V (diagonal d) Vᵀ` with `Vᵀ V = 1` (`Unitary.conjStarAlgAut_apply`,
  `Unitary.coe_star_mul_self`, `star = ᵀ` over ℝ); eigenvalues `d i>0` from `PosDef.eigenvalues_pos`.
- **Assemble** (`isSVD_of_spectral`): `σ i=√(d i)`, `U=Sg V (diagonal σ)⁻¹` (pointwise-inverse
  diagonal). `Uᵀ U = σ⁻¹ (Vᵀ V) D (Vᵀ V) σ⁻¹ = σ⁻¹ D σ⁻¹ = 1` and `U (diagonal σ) Vᵀ = Sg V Vᵀ = Sg`
  are **pure matrix-cancellation algebra** (the `SVDReduction.lean` regroup-and-cancel style).
- **End-to-end discharge** (`exists_mode_dynamics_of_gradFlow_of_isUnit`): compose with
  `a_dyn_of_gradFlow`/`b_dyn_of_gradFlow` (`hdiag := rfl`) ⇒ network gradient descent on an
  invertible `Sg` obeys `a_dyn`/`b_dyn` in *some* SVD frame, **with no SVD assumed**.

Numerics: `scripts/check_svd_existence.py` (stdlib + Jacobi eigensolver): `U diag(σ) Vᵀ = Sg`
to 5e-15, `VᵀV=1` to 2e-15, `UᵀU=1` to 1e-11, min singular value >0 (full rank confirmed).

**Deferred / next.** Phase E **general (rank-deficient) case** — zero singular values need an
orthonormal completion of `U` via `Orthonormal.exists_orthonormalBasis_extension` (with
`Fin N ↔ {σ>0} ↔ complement` reindexing and a `Matrix ↔ EuclideanSpace` bridge); separate
HIGH-risk milestone, not attempted. Also still open: general *unbalanced* manifold init
(Picard–Lindelöf), the `t→∞` limit `uf→s`, and the optional rectangular-diagonal `S`.

## Session 2026-06-22 — Phase D option 3 DONE (forward-invariance via ODE uniqueness)

**Done.** `DlnDynamics/ManifoldInvariance.lean` — forward-invariance *in time* of the
orthogonal-mode manifold (Saxe's *"`aᵅ` and `bᵅ` will remain parallel to `rᵅ` for all future
time"*), discharging option 1's manifold-for-all-`t` hypothesis. Full chain, gap-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`), `lake build` clean, no `sorry`.

The argument (each step a named lemma, mirroring the paper proof):
- **Lift** scalar `ab_dyn` solutions to barred matrices `aLift`/`bLift` (column/row `α` =
  `cα t • rᵅ`); `aMode_aLift`/`bMode_bLift` land them on the manifold.
- **Lift solves `wbo_dyn`** (`aLift_solves`/`bLift_solves`) — "option 1 run backwards": reuse
  `flow_a_entry`/`flow_b_entry` + `competition_vanishes` (orthonormality kills the competition).
- **Uniqueness** (`eq_of_autonomous_ode`, `trajectory_eq_lift`): package both matrix flows on the
  product state via `HasDerivAt.prodMk`; the field `flowField` is a matrix polynomial, hence
  `C^∞` (`flowField_contDiff`, proved entrywise) and locally Lipschitz on closed balls
  (`ContDiffOn.exists_lipschitzOnWith`); `ODE_solution_unique_of_mem_Ioo` on `Ioo (-T) T` for
  `T=|t|+1` ⇒ trajectory = lift ∀`t`.
- **Forward-invariance** (`manifold_forward_invariant`) reads membership off that equality.
- **Constructive balanced solution** (`uf_pos`, `isABFlow_sqrt_uf`): `a=b=√∘uf` solves `ab_dyn`
  via `HasDerivAt.sqrt` + `uf_hasDerivAt`. Headlines `isABFlow_of_modeFlow_of_init` /
  `isABFlow_of_gradFlow_of_init` are then **hypothesis-free** (only a balanced paper-regime init
  `aᵅ(0)=bᵅ(0)=√(u₀ α)·rᵅ`, `0<u₀ α<σ α`) — no manifold and no solution hypothesis.

Key gotcha (now in CLAUDE.md): matrix `ContDiff`/ODE lemmas need `open scoped
Matrix.Norms.Elementwise` (plain `open Matrix` does not register the folded-`Matrix` norm
instance; it is defeq to the `Pi` one matrix `HasDerivAt` already uses — no diamond). Numerics:
`scripts/check_manifold_invariance.py` (parallelism residual ~1e-14 under RK4).

**Deferred / next.** General *unbalanced* orthogonal-mode init needs scalar existence
(Picard–Lindelöf + global a-priori bound) — `manifold_forward_invariant` already takes scalar
solutions as a hypothesis, so this only upgrades the construction. Then **Phase E** — SVD
existence (discharge `IsSVD`). Remaining Phase-C cleanup: rectangular-diagonal `S`.

## Earlier plan — Phase D option 3 (forward-invariance, parallel), then E (SVD existence)

Layers 1–2 and **Layer-3 Phases A, B, C, and D-option-1 are done.** Phase A: the
matrix flow `wb_avg` from gradient descent (`MatrixFlow.lean`). **Phase B**
(`SVDReduction.lean`): the orthogonal change of variables `Σ³¹ = U S Vᵀ` (SVD
hypothesized via `IsSVD`) reducing `wb_avg` to the decoupled `wbo_dyn`
(`wbo_dyn_of_gradFlow`), with reusable Frobenius/trace orthogonal-invariance API
(`sum_sq_mul_orthogonal`) and loss invariance (`Ematrix_orthogonal_invariant`).
**Phase C** (`ModeDynamics.lean`): the per-mode vector ODEs `a_dyn`/`b_dyn` (column/row
extraction with explicit `∑_{γ≠α}` competition sums) in the square diagonal case
`N₃=N₁=N`, `S = diagonal σ`, plus end-to-end `a_dyn_of_gradFlow`/`b_dyn_of_gradFlow`.
**Phase D option 1** (`InvariantManifold.lean`): on the orthogonal-mode manifold the
competition vanishes and the modes reduce to the scalar `ab_dyn` (`IsABFlow`) —
`competition_vanishes`, `isABFlow_of_modeFlow`, and the full chain
`isABFlow_of_gradFlow_on_manifold` (network gradient descent ⇒ `IsABFlow`, hence
`Conservation`/`ClosedForm`), taking manifold-membership-for-all-t as a hypothesis.

Next is **Phase D option 3** — forward-invariance *in time* of the manifold (Saxe's
"straightforward to verify ... remain parallel to rᵅ for all future time"), via ODE
uniqueness, discharging option 1's manifold hypothesis. Handed to a **parallel session**
(`PHASE_D_OPTION3.md`, new file `ManifoldInvariance.lean`); HIGH risk. Then **Phase E** —
SVD existence, discharging the `IsSVD` hypothesis. Remaining Phase-C cleanup:
rectangular-diagonal `S`. See the phased plan below.

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
   - **Phase B — orthogonal change of variables → `wbo_dyn`** *(DONE,
     `SVDReduction.lean`)*. SVD `Σ³¹ = U S Vᵀ` taken as the hypothesis `IsSVD`
     (orthogonality `UᵀU=1`, `VᵀV=1`; reverse `UUᵀ=1`, `VVᵀ=1` derived via
     `mul_eq_one_comm_of_equiv`). Frobenius invariance `∑(UMVᵀ)²=∑M²`
     (`sum_sq_mul_orthogonal`) via the trace bridge `trace(MᵀM)=∑Mᵢⱼ²`
     (`trace_transpose_mul_self`) + `trace_mul_comm`/`trace_mul_cycle`; loss
     invariance `Ematrix_orthogonal_invariant`. Flow change of variables
     `change_of_vars_a`/`_b` → `wbo_dyn`/`wbo_dyn_of_gradFlow`
     (`τ Ẇ̄ᵃ = W̄ᵇᵀ(S − W̄ᵇ W̄ᵃ)`, `τ Ẇ̄ᵇ = (S − W̄ᵇ W̄ᵃ)W̄ᵃᵀ`). Derivative through a
     constant matrix factor: `HasDerivAt.matrix_mul_const`/`const_matrix_mul`.
   - **Phase C — column/row extraction → `a_dyn`/`b_dyn`** *(STARTED,
     `ModeDynamics.lean`)*. Square diagonal case `N₃=N₁=N`, `S=diagonal σ`: per-mode
     vectors `aMode` (column α), `bMode` (row α); entry competition identities
     `flow_a_entry`/`flow_b_entry` (full Gram sum split off the α term via
     `Finset.add_sum_erase`); the vector ODEs `a_dyn`/`b_dyn` with explicit
     `∑_{γ≠α}` competition; and the **end-to-end** `a_dyn_of_gradFlow`/
     `b_dyn_of_gradFlow` composing `wbo_dyn_of_gradFlow` (network gradient flow + SVD +
     diagonal `S` ⇒ the mode ODEs for `Wᵃ V`, `Uᵀ Wᵇ`). Remaining (optional):
     rectangular `S`. The link to scalar `ab_dyn` is Phase D.
   - **Phase D — decoupled invariant manifold → `ab_dyn` (scalar)** *(option 1 DONE,
     `InvariantManifold.lean`; option 3 in a parallel session)*. On init `aᵅ,bᵅ ∝ rᵅ`
     (orthonormal), cross dot-products are 0, competition vanishes ⇒ scalar `ab_dyn`.
     **Option 1 (done):** `competition_vanishes`, `isABFlow_of_modeFlow` (reduction,
     taking manifold-membership-for-all-t as a hypothesis), and the end-to-end
     `isABFlow_of_gradFlow_on_manifold` (network gradient descent + SVD + diagonal `S`
     + manifold ⇒ `IsABFlow`, hence `Conservation`/`ClosedForm`). **Option 3 (the hard
     part, deferred to a parallel session, `PHASE_D_OPTION3.md`):** forward-invariance
     *in time* of the manifold (the paper's "straightforward to verify ... remain
     parallel to rᵅ for all future time") via ODE uniqueness — discharges option 1's
     manifold hypothesis. New file `ManifoldInvariance.lean`.
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

## Session 2026-06-21 (cont.) — Phase D option 1 (invariant-manifold reduction to `ab_dyn`)

**Done.**
- **Phase D option 1 complete** (`DlnDynamics/InvariantManifold.lean`), formalizing Saxe
  §"The time course of learning" (arXiv lines 162–189), the reduction of the vector mode
  dynamics to the scalar `ab_dyn` on the orthogonal-mode manifold:
  `HasDerivAt.dotProduct_const` (project a vector derivative onto a constant vector);
  `competition_vanishes` (orthogonal modes don't compete — line 181); `isABFlow_of_modeFlow`
  (on the manifold, `wbo_dyn` reduces to `IsABFlow` for the scalar projections `aᵅ·rᵅ`,
  `bᵅ·rᵅ`); and the end-to-end `isABFlow_of_gradFlow_on_manifold` (network gradient
  descent + SVD + diagonal `S` + manifold ⇒ `IsABFlow`, hence `Conservation`/`ClosedForm`).
- The proof mirrors the paper: competition drops (orthonormality), the cooperative term
  `(σα − aᵅ·bᵅ)bᵅ` projects onto `rᵅ` to give `τ ȧ = b(σα − ab)`.
- Verified: clean `lake build` (8568 jobs); sorry-gate green; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for `isABFlow_of_modeFlow` and
  `isABFlow_of_gradFlow_on_manifold`.

**Scope honesty.** Option 1 takes manifold-membership-for-all-t (`hmemA`/`hmemB`) as an
explicit hypothesis. The forward-invariance *in time* (the paper's "straightforward to
verify ... remain parallel for all future time") is **option 3** — a separate ODE-uniqueness
argument, handed to a parallel session (`PHASE_D_OPTION3.md`), not yet formalized.

## Session 2026-06-21 (cont.) — Phase B (`wbo_dyn`) + Phase C start (`a_dyn`/`b_dyn`)

**Done.**
- **Phase B complete** (`DlnDynamics/SVDReduction.lean`): the SVD change of variables.
  `IsSVD` interface (orthogonality + factorization, with derived `hUU`/`hVV`);
  `trace_transpose_mul_self` (Frobenius² as a trace); `sum_sq_mul_orthogonal`
  (orthogonal invariance via `trace_mul_comm`/`trace_mul_cycle`);
  `Ematrix_orthogonal_invariant` (loss preserved); `HasDerivAt.matrix_mul_const`/
  `const_matrix_mul`; `change_of_vars_a`/`_b`; capstones `wbo_dyn` and
  `wbo_dyn_of_gradFlow` (compose with Phase A).
- **Phase C started** (`DlnDynamics/ModeDynamics.lean`): square diagonal case.
  `aMode`/`bMode` (column/row mode vectors); `mul_apply_eq_dot`/`_dot'`;
  `flow_a_entry`/`flow_b_entry` (per-entry competition identities); the per-mode
  vector ODEs `a_dyn`/`b_dyn` with explicit `∑_{γ≠α}` competition sums; and the
  end-to-end `a_dyn_of_gradFlow`/`b_dyn_of_gradFlow` (network gradient descent + SVD +
  diagonal `S` ⇒ the mode ODEs), completing the chain
  `network loss → wb_avg → wbo_dyn → a_dyn/b_dyn`.
- Verified: clean `lake build`; sorry-gate green; numerical pre-check
  (`scripts/check_svd_reduction.py`, pure stdlib: change-of-variables residual
  ~4e-12, `a_dyn` competition residual ~7e-15); `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` for `wbo_dyn_of_gradFlow`, `a_dyn`, `b_dyn`,
  `a_dyn_of_gradFlow`, `b_dyn_of_gradFlow`.

**Method.** The change of variables is at the *flow* level (only `UᵀU=1`/`VᵀV=1`
plus their square-matrix reverses); `wbo_dyn` is then `matrixFlow_of_gradFlow` with the
diagonal target, so the loss-invariance API (`sum_sq_mul_orthogonal`,
`Ematrix_orthogonal_invariant`) is the *honest "loss is preserved"* statement rather
than strictly on the critical path. Phase C reads off column/row α, splitting the full
Gram sum `∑_γ` into the `γ=α` self term and the `∑_{γ≠α}` competition with
`Finset.add_sum_erase`.

**Pitfalls (distilled into CLAUDE.md).** Rectangular `*` is heterogeneous `HMul`, so
`smul_mul_assoc`/`mul_smul_comm` don't fire — use `Matrix.smul_mul`/`Matrix.mul_smul`;
dot notation `h.myLemma` fails for a locally-defined `HasDerivAt.myLemma` (the type
unfolds to `HasFDerivAtFilter`) — call it qualified; `Σ` is a reserved token (can't name
a variable `Σ31`); orthogonality reverse via `Matrix.mul_eq_one_comm_of_equiv`.

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
