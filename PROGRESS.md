# Progress log

Running narrative of the formalization — what got done, what's next. Newest
session at the top. Reusable *lessons* (tactics, Mathlib gotchas, API) live in
`CLAUDE.md`; this file is the *story* and the plan.

## Session 2026-06-22 — Depth-`N` MATRIX REDUCTION COMPLETE (Phases B–C: change of variables → IsDeepFlow)

**Done.** `DlnDynamics/DeepReduction.lean` — the depth-`N` analog of Phases B–C, connecting the
matrix flow `multilayer_dyn` to the scalar `IsDeepFlow`. **Milestone 1 (full depth-`N` matrix
reduction) is complete** for equal-size square layers. Gap-free (`#print axioms` =
`[propext, Classical.choice, Quot.sound]` on `isDeepFlow_of_gradFlow`, `deep_dyn_of_gradFlow`,
`flowval_conj`), `lake build` clean, no `sorry`. The mode-decoupling identity numerically
cross-checked (residual ~5e-12 over random orthogonal frames / depths).

User chose "continue Phase B–C now". The chain: `IsDeepMatrixGradFlow` (gradient descent) →
`multilayerFlow_of_gradFlow` (Eq. 244) → change of variables `Wₗ = R₍ₗ₊₁₎ diag(aₗ) Rₗᵀ` →
per-mode `IsDeepFlow` → (symmetric submanifold) `deep_dyn`.

- **`prodDesc_diagonal`** — `∏ diag(aᵢ) = diag(∏ aᵢ)` (induction + `prodDesc_succ`).
- **Sub-range telescoping.** `belowProd_factored : ∏_{i<l} Wᵢ = Rₗ diag(∏_{i<l} aᵢ) R₀ᵀ` and
  `aboveProd_factored : ∏_{i>l} Wᵢ = R_m diag(∏_{i>l} aᵢ) R₍ₗ₊₁₎ᵀ`. The take/drop prefix/suffix
  products have no clean `ofFn`-reindexing, so proven via one-step recursions `belowProd_succ`
  (`List.cons_getElem_drop_succ`) / `aboveProd_succ` (`List.prod_take_succ`) + `Fin.induction` /
  `Fin.reverseInduction`; `Finset.Iio`/`Ioi` successor shifts handled per step.
- **`flowval_conj`** — the mode decoupling: `(R₍ₗ₊₁₎)ᵀ · [aboveᵀ(Σ³¹−∏W)belowᵀ] · Rₗ` collapses
  (4 orthogonal-pair cancellations + 3 diagonal merges) to `diag(α ↦ ∏_{i>l}·(σα−∏)·∏_{i<l})` —
  the diagonal of scalar deep-flow velocities.
- **`hasDerivAt_conj_apply`** — extracts a scalar entry's derivative from a matrix `HasDerivAt`
  through constant conjugating factors (entrywise sum + `Finset.sum_apply` bridge).
- **`isDeepFlow_of_gradFlow`** — assembles the above: each mode `α` of the factored gradient flow
  obeys `IsDeepFlow (σ α) τ`. **`deep_dyn_of_gradFlow`** composes with `deep_dyn_of_deepFlow`:
  `N_l`-layer gradient descent ⇒ `deep_dyn` on the symmetric submanifold, end to end.

Diagonality-in-frame is a hypothesis (the depth-`N` analog of `InvariantManifold`'s manifold
membership). **Next:** the time equation (`t→∞` limit + `u_int`), the infinite-depth limit
(`inf_dyn`/`inf_tc`), and symmetric-manifold forward-invariance in time.

## Session 2026-06-22 — Depth-`N` Phase A DONE (matrix flow `multilayer_dyn` from gradient descent)

**Done.** `DlnDynamics/DeepMatrixFlow.lean` — derives the `N_l`-layer matrix gradient flow
(Saxe Eq. `multilayer_dyn`) from per-entry gradient descent on `E = ½‖Σ³¹ − ∏W‖²` (equal-size
square `n×n` layers, `m = N_l − 1` weight matrices). Gap-free (`#print axioms` =
`[propext, Classical.choice, Quot.sound]` on `multilayerFlow_of_gradFlow`, `prodDesc_telescope`),
`lake build` clean, no `sorry`. Matrix gradient numerically cross-checked against finite
differences (residual ~2e-7).

The user chose "derive Eq. 244 first" (over positing it / over the reduction first), equal-square
layers, diagonality-as-hypothesis. The heaviest, most index-intensive part; built bottleneck-first:

- **Ordered product.** Matrices don't commute ⇒ `prodDesc W := (List.ofFn W).reverse.prod`
  (descending `W_{m-1}⋯W₀`), NOT `Finset.prod`. `prodDesc_succ` peels the top factor.
- **Telescoping (Phase B core, proven ahead).** `prodDesc_telescope`:
  `∏(R₍ᵢ₊₁₎ W̄ᵢ Rᵢᵀ) = R_m (∏W̄ᵢ) R₀ᵀ` — the `Rₗ` change of variables cancels every interior
  orthogonal `R`. Induction on `m` (auto-generalizes the `m`-dependent `R, Wb`); the only
  non-trivial step per layer is `Cᵀ C = 1` regroup-and-cancel.
- **Product split (Phase A crux).** `prodDesc_update : prodDesc (update W l V) = aboveProd · V ·
  belowProd` via `List.ofFn (update …) = (ofFn W).set ↑l V`, `reverse_set`, `List.prod_set` (all
  by `List.ext_getElem` + `omega`). Makes the loss affine in one layer's perturbation.
- **Unified bilinear derivative.** `hasDerivAt_loss_layer`: `∂/∂X ½‖S − A X B‖² = −Aᵀ(S−AXB)Bᵀ`,
  one lemma covering every layer's partial (and both 3-layer `MatrixFlow` partials). Selector
  `(A·single k j 1·B)ₚ_q = Aₚₖ B_jq` reduces it to the Layer-1 squared-affine technique; Frobenius
  assembly via `Finset.sum_comm`.
- **Assembly.** `IsDeepMatrixGradFlow` (per-entry grad descent) ⇒ `multilayerFlow_of_gradFlow`
  `τ Ẇₗ = aboveProdᵀ (Σ³¹ − ∏W) belowProdᵀ` (Eq. `multilayer_dyn`, `Σ¹¹ = I`).

**Remaining for milestone 1:** Phase B (the `Rₗ` change of variables → decoupled diagonal flow,
using `prodDesc_telescope`) + Phase C (mode extraction `Wₗ = R₍ₗ₊₁₎ diag(aₗ) Rₗᵀ` ⇒ scalar
`IsDeepFlow`, diagonality-as-hypothesis); then `inf_dyn`/`inf_tc`. See CLAUDE.md "Next steps".

## Session 2026-06-22 — Depth-`N` law DONE (scalar headline, Saxe Eq. `deep_dyn`)

**Done.** `DlnDynamics/DeepDynamics.lean` — the depth-`N` generalization of the reduced mode
dynamics. Gap-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]` on `deep_dyn`,
`deepFlow_conserved`, `deep_dyn_of_deepFlow`, `deepSym_hasDerivAt_two`), `lake build` clean, no
`sorry`. Numerically pre-checked (conservation residual ~1e-16, `deep_dyn` residual ~1e-8 over
random depths/params; RK4-integrated trajectories).

For an `N_l`-layer net with `m = N_l − 1` weight matrices, each connectivity mode is `m` scalars
`a₁,…,aₘ` doing gradient descent on the deep energy `E = (1/2τ)(s − ∏ᵢ aᵢ)²`:
- **`IsDeepFlow`** — the `m`-scalar flow `τ aₗ' = (s − ∏ᵢ aᵢ)·∏_{i≠l} aᵢ` (the honest start).
- **`deepFlow_conserved` / `_eq`** — `aᵢ² − aⱼ²` constant of motion at *every* depth (depth-`N`
  analog of `ab_conserved`). Clean proof: `(∏_{k≠i} aₖ)·aᵢ = ∏ₖ aₖ` (`Finset.prod_erase_mul`)
  makes `aᵢ aᵢ'` independent of `i`, so the product-rule derivative of `aᵢ² − aⱼ²` is `0` by `ring`.
- **`isDeepSymFlow_of_symmetric`** — algebraic reduction onto the symmetric submanifold
  `a₁=⋯=aₘ=c`: `∏ᵢ c = cᵐ` (`prod_const` + `card_univ`/`Fintype.card_fin`), `∏_{i≠l} c = cᵐ⁻¹`
  (`card_erase_of_mem`), so `c` obeys `τ c' = (s − cᵐ)cᵐ⁻¹` (`IsDeepSymFlow`).
- **`deepSym_hasDerivAt`** (Nat-power form) and **`deep_dyn`** (paper's rpow form) — the headline:
  `u = aᵐ` obeys `τ u' = (N_l−1) u^{2−2/(N_l−1)}(s − u)`. `HasDerivAt.pow m` gives
  `(aᵐ)' = m·aᵐ⁻¹·a'`; `aᵐ⁻¹·aᵐ⁻¹ = a^{2(m−1)}` (`← pow_add`, `two_mul`). The rpow bridge
  `(aᵐ)^{2−2/m} = a^{2(m−1)}` (`rpow_bridge`, `0<a`) is `Real.rpow_natCast` + `Real.rpow_mul`
  with the exponent identity `m·(2−2/m) = 2(m−1)` (`push_cast [Nat.cast_sub hm]; field_simp`).
- **`deep_dyn_of_deepFlow`** — end-to-end: `IsDeepFlow` + symmetric + positive ⇒ `deep_dyn`.
- **`deepSym_hasDerivAt_two`** — consistency cross-check: at `m = 2` (`N_l = 3`) the depth-`N`
  law collapses to the two-layer logistic `sigmoidal_dyn` `τ u' = 2u(s − u)`.

**Deferred** (recorded in CLAUDE.md "Next steps"): the depth-`N` *matrix* reduction — deriving
`IsDeepFlow` from the `N_l`-layer matrix gradient descent `multilayer_dyn` via the layerwise `Rₗ`
change of variables (the depth-`N` analog of Phases A–C), plus forward-invariance of the
symmetric submanifold (analog of `ManifoldInvariance`); the infinite-depth limit `inf_dyn`/`inf_tc`;
and the time equation (`t → ∞` limit, learning-time integral `u_int`).

## Session 2026-06-22 — Phase E DONE in full (SVD existence, any square matrix)

**Done.** `DlnDynamics/SVDExistence.lean` — *constructs* a singular value decomposition of
**any** square real `Sg`, discharging the `IsSVD` hypothesis Phase B carried unconditionally.
Gap-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), `lake build` clean, no
`sorry`. Built in two passes (full-rank first, then the rank-deficient general case).

Both passes share the spectral start: `Sgᵀ Sg` Hermitian PSD (`posSemidef_transpose_mul_self`);
the **real spectral adapter** `real_spectral`/`eigenvectorMatrix_orthogonal` unfolds Mathlib's
`spectral_theorem` (`conjStarAlgAut`/`unitaryGroup`/`RCLike.ofReal` form) to plain
`Sgᵀ Sg = V (diagonal d) Vᵀ` with `Vᵀ V = 1` (`Unitary.conjStarAlgAut_apply`,
`Unitary.coe_star_mul_self`, `star = ᵀ` over ℝ); `σ i := √(d i)`, `d i ≥ 0` from PSD.

- **Full-rank (explicit), `exists_isSVD_of_isUnit`.** For invertible `Sg`, `det(Sgᵀ Sg)=(det Sg)²≠0`
  gives `Sgᵀ Sg` PosDef (`posDef_transpose_mul_self_of_isUnit`, via `posDef_iff_det_ne_zero`), so
  every `σ i>0` and the left factor is the *explicit* `U=Sg V (diagonal σ)⁻¹` (pointwise-inverse
  diagonal). `Uᵀ U = σ⁻¹(Vᵀ V)D(Vᵀ V)σ⁻¹ = 1` and `Sg = U(diagonal σ)Vᵀ` are pure
  matrix-cancellation algebra (`isSVD_of_spectral`).
- **General / rank-deficient, `exists_isSVD` (no hypothesis).** Reduced to a self-contained
  **`column_completion`**: `Aᵀ A = diagonal(σ²)`, `σ≥0` ⟹ `∃ U, Uᵀ U=1 ∧ U(diagonal σ)=A`. The
  `σ i>0` columns of `A := Sg V` normalized are orthonormal (their inner products are the
  off-diagonal Gram entries = 0); `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
  completes them to an orthonormal basis indexed by `Fin N` **with no manual reindexing** (it
  packs `exists_equiv_extend_of_card_eq` internally). The basis matrix
  (`(basisFun).toBasis.toMatrix ⇑b`) is orthogonal for free
  (`toMatrix_orthonormalBasis_mem_unitary`) and `U i j = (b j) i` by `rfl`; at `σ j=0`, column
  `j` of `A` is `0` (its squared norm is the Gram diagonal `σ j²=0`) so both sides of
  `U(diagonal σ)=A` vanish — the zero-singular-value columns of `U` are the *free* completion.
- **End-to-end discharge** (`exists_mode_dynamics_of_gradFlow`, now unconditional): compose with
  `a_dyn_of_gradFlow`/`b_dyn_of_gradFlow` (`hdiag := rfl`) ⇒ network gradient descent on *any*
  square `Sg` obeys `a_dyn`/`b_dyn` in *some* SVD frame, **with no SVD assumed**.

Key gotchas (now in CLAUDE.md): the real spectral adapter; building a Euclidean vector from a
function via `(WithLp.equiv 2 (Fin N → ℝ)).symm` (a Pi-literal won't ascribe to `EuclideanSpace`);
`⟪x,y⟫_ℝ = ∑ x i * y i` via `EuclideanSpace.inner_eq_star_dotProduct`; and `conv_lhs => rw [hgram]`
to dodge the dependent-motive failure (`hH.eigenvalues` depends on `Sgᵀ Sg`).

Numerics: `scripts/check_svd_existence.py` (stdlib + Jacobi): full-rank `U diag(σ) Vᵀ = Sg` to
5e-15; general/rank-deficient (U via Gram-Schmidt completion) `UᵀU=1` to 4e-12 and reconstruction
to 2e-8, rank deficiency up to 4.

**Next steps (agreed).** (1) **Depth-`N` law** (Eq. `deep_dyn`) — generalize the 3-layer result
to `N` layers (a new theorem, the larger piece). (2) **Time equation** — the `t→∞` limit `uf→s`
and the learning-time integral `t(u)`/`u_int` (`ClosedForm` verifies the solution, not the
integration/asymptotics). Also still open (lower priority): unbalanced/hyperbolic dynamics
(Appendix A, `a≠b`) and rectangular `Σ³¹`.

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
