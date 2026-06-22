# Criticisms

This file lists the criticisms most important to the success of the Saxe 2014
Lean formalization. These are not style nits; they are the issues most likely to
affect whether the project remains mathematically honest, readable, and able to
reach the full matrix-to-mode reduction.

## Resolution status (updated 2026-06-22)

Most of the original criticisms have been addressed across the Phase B/C/D work; the
items below are kept verbatim as the review, with status noted here.

- **Critical 1 (keep the reduction distinct from the per-mode side result)** — the full
  chain `network loss → wb_avg → wbo_dyn → a_dyn/b_dyn → ab_dyn` is now formalized as
  composable theorems (`wbo_dyn_of_gradFlow`, `a_dyn_of_gradFlow`,
  `isABFlow_of_gradFlow_on_manifold`); docs state explicitly which links are established
  and that the one remaining gap is forward-invariance in time.
- **Critical 2 (Phase B before SVD existence)** — done: `SVDReduction.lean`, SVD carried
  as the `IsSVD` hypothesis; SVD *existence* (Phase E) now **fully discharged for any square
  `Sg`** (`SVDExistence.lean`, `exists_isSVD`; explicit full-rank variant
  `exists_isSVD_of_isUnit`).
- **Critical 3 / Recommended 6 (invariant manifold as a real theorem)** — option 1 done
  (`isABFlow_of_modeFlow`, with explicit manifold hypotheses, not hidden in the
  extraction); forward-invariance in time (option 3) is scoped as its own theorem in
  `PHASE_D_OPTION3.md` and is in progress in a parallel session.
- **High 1 (stale docs)** — done. **High 3 (Frobenius API)** — done
  (`trace_transpose_mul_self`, `sum_sq_mul_orthogonal`, named trace steps).
  **High 4 (mode indexing)** — done (`aMode`/`bMode`, explicit `∑_{γ≠α}` competition).
- **High 2 (SVD interface) / Recommended 7** — the `IsSVD` interface is designed and used;
  the SVD *existence* build (Phase E) is **done for any square `Sg`** (`SVDExistence.lean`,
  `exists_isSVD`), composed end-to-end in `exists_mode_dynamics_of_gradFlow` (gradient descent
  on any square `Sg` ⇒ `a_dyn`/`b_dyn`, no SVD assumed). Fully resolved.
- **Medium 2 (lemma structure over comments)** — addressed; large rewrites factored into
  named lemmas mirroring the paper, now a standing rule in `CLAUDE.md`.
  **Medium 3 (conceptual chain over endpoint equations)** — addressed (composable chain).
  **Medium 1 (integration argument in `ClosedForm`)** — **now resolved**: `TimeEquation.lean`
  proves the separable learning-time integral `u_int` (`learningTime_integral`, second FTC) and
  the `t→∞` asymptotics `uf → s` (`uf_tendsto_atTop`).

**The analytical core is complete.** Remaining genuine generalizations: the rectangular-diagonal
`S` (non-square `Σ³¹`) SVD/depth-`N` reduction, and the unbalanced learning-*time* integral
(Appendix A; the `u`-dynamics is done in `UnbalancedDynamics.lean`).
Done: Phase E SVD existence (any square `Sg`); Phase D option 3 forward-invariance; depth-`N`
scalar law `deep_dyn` (`DeepDynamics`); **depth-`N` matrix reduction end-to-end** (`multilayer_dyn`
Phase A `DeepMatrixFlow`, change of variables + mode extraction Phases B–C `DeepReduction`,
`deep_dyn_of_gradFlow`) + **forward-invariance** (`DeepManifoldInvariance`); **time equation**
(`t→∞` limit + integral `u_int`, `TimeEquation`); **infinite-depth limit** (`inf_dyn`/`inf_tc`,
`InfiniteDepth`); **unbalanced dynamics** (Appendix A, `UnbalancedDynamics`).

## Critical

1. The scalar `ab_dyn` development is not yet the paper's full derivation.

   `GradientFlow.lean` and `Network.lean` correctly show that an already
   decoupled one-mode loss gives `IsABFlow`, but Saxe reaches `ab_dyn` only after
   the matrix dynamics, SVD change of variables, mode extraction, and invariant
   manifold argument. The project must keep this distinction explicit. Otherwise
   the formalization risks appearing to prove the central reduction before it has
   actually been formalized.

2. Phase B should be completed before SVD existence.

   The next essential theorem is the orthogonal change of variables from
   `Sigma31 = U * S * V^T`, `Wa = Wao * V^T`, and `Wb = U * Wbo` to the
   transformed dynamics `wbo_dyn`. This should assume an SVD-like decomposition
   as a hypothesis. Starting with full SVD existence is likely to consume a lot
   of effort before the project knows the exact interface needed downstream.

3. The invariant manifold proof is a major bottleneck, not a routine cleanup.

   Saxe says it is straightforward that the special orthogonal-mode
   initialization remains decoupled. In Lean, this is a forward-invariance
   statement for an ODE-defined flow. It should be planned as a real theorem with
   explicit hypotheses, not hidden inside the extraction from `a_dyn` to
   `ab_dyn`.

## High Priority

1. Documentation is stale and may mislead future work.

   `MatrixFlow.lean` still describes itself as a skeleton with proofs in
   progress, but Phase A is complete and gap-free. `README.md` also mostly
   describes the older scalar state of the project. These docs should be updated
   so readers know which statements are established foundations and which are
   still planned.

2. The future SVD theorem needs an interface design before implementation.

   The likely proof route is standard: diagonalize `M^T * M`, take singular
   values as square roots of nonnegative eigenvalues, define left singular
   vectors by `u_i = sigma_i^{-1} * M v_i` for positive singular values, and
   extend them to an orthonormal basis. The hard Lean work will be rectangular
   indexing and basis extension. Do not commit to ordered singular values or a
   heavyweight structure unless Phase B/C actually need them.

3. Frobenius orthogonal invariance should be isolated as reusable API.

   Phase B will need facts like `||U * M * V^T||_F = ||M||_F` under orthogonality.
   If this is proved inline inside the SVD change-of-variables theorem, the proof
   will become hard to read and hard to reuse. It should be factored into named
   lemmas matching the human argument: trace expansion, cyclicity, and
   cancellation by `U^T * U = I`, `V^T * V = I`.

4. Mode extraction from `wbo_dyn` must preserve the paper's indexing story.

   The transition to `a_dyn` and `b_dyn` should expose the paper's columns of
   `Wao` and rows of `Wbo`, with the competition sums over other modes. A proof
   that only rewrites matrix entries without naming this structure will be
   difficult for a human to audit against the paper.

## Medium Priority

1. The closed-form proof verifies the solution but does not formalize the paper's
   integration argument.

   `ClosedForm.lean` proves that `uf` satisfies the logistic ODE and initial
   condition. This is mathematically valid, but it does not formalize Saxe's
   separable integral `u_int` or an IVP uniqueness argument. For the current
   project this is acceptable, but it should not be described as a formalization
   of the integration derivation until that bridge exists.

2. Some Lean proofs are readable only because of comments, not lemma structure.

   `MatrixFlow.lean` is much better than a raw tactic dump, but future Phase B/C
   proofs will be more complex. Large algebraic rewrites should be split into
   named lemmas whose statements correspond to human proof steps. This is
   especially important for orthogonal invariance, diagonal matrices, row/column
   extraction, and zero competition terms.

3. The project should avoid proving only endpoint equations.

   The goal is not merely to make Lean accept a final ODE. The formal statements
   should preserve the paper's conceptual chain:

   `network loss -> wb_avg -> SVD coordinates -> wbo_dyn -> a_dyn/b_dyn ->
   invariant manifold -> ab_dyn -> sigmoidal dynamics`.

   Any shortcut should be documented as a derived side result, not as a substitute
   for this chain.

## Recommended Next Steps

1. ✅ Update stale docs in `README.md` and the header of `MatrixFlow.lean`.
2. ✅ Define the Phase B SVD-hypothesis interface without proving SVD existence (`IsSVD`).
3. ✅ Prove reusable Frobenius/trace orthogonal-invariance lemmas
   (`trace_transpose_mul_self`, `sum_sq_mul_orthogonal`).
4. ✅ Prove the change of variables from `wb_avg` to `wbo_dyn` (`wbo_dyn_of_gradFlow`).
5. ✅ Extract column/row mode equations as `a_dyn` and `b_dyn`.
6. ✅ Treat the invariant manifold proof as its own milestone (option 1 done,
   `isABFlow_of_modeFlow`; ⟳ option 3 forward-invariance in a parallel session).
7. ⬜ Only then return to full SVD existence (Phase E), using the `IsSVD` interface that
   Phase B/C/D actually require — still deferred.
