# Criticisms

This file lists the criticisms most important to the success of the Saxe 2014
Lean formalization. These are not style nits; they are the issues most likely to
affect whether the project remains mathematically honest, readable, and able to
reach the full matrix-to-mode reduction.

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

1. Update stale docs in `README.md` and the header of `MatrixFlow.lean`.
2. Define the Phase B SVD-hypothesis interface without proving SVD existence.
3. Prove reusable Frobenius/trace orthogonal-invariance lemmas.
4. Prove the change of variables from `wb_avg` to `wbo_dyn`.
5. Extract column/row mode equations as `a_dyn` and `b_dyn`.
6. Treat the invariant manifold proof as its own milestone.
7. Only then return to full SVD existence, using the interface that Phase B/C
   actually require.
