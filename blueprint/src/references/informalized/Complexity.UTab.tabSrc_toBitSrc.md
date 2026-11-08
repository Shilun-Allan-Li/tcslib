<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.tabSrc_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tabulated Source Index

**Claim.** For an available source descriptor whose associated bit source is valid, its tabulated index equals the value of its associated linear register expression.

**Proof.** Unfold the tabulated index and use validity to select its valid-source branch. Then split on the source descriptor. For a constant source, the two Boolean cases give the index $n$ or $n+1$, matching the expression. For an input-head source, availability places the index before the unary-prefix length, so the tabulation selects the input-prefix offset; substituting the hypotheses for the first two registers gives the linear expression. For a unary-input source, the index lies in the unary suffix, and the same substitutions identify its tabulated index with the value of the corresponding register expression. For a previous-block source, the tabulated block number is $ho(r_Q)+d-1$; adding the block’s offset converts this to $ho(r_Q)+d$, and expanding the tabulation base yields exactly the sum contributed by the repeated $r_Q$ registers and the constant term. For current-block and previous-snapshot sources, availability ensures respectively that $ho(r_I)-1+1=ho(r_I)$ and $ho(r_{LB})-1+1=ho(r_{LB})$; expanding the base again gives the repeated-register sum and constant in each expression. Finally, for a cell-end source, expand the block number as $ho(r_{LB})+(	au+1)(2ho(r_T)+1)-1$. The multiplier is positive, so adding one cancels the subtraction; expanding the product gives the contributions of the repeated $r_{LB}$ and $r_T$ registers, and the remaining terms agree with the constant part of the expression.
