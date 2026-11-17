<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.monomial_neg_input_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial under Global Sign Reversal

**Claim.** Reversing every sign in the input multiplies the monomial indexed by $S$ by $(-1)^{|S|}$.

**Proof.** In the product defining the monomial, each coordinate indexed by $S$ changes from its sign value to its negative, since sign value respects negation. Factoring one $-1$ from each of the $|S|$ factors gives $(-1)^{|S|}$ times the original product.
