<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Sum Preservation

**Claim.** For a finite family of functions $f_k$, coordinate projection commutes with their sum: $P_J(\sum_k f_k)=\sum_k P_J f_k$.

**Proof.** Evaluate both sides at an arbitrary input $x$. The summand function inside the expectation defining the left side can be written pointwise as $y\mapsto\sum_k f_k(\operatorname{merge}_J(x,y))$. Finite expectation is additive, so its expectation equals the sum over $k$ of the expectations of these composed functions. Each such expectation is $(P_J f_k)(x)$ by definition. Thus the two sides agree at every $x$.

**Key facts.** `FABL.pmfExpectation_sum`.
