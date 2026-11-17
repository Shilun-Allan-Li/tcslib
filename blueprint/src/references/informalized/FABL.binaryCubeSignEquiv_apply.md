<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.binaryCubeSignEquiv_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Formula for Sign Encoding

**Claim.** At each coordinate, the sign encoding of a binary vector is the sign encoding of that coordinate's bit, namely $(-1)^{x_i}$.

**Proof.** The sign encoding on a product of coordinate spaces is defined coordinatewise from the scalar sign equivalence. Evaluating it at coordinate $i$ therefore gives the scalar encoding of $x_i$, which is $(-1)^{x_i}$.
