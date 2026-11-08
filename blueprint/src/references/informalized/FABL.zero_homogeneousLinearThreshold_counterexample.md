<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.zero_homogeneousLinearThreshold_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Constant Threshold Counterexample

**Claim.** For the specified one-dimensional Boolean function that is constantly $1$, the zero coefficient vector represents it as a linear threshold function; it is not odd, and its mean is $1$.

**Proof.** With every coefficient equal to zero and offset zero, the affine linear form vanishes at every input. By the convention that the sign at zero is $1$, the threshold function is therefore constantly $1$, as required. To see that the Boolean function is not odd, evaluate the oddness condition at the input whose sole coordinate is $1$: its negation is the input with sole coordinate $-1$, but the function takes value $1$ at both, whereas oddness would require opposite values. Finally, the real-valued version of the function is also constantly $1$, so its uniform mean is $1$.
