<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.uniformInner_projection_rounding_eq_expect_abs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection paired with its sign rounding

**Claim.** The uniform inner product of the coordinate projection of a Boolean function with its sign rounding equals the uniform average of the absolute value of that projection.

**Proof.** Rewrite the uniform inner product as an expectation of pointwise products. At a fixed input, write $t$ for the projected value. The rounded function has real value $1$ if $t\ge0$ and $-1$ otherwise (\texttt{FABL.signValue_thresholdSign}). If $t\ge0$, its product with $t$ is $t=|t|$. If $t<0$, the product is $-t=|t|$. Hence the pointwise product equals the absolute value in either case, and taking the uniform average proves the identity.

**Key facts.** `FABL.signValue_thresholdSign`.
