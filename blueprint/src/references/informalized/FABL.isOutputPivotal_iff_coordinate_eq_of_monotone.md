<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.isOutputPivotal_iff_coordinate_eq_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output pivotality for monotone functions

**Claim.** For a monotone sign-valued function, having output $b$ at $x$ and being pivotal at coordinate $i$ is equivalent to having $x_i=b$ and being pivotal there.

**Proof.** Assume first that $f(x)=b$ and that coordinate $i$ is pivotal at $x$. Monotonicity gives the pivotal-output identity $f(x)=x_i$ (the fact that a monotone function’s output at a pivotal coordinate equals that coordinate, `FABL.monotone_output_eq_coordinate_of_isPivotal`). Thus $x_i=b$, and pivotality is already part of the assumption. Conversely, suppose $x_i=b$ and $i$ is pivotal at $x$. The same identity gives $f(x)=x_i=b$, while pivotality remains unchanged. These implications establish the equivalence.

**Key facts.** `FABL.monotone_output_eq_coordinate_of_isPivotal`.
