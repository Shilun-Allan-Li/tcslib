<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.BoundedCubeFunction.oddPart_ofBoolean_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd part of a coordinate function

**Claim.** For each coordinate $i$, the odd part of the bounded real-valued function induced by the $i$th coordinate dictator equals that function.

**Proof.** Use extensionality of bounded cube functions (`FABL.BoundedCubeFunction.ext`) and fix an input $x$. The dictator's value there is the real value of $x_i$, while its value at $-x$ is the real value of $-x_i$. The real-value map sends negation of a sign to negation of its real value (`FABL.signValue_neg`), so the odd part at $x$ is $(a-(-a))/2=a$, where $a$ is the real value of $x_i$. This is exactly the dictator's value at $x$.

**Key facts.** `FABL.BoundedCubeFunction.ext`, `FABL.signValue_neg`.
