<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mod-three indicator values

**Claim.** The mod-three indicator at $x$ is $1$ when the integer coordinate sum is divisible by $3$, and is $0$ otherwise.

**Proof.** By definition, the Boolean-valued function returns the decision of whether the integer coordinate sum is divisible by $3$. Its real-valued version sends true to $1$ and false to $0$. Evaluating these two cases yields the asserted indicator formula.
