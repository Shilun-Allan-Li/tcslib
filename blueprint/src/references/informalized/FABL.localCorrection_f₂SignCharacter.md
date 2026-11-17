<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.localCorrection_f₂SignCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Correction of a Sign Character

**Claim.** For every sign character and every pair of inputs, locally correcting the character at the second input returns its value at the first input.

**Proof.** The dot product is additive in its second argument, so the character at $x+y$ is the product of its values at $x$ and $y$, by the multiplicative law for sign encoding (signEncode_add). Thus local correction gives $f(y)(f(x)f(y))$. Since each value is a sign, its square is $1$; associativity and commutativity of multiplication then reduce this expression to $f(x)$.

**Key facts.** `FABL.signEncode_add`.
