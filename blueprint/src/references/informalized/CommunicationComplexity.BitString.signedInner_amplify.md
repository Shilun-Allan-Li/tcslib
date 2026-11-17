<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/BitString.lean :: CommunicationComplexity.BitString.signedInner_amplify -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Inner Product Under Repetition

**Claim.** Repeating each of two bit strings $a$ times multiplies their signed inner product by $a$.

**Proof.** Proceed by induction on the number $a$ of repetitions. When $a=0$, both repeated strings are empty, so their signed inner product is the empty sum, namely $0$; this equals $0$ times the original signed inner product. For the induction step, write each string repeated $a+1$ times as one copy followed by the string repeated $a$ times. The signed inner product is unchanged when the coordinate indexing is transported along the relevant cast of finite index sets (the cast invariance fact, `CommunicationComplexity.BitString.signedInner_comp_cast`). It is additive over concatenated strings (`CommunicationComplexity.BitString.signedInner_append`), so the new inner product is the inner product of one copy plus that of the $a$ repetitions. The first term is the original signed inner product, and the induction hypothesis makes the second $a$ times that value. Their sum is $(a+1)$ times the original signed inner product.

**Key facts.** `CommunicationComplexity.BitString.signedInner_comp_cast`, `CommunicationComplexity.BitString.signedInner_append`.
