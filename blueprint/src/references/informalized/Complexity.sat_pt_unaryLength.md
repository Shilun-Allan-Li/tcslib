<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_unaryLength -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Length

**Claim.** The function mapping each binary string $x$ to the string of $|x|$ ones is polynomial-time computable.

**Proof.** Apply the polynomial-time construction for finite-state word processing (`satMap_poly`) with a single state that remains unchanged on every input bit and emits one true bit at each position, with no additional output at the end. Induction on the input list shows that after reading a list of length $r$, the emitted word is the list of $r$ true bits: the empty input produces the empty list, and each additional bit adds one true bit. Therefore the machine computes the unary encoding of the input length.

**Key facts.** `Complexity.satMap_poly`.
