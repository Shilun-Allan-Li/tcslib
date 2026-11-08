<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.iterate_detWStep_encState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration Commutes with State Encoding

**Claim.** For every natural number $p$, arithmetic state $s$, and natural number $n$, applying the encoded determinant step $n$ times to the encoding of $s$ with parameter $p$ gives the encoding, with the same parameter, of the state obtained by applying the determinant step with parameter $p$ exactly $n$ times.

**Proof.** Induct on $n$, generalizing the state $s$. For zero iterations, both sides are the original state encoding. For the successor case, write each iterate as one step applied after the preceding iterate. The one-step correspondence between the encoded determinant step and the arithmetic determinant step gives the desired encoding after the first step; the induction hypothesis, which applies to every state, then identifies the remaining iterations.

**Key facts.** `Complexity.BinArith.detWStep_encState`.
