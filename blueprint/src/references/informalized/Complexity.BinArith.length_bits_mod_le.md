<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.length_bits_mod_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length of a Remainder

**Claim.** If the represented value of $w$ is positive, then the binary expansion of the remainder of $x$ modulo that value has length at most the length of $w$.

**Proof.** Because the modulus $\mathrm{bitsVal}(w)$ is positive, the remainder satisfies $x\bmod \mathrm{bitsVal}(w)<\mathrm{bitsVal}(w)$, and therefore is at most that value. Apply `length_bits_le_of_le` to this remainder and the representing string $w$, using that $w$ has length at most itself, to obtain the claimed length bound.

**Key facts.** `Complexity.BinArith.length_bits_le_of_le`.
