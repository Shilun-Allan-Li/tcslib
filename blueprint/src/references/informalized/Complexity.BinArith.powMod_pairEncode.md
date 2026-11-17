<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.powMod_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Modular Power on Encoded Inputs

**Claim.** For natural numbers $a,n,p$ with $p\ne0$, the modular-power operation on the nested encoding of their binary representations returns the binary representation of $a^n\bmod p$.

**Proof.** The pair-encoding projection identities recover the three input bit strings from the nested encoding. Their represented values are therefore $a$, $n$, and $p$, since the value of the binary representation of a natural number is that number. Substitution into the definition of the modular-power operation gives the binary representation of $a^n\bmod p$; the assumption $p\ne0$ makes the zero-modulus branch in that definition inapplicable.

**Key facts.** `Complexity.LogProg.bitsVal_bits`.
