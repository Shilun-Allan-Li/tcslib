<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.powInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Invariant Preservation and Progress

**Claim.** One application of the specified state update preserves the power invariant; when the modulus is positive and the exponent component is nonempty, the exponent component becomes strictly shorter.

**Proof.** Unpack the invariant state as an encoding of the modulus $B$, exponent $E$, base residue $b$, and accumulator $\mathrm{acc}$. If the update's stopping test holds—either $E$ is empty or $B=0$—the state is unchanged, so the invariant is unchanged. In this case the progress implication is vacuous or its exponent-length hypothesis is impossible. Otherwise $E$ has the form $(c)::E'$ and $B>0$. The update drops the first exponent bit and replaces the base residue by $b^2\bmod B$; it replaces the accumulator by $\mathrm{acc}\,b\bmod B$ when $c$ is true, and leaves it unchanged when $c$ is false. These are exactly the decoded components of the updated encoding. The exponent length decreases by one, and the represented base and accumulator remain canonical because they are produced as binary representations. The modular-remainder length bound gives the required size bounds for the new residues; in the unchanged-accumulator branch its old bound applies. Since each new residue is reduced modulo the positive modulus, both remain strictly below it. For the invariant congruence, the old relation is $\mathrm{acc}\,b^{E}=A^N$ modulo $B$. If $c$ is false, the accumulator is unchanged and $E=2E'$, so replacing $b$ by $b^2$ gives $\mathrm{acc}(b^2)^{E'}=\mathrm{acc}b^E$. If $c$ is true, the accumulator gains a factor of $b$ and $E=2E'+1$, yielding the same product. Reducing the updated residues modulo $B$ preserves these congruences, proving the invariant after the step.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.length_bits_mod_le`.
