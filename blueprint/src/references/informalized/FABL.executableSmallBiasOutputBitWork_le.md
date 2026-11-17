<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasOutputBit.lean :: FABL.executableSmallBiasOutputBitWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Bit Work Bound

**Claim.** For all natural numbers $\ell$ and $j$, the work for output bit $j$ is at most $16(j+1)(\ell+1)^2$.

**Proof.** The arithmetic-work bound (FABL.binaryArithmeticWork_le) gives $M(\ell)\le 8(\ell+1)^2$, since modular-multiplication work is at most the maximum of the addition and multiplication work. As $(\ell+1)^2\ge1$, it follows that $M(\ell)+1\le9(\ell+1)^2$. The output-work identity (FABL.executableSmallBiasOutputBitWork_eq) writes the total as $\ell+(j+1)(M(\ell)+1)+2\ell+1$. The part independent of $j$ satisfies $3\ell+1\le4(\ell+1)^2$, and $(\ell+1)^2\le(j+1)(\ell+1)^2$. Applying these estimates bounds the total by $4(j+1)(\ell+1)^2+9(j+1)(\ell+1)^2=13(j+1)(\ell+1)^2$, which is at most the claimed bound with constant $16$.

**Key facts.** `FABL.binaryArithmeticWork_le`, `FABL.executableSmallBiasOutputBitWork_eq`.
