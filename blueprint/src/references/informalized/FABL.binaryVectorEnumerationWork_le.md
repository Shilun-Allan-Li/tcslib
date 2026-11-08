<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryVectorEnumerationWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Enumeration work bound

**Claim.** For every integer $\ell\ge 0$, the work required to enumerate all binary vectors of length $\ell$ is at most $4(\ell+1)2^\ell$.

**Proof.** Proceed by induction on $\ell$. At length zero the work and the proposed bound both simplify to $1$ and $4$, respectively. For the step from $\ell$ to $\ell+1$, the enumeration list has length $2^\ell$ (by the length formula `length_allBinaryVectors`), and the work recurrence therefore gives the previous work plus $3\cdot 2^\ell+1$. The induction hypothesis bounds the previous work by $4(\ell+1)2^\ell$. Since $2^\ell\ge1$, this sum is at most $4(\ell+2)2^\ell$, which is the desired bound because $2^{\ell+1}=2\cdot2^\ell$.

**Key facts.** `FABL.length_allBinaryVectors`.
