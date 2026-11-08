<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: CommunicationComplexity.FiniteMeasureSpace.pmf_klDiv_eq_sum_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite PMF formula for relative entropy

**Claim.** For probability mass functions $p$ and $q$ on a finite discrete space, their relative entropy is infinite if $q$ vanishes at a point where $p$ is nonzero; otherwise it is the sum of $p(\omega)\log(p(\omega)/q(\omega))$ over all points.

**Proof.** Apply the finite-space formula for relative entropy, which expresses it using the real masses of singleton sets and includes the correction terms $q(\Omega)-p(\Omega)$. Each singleton has measure equal to the corresponding PMF mass, so its real measure is the real value of that mass. Thus the exceptional condition in the finite-space formula becomes exactly that $q(\omega)=0$ while $p(\omega)\ne0$. Since both PMFs have total mass one, the correction terms cancel, leaving the stated sum.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.klDiv_eq_sum_log`.
