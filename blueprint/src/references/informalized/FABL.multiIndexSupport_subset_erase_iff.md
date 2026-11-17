<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.multiIndexSupport_subset_erase_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support contained in a punctured set

**Claim.** The support of $a$ is contained in the set of all positions except $i$ if and only if $a(i)=z$.

**Proof.** Use the characterization that support containment in a set $J$ is equivalent to every position outside $J$ having value $z$ (\texttt{FABL.multiIndexSupport\_subset\_iff}). For $J$ equal to all positions except $i$, the only position outside $J$ is $i$. Thus containment implies $a(i)=z$. Conversely, if $a(i)=z$, every position outside $J$ has value $z$, so the characterization gives the required containment.

**Key facts.** `FABL.multiIndexSupport_subset_iff`.
