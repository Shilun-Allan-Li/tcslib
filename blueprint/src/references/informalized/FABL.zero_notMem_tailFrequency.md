<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.zero_notMem_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Is Absent from Tail Frequencies

**Claim.** For every natural number $n$ and every finite set $S\subseteq\mathrm{Fin}(n)$, the index $0$ does not belong to the set obtained by shifting each element of $S$ up by one in $\mathrm{Fin}(n+1)$.

**Proof.** Every element in the image of $S$ under the successor embedding has first coordinate one greater than the first coordinate of an element of $S$. Its first coordinate is therefore positive, while the index $0$ has first coordinate zero. Hence $0$ cannot be in the image.
