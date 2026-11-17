<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityCharacterizations.lean :: FABL.fourierDegree_toReal_le_of_isKJunta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier degree of a junta

**Claim.** If a Boolean function depends only on a set of at most $k$ coordinates, then its real-valued sign function has Fourier degree at most $k$.

**Proof.** Choose a coordinate set $J$ of size at most $k$ on which the function depends. The real-valued sign function depends on the same set (`dependsOn_toReal_iff`). For any set $T$ with $|T|>k$, we cannot have $T\subseteq J$, since that would imply $|T|\le |J|\le k$. A function depending only on $J$ has zero Fourier coefficient at any set not contained in $J` (`fourierCoeff_eq_zero_of_dependsOn_of_not_subset`). Thus every coefficient above degree $k$ vanishes, and the Fourier degree criterion proves the result.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.dependsOn_toReal_iff`, `FABL.fourierCoeff_eq_zero_of_dependsOn_of_not_subset`.
