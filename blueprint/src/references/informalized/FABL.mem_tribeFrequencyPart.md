<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.mem_tribeFrequencyPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a Tribe Frequency Part

**Claim.** A position $o$ belongs to the frequency part of $T$ for block $i$ exactly when the position corresponding to $(i,o)$ belongs to $T$.

**Proof.** By definition, the frequency part is the set of within-block positions whose corresponding pair-index lies in $T$. Since $o$ is already a position among the $w$ possibilities, membership in the filtered set is equivalent precisely to that condition.
