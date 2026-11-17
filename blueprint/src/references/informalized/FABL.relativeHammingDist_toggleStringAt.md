<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.relativeHammingDist_toggleStringAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distance After Toggling One Coordinate

**Claim.** For a Boolean string of positive length $n$, toggling one coordinate produces a string at relative Hamming distance $1/n$.

**Proof.** The relative distance is the uniform probability of a mismatch, equivalently the Hamming distance divided by the number of strings in the domain (\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}). In the sum counting mismatches between the original string and its toggle, every coordinate other than $i$ contributes zero, because the toggle leaves it unchanged. At coordinate $i$, the Boolean value is negated, so it differs and contributes one. Thus the Hamming distance is one, and the relative distance is $1/n$.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`.
