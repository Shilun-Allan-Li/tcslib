<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.usesSpace_of_haltsWithin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound from per-input halting times

**Claim.** If each input has a time at which every run halts and every run of that length uses at most the prescribed space bound, then every run on every input satisfies that bound.

**Proof.** Fix an input $x$ and a choice word $w$. The hypothesis supplies a time $T$ for this input, such that every length-$T$ run halts and uses at most $s(|x|)$ cells. Apply the space bound from a halting time bound (`spaceUsedWith_le_of_haltsWithin`) with $S=s(|x|)$ to conclude that the run on $w$ uses at most $s(|x|)$ cells. Since $x$ and $w$ were arbitrary, this is the claimed space bound.

**Key facts.** `Turing.FinNDTM.spaceUsedWith_le_of_haltsWithin`.
