<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/LeftoverHash.lean :: TCSlib.InformationTheory.leftover_hash_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Leftover Hash Bound

**Claim.** For a finite field $F$ and an input distribution on $F$ with point probabilities at most $2^{-k}$, the statistical distance between the output $(s,aX+b)$, with $s=(a,b)$ uniform on $F^2$, and uniform on $F^2\times F$ is at most $\frac12\sqrt{|F|2^{-k}}$.

**Proof.** The affine family $x\mapsto ax+b$ is universal (`TCSlib.InformationTheory.isUniversal_affine`). Apply the leftover hash bound to this family and the given input distribution. Its output space is $F^2\times F$, whose hash range has size $|F|$, so the bound becomes $\frac12\sqrt{|F|2^{-k}}$.

**Key facts.** `TCSlib.InformationTheory.isUniversal_affine`, `TCSlib.InformationTheory.leftover_hash`.
