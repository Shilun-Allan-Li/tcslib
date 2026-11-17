<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.derivative_distance_lemma -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Distance of derivatives from lower degree

**Claim.** Under the stated farness hypothesis, there is a threshold $\delta\ge\varepsilon$ such that for every shift, some Boolean function has the property that if it has degree at most $d-1$, its distance from the derivative is at least $\delta$.

**Proof.** The proof argues by contraposition. If no such threshold exists, take the threshold to be $\varepsilon$; the negation supplies a shift for which every degree-at-most-$(d-1)$ candidate has distance strictly below $\varepsilon$ from the derivative. The proof then selects the complement of that derivative as a candidate. Expanding the Boolean distance for this choice reduces the claim to the pointwise XOR identities and the assumed farness inequalities, yielding a contradiction. The supplied upstream monotonicity lemma is not invoked in this proof.

**Caveat.** The proof source compresses the candidate's degree and distance calculations into `simp_all`; the supplied statements do not expose the intermediate justification that makes this choice eligible.
