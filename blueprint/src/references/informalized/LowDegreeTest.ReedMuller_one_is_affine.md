<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.ReedMuller_one_is_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree-one functions are affine

**Claim.** Every Boolean function in $\mathrm{RM}(1,n)$ is linear or becomes linear after complementing its values; equivalently, it is affine over $\mathbb F_2$.

**Proof.** Membership in $\mathrm{RM}(1,n)$ supplies the Boolean degree-at-most-one condition. The degree-one affine characterization states that any function satisfying this condition is either linear or has a complement that is linear (`LowDegreeTest.degree_le_one_implies_affine`). Applying that characterization gives the asserted disjunction.

**Key facts.** `LowDegreeTest.degree_le_one_implies_affine`.

**Caveat.** The supplied informal statement discusses the BLR test and a derandomization claim, which does not match the formal declaration or its proof. This account follows the formal declaration and proof source.
