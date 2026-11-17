<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.relativeHammingDist_addressing_ge_quarter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addressing Function Distance Bound

**Claim.** If $|J|\le 2^{m-1}$ and $g$ depends only on coordinates in $J$, then its relative Hamming distance from the addressing function is at least $1/4$.

**Proof.** The probability that the addressing function selects a coordinate outside $J$ is at least $1/2$ (`FABL.uniformProbability_addressingSelectedOutside_ge_half`). For any such function $g$ depending only on $J$, this probability is at most twice the relative Hamming distance from the addressing function to $g$ (`FABL.two_mul_relativeHammingDist_addressing_ge_event`). Combining the inequalities gives $1/2\le 2d$, where $d$ is that distance, hence $d\ge 1/4$.

**Key facts.** `FABL.uniformProbability_addressingSelectedOutside_ge_half`, `FABL.two_mul_relativeHammingDist_addressing_ge_event`.
