<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.half_add_delta_le_e3LinValue_of_sevenEighths_add_delta_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value Transfer

**Claim.** If the associated three-literal satisfiability instance has value at least $7/8+\delta$, then the original three-variable linear constraint instance has value at least $1/2+\delta$ under the corresponding assignment over the field with two elements.

**Proof.** The value of the transformed satisfiability instance is exactly $3/4$ plus one quarter of the original linear instance's value under the corresponding assignment (`value_e3LinToE3Sat`). Substituting this identity into the assumed lower bound gives $7/8+\delta\le 3/4+P/4$, where $P$ is the original value. Rearranging yields $1/2+\delta\le P$.

**Key facts.** `FABL.value_e3LinToE3Sat`.
