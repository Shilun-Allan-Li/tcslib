<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.rademacherSummands_iIndep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Rademacher summands

**Claim.** Under the uniform probability measure on $\{-1,1\}^n$, the random variables $x\mapsto a_i x_i$, indexed by the coordinates, are mutually independent.

**Proof.** The uniform measure on the sign cube is the product of the uniform measures on its coordinate sign spaces (`rademacherMeasure_eq_pi`). Under a product measure, coordinate projections are mutually independent; composing each projection with a measurable function preserves this independence. For coordinate $i$, that function sends a sign $s$ to $a_i s$, which is measurable on the finite sign space. Applying the product-measure independence result to these coordinatewise functions proves the claim.

**Key facts.** `FABL.rademacherMeasure_eq_pi`.
