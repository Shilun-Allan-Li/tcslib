<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.twoDivPiRademacherSummands_iIndep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Rademacher summands

**Claim.** On the uniform probability space of sign vectors, the random variables $x\mapsto a(i)x_i$ are mutually independent as the coordinate $i$ varies.

**Proof.** First identify the uniform measure on sign vectors with the product of the coordinatewise uniform sign measures, using the product representation of the sign measure (`FABL.twoDivPiRademacherMeasure_eq_pi`). Each summand is obtained by applying the coordinate map $s\mapsto a(i)s$ to the sign in coordinate $i$; this map is measurable since the sign space is finite. Under a product measure, measurable functions applied separately to distinct coordinates form an independent family. Thus the summands are mutually independent.

**Key facts.** `FABL.twoDivPiRademacherMeasure_eq_pi`.
