<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/ArrowLevelOneBound.lean :: FABL.three_div_nat_isLittleO_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Reciprocal Sequence

**Claim.** As $n$ tends to infinity through the natural numbers, $3/n$ is little-$o$ of the constant sequence $1$, equivalently it tends to zero.

**Proof.** The characterization of little-$o$ relative to the constant-one sequence reduces the claim to convergence to zero. The natural numbers, viewed as real numbers, tend to infinity; composing this with the fact that reciprocals tend to zero along values tending to infinity shows that $1/n\to0$. Multiplication of a convergent sequence by the constant $3$ preserves its limit, so $3/n\to0$, as required.
