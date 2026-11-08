<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.card_fixedSignCube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed sign cube cardinality

**Claim.** For a set $J$ of indices among $n$ coordinates, the sign assignments to coordinates outside $J$ form a set of cardinality $2^{n-|J|}$.

**Proof.** A sign assignment outside $J$ is a function from the complement of $J$ in the $n$ coordinates to the two possible signs. The number of such functions is therefore $2$ raised to the cardinality of that complement. The complement has $n-|J|$ elements, giving the stated formula.
