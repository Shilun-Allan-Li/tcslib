<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InAC.inNC_one_of_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-zero AC lies in NC

**Claim.** A language recognized by a well-formed, polynomial-size circuit family of depth bounded by a constant at exponent zero is recognized by a polynomial-size family of fan-in-two circuits whose depth has the stated exponent-one bound.

**Proof.** Convert the given depth-zero AC family into a depth-zero tree-AC family (`Language.InAC.inTreeAC_zero`). The tree-circuit conversion theorem raises the depth exponent by one while producing a fan-in-two tree-circuit family (`Language.InTreeAC.inTreeNC_succ`). Finally, tree-NC is included in NC (`Language.InTreeNC.inNC`), giving the required recognition and depth bound.

**Key facts.** `Language.InAC.inTreeAC_zero`, `Language.InTreeAC.inTreeNC_succ`, `Language.InTreeNC.inNC`.
