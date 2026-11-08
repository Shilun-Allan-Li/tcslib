<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/BerryEsseenIntervals.lean :: FABL.gaussianReal_cdf_leftLim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left continuity of the Gaussian distribution function

**Claim.** For every real number $x$, the left-hand limit of the standard Gaussian distribution function at $x$ equals its value at $x$.

**Proof.** The standard Gaussian assigns measure zero to each singleton: its null-singleton property gives $(\gamma)(\{x\})=0$. The singleton identity for the measure associated with a distribution function identifies this measure with the jump from the left limit to the value at $x$. Thus that jump is zero. Since a distribution function is monotone, its left-hand limit is at most its value; together with the zero-jump equality, this gives equality.
