<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.rightGuide_origin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Origin on the Right Guide

**Claim.** For every natural number $R$ and integer $z$, the right guide of radius $R$ carries the origin symbol at $z$ exactly when $z=0$.

**Proof.** Separate the exceptional position $z=R+1$, where the right guide is updated to carry the edge symbol. Since $R+1\ne0$, the origin symbol is absent there. At every other position the update leaves the original copy guide unchanged. That copy guide carries the origin symbol exactly at zero, by the origin characterization for copy guides with positive length (`Complexity.copyGuide_origin`); here its length is $R+1>0$.

**Key facts.** `Complexity.copyGuide_origin`.
