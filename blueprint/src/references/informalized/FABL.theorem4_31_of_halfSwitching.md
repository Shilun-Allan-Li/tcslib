<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.theorem4_31_of_halfSwitching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning from Half-Switching Bounds

**Claim.** Under the stated half-switching hypothesis, the low-degree Fourier estimator learns every function in the specified depth-size circuit class with the claimed error probability, while satisfying the stated sample, query, and work bounds.

**Proof.** Apply the theorem that converts low-degree Fourier concentration into a learning guarantee and resource bounds (\texttt{theorem4\_31\_of\_lowDegreeConcentration}). It remains to supply its concentration hypothesis and work bound. For each target in the circuit class, its representation gives a depth-$d$, size-at-most-$s$ circuit. The half-switching hypothesis, together with the LMN concentration theorem, implies concentration through the chosen degree cutoff; the parameter conversion supplies $0<\varepsilon\le1/2$ (\texttt{positiveLearningParameter\_toReal\_mem\_Ioc}) (\texttt{lmn\_theorem\_of\_halfSwitching}). Finally, the requested work bound is exactly the defined low-degree learner work cost, so it is bounded by itself. The conversion theorem then gives the asserted success probability and resource bounds.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.lmn_theorem_of_halfSwitching`, `FABL.theorem4_31_of_lowDegreeConcentration`.
