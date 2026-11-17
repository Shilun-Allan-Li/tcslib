<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.monotoneBoundedInfluenceRandomExampleBudget_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Example Budget Bound

**Claim.** Under the stated dimension, accuracy, and influence assumptions, the monotone bounded-influence random-example budget is at most $K(C,Q)(n+1)^{E(C,Q)}$, with the specified constant and exponent.

**Proof.** Put $N=n+1$, let $M$ be the bound on the selected Fourier family, and write $m_1$ and $m_2$ for the singleton-stage and second-stage sample counts. The family-size bound (`learningConsequencesFamilyBound_le_fixed_power`) gives $M\le A N^E$, and the sample-count bounds (`singletonInfluenceSampleCount_le_fixed_power` and `boundedFamilySampleCount_le_fixed_power`) give $m_1\le A_1N^{E_1}$ and $m_2\le A_2N^{E_2}$, where $A,A_1,A_2,E,E_1,E_2$ are the corresponding specified constants and exponents. Since $n\le N$, the singleton-stage contribution satisfies $nm_1\le A_1N^{E_1+1}$. The second-stage contribution satisfies $Mm_2\le AA_2N^{E+E_2}$. By the definition of the overall exponent $D$, both $E_1+1$ and $E+E_2$ are at most $D$. Since $N\ge1$, each power is at most $N^D$, so adding the contributions yields $(A_1+AA_2)N^D$. The definitions of the random-example constant and exponent identify this with the claimed bound.

**Key facts.** `FABL.learningConsequencesFamilyBound_le_fixed_power`, `FABL.singletonInfluenceSampleCount_le_fixed_power`, `FABL.boundedFamilySampleCount_le_fixed_power`.
