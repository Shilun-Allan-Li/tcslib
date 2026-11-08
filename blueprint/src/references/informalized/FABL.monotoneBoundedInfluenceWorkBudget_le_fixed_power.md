<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.monotoneBoundedInfluenceWorkBudget_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Work Budget Bound

**Claim.** Under the stated dimension, accuracy, and influence assumptions, the monotone bounded-influence work budget is at most $W(C,Q)(n+1)^{F(C,Q)}$, with the specified constant and exponent.

**Proof.** Set $N=n+1$, write $M$ for the family-size bound and $m_1,m_2$ for the two sample counts, and abbreviate their constants and exponents by $A,A_1,A_2,E,E_1,E_2$. The family and sample-count estimates (`learningConsequencesFamilyBound_le_fixed_power`, `singletonInfluenceSampleCount_le_fixed_power`, and `boundedFamilySampleCount_le_fixed_power`) give $M\le AN^E$, $m_1\le A_1N^{E_1}$, and $m_2\le A_2N^{E_2}$. Also $n\le N$ and $n+2\le2N$. Therefore the first stage's work term is bounded by $2A_1N^{E_1+2}$, and the second stage's by $2AA_2N^{E+E_2+1}$. The remaining additive term $n$ is bounded by $N^D$, where $D$ is the overall work exponent: its definition ensures $D\ne0$, and $N\ge1$ implies $N\le N^D$. By definition, $E_1+2\le D$ and $E+E_2+1\le D$. Raising $N\ge1$ to these ordered exponents bounds each contribution by its coefficient times $N^D$. Summing gives $(2A_1+1+2AA_2)N^D$, which is exactly the specified work constant times $(n+1)$ to the specified work exponent.

**Key facts.** `FABL.learningConsequencesFamilyBound_le_fixed_power`, `FABL.singletonInfluenceSampleCount_le_fixed_power`, `FABL.boundedFamilySampleCount_le_fixed_power`.
