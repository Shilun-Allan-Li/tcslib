<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.fourierOneNormClass_queryLearnable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query learning from bounded Fourier norm

**Claim.** If a Boolean target has Fourier one norm at most $s$, then the query-mode Kushilevitz–Mansour procedure, with family-size bound $\\max\{1,\lceil 4s^2/\varepsilon\rceil\}$, outputs a hypothesis whose relative Hamming error exceeds $\varepsilon$ with probability at most $1/10$.

**Proof.** Let $\mathcal F$ be the family of Fourier frequencies whose coefficients for the target have magnitude greater than $\varepsilon/4$. The positive-parameter hypothesis ensures $\varepsilon/4>0$, so the concentration theorem for the $\ell_1$-concentrating Fourier family shows that the target's Fourier spectrum is concentrated on $\mathcal F$ (`isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily`). The family-size estimate bounds $|\mathcal F|$ by the prescribed value of $M$ (`card_l1ConcentratingFourierFamily_le_familySizeBound`). Apply the Kushilevitz–Mansour failure-probability theorem to this initial family: under precisely these size and concentration hypotheses, its query-mode program has probability at most $1/10$ of producing error greater than $\varepsilon$ (`kushilevitzMansourProgramForBound_failureProbability_le_one_tenth`).

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.isFourierSpectrumConcentratedOn_l1ConcentratingFourierFamily`, `FABL.card_l1ConcentratingFourierFamily_le_familySizeBound`, `FABL.kushilevitzMansourProgramForBound_failureProbability_le_one_tenth`.
