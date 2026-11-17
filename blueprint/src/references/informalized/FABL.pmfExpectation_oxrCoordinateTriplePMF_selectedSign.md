<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrCoordinateTriplePMF_selectedSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected-sign expectation for a mixed triple

**Claim.** For the mixture of the pair and parity triple constructions, the expected product of the selected signs has the stated value: it vanishes when $b\ne c$; when $b=c$, its value is $-(1-\delta)$ if all selectors are true, zero if only $a$ is true, $-\delta$ if $a$ is false and $b,c$ are true, and $1$ if all selectors are false.

**Proof.** Condition on which construction is used. The pair construction's selected-sign expectation is $(-1)^b$ when $a$ is false and $b=c$, and zero otherwise (`pmfExpectation_oxrPairTriplePMF_selectedSign`). The parity construction's expectation is $(-1)^a$ when all three selectors agree, and zero otherwise (`pmfExpectation_oxrParityTriplePMF_selectedSign`). Average these two conditional expectations using the biased selector: the pair construction has probability $\delta$ and the parity construction probability $1-\delta$ (`pmfExpectation_pBiasedBitPMF_affine`). In the eight possible selector configurations, if $b\ne c$ both conditional expectations vanish. If $b=c$, the cases are: all true, giving $-(1-\delta)$; only $a$ true, giving zero; $a$ false with $b,c$ true, giving $-\delta$; and all false, giving $1$.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_oxrPairTriplePMF_selectedSign`, `FABL.pmfExpectation_oxrParityTriplePMF_selectedSign`, `FABL.pmfExpectation_pBiasedBitPMF_affine`.
