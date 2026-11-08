<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrParityTriplePMF_selectedSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected-sign expectation for the parity triple

**Claim.** For the parity triple $(U,V,-UV)$, the expected product of the selected signs is $(-1)^a$ when $a=b=c$, and is zero otherwise.

**Proof.** Rewrite the triple as a function of the uniformly distributed pair $(U,V)$. The expectation under this image distribution becomes an expectation over the pair (`pmfExpectation_map`), and the uniform distribution's expectation is its uniform average (`pmfExpectation_uniformPMF_eq_expect`). The pair average factors into averages over $U$ and $V$. Each sign average is computed by averaging its two possible values, $(g(1)+g(-1))/2$ (`expect_sign`). If all three selectors are false, the product is $1$. If all are true, the product is $U V(-UV)=-1$. In every other selector pattern, after simplifying the product there is an uncancelled factor of either $U$ or $V$, whose uniform average is zero. This yields the stated cases.

**Key facts.** `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_sign`.
