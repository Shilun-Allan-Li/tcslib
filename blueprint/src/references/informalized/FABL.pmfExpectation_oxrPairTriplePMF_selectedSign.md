<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.pmfExpectation_oxrPairTriplePMF_selectedSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected-sign expectation for the pair triple

**Claim.** For the pair triple $(U,V,-V)$, the expected product of the selected signs is $(-1)^b$ when $a$ is false and $b=c$, and is zero otherwise.

**Proof.** Express the triple's distribution as the image of the uniform distribution on pairs of signs. The expectation under an image distribution is the expectation of the function composed with the map (`pmfExpectation_map`), and expectation under the uniform distribution agrees with the uniform average (`pmfExpectation_uniformPMF_eq_expect`). The average over the two input signs factors into the product of their separate averages. Evaluate each sign average using the fact that a uniform sign has expectation $(g(1)+g(-1))/2$ for any function $g$ (`expect_sign`). If $a$ is selected, the product contains the independent factor $U$, whose average is zero. If $a$ is unselected, the remaining selected factors involving $V$ are $V$ and $-V$: their product is $-1$ when both are selected, while if neither is selected the product is $1$. If exactly one is selected, its average is zero. These cases give precisely the claimed formula.

**Key facts.** `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_sign`.
