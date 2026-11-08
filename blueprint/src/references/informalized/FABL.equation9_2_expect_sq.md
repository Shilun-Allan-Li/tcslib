<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.equation9_2_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second moment decomposition

**Claim.** Under the decomposition $f(b,x)=b\,d(x)+e(x)$, the second moment of $f$ is $\mathbb{E}[d^2]+\mathbb{E}[e^2]$.

**Proof.** This is the second-moment decomposition for a function written as its odd part $b\,d(x)$ plus its even part $e(x)$ in the first sign coordinate. Applying that identity gives the asserted equality.

**Key facts.** `FABL.expect_sq_eq_expect_odd_even`.
