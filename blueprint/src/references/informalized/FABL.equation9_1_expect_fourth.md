<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.equation9_1_expect_fourth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth moment decomposition

**Claim.** Under the decomposition $f(b,x)=b\,d(x)+e(x)$, the fourth moment of $f$ is $\mathbb{E}[d^4]+6\mathbb{E}[d^2e^2]+\mathbb{E}[e^4]$.

**Proof.** This is exactly the fourth-moment decomposition for a function written as its odd part $b\,d(x)$ plus its even part $e(x)$ in the first sign coordinate. Applying that identity gives the asserted equality.

**Key facts.** `FABL.expect_fourth_eq_expect_odd_even`.
