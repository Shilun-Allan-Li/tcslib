<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.expect_hammingUpperTailIndicator_mul_normalizedRademacherSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tail-Weighted Sum Identity

**Claim.** For every $t\in\mathbb R$ and $n\in\mathbb N$, the expectation of the normalized Rademacher sum multiplied by its upper-tail indicator equals the expectation of its excess above $t$, with negative excess replaced by zero, plus $t$ times the expectation of the indicator.

**Proof.** At each cube point, the pointwise identity for the tail indicator states that the product of the indicator and the normalized sum is the positive part of the sum minus $t$, plus $t$ times the indicator (\texttt{hammingUpperTailIndicator_mul_normalizedRademacherSum}). Taking uniform expectations preserves this equality. Linearity distributes expectation over the sum, and the constant factor $t$ can be taken outside the expectation, yielding the claimed identity.

**Key facts.** `FABL.hammingUpperTailIndicator_mul_normalizedRademacherSum`.
