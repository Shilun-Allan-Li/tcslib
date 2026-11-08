<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdFunctionCounting.lean :: FABL.two_pow_add_one_le_next_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive powers of two

**Claim.** For every natural number $n$, $2^n+1\le 2^{n+1}$.

**Proof.** The successor-power identity gives $2^{n+1}=2^n\cdot 2=2^n+2^n$. Since $2^n\ge1$, adding $2^n$ to $2^n$ is at least adding $1$, proving the inequality.
