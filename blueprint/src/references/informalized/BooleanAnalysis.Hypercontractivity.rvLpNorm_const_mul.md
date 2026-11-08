<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.rvLpNorm_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the random-variable norm

**Claim.** For any measure space, real-valued function $X$, and real $c,q$, the norm satisfies $N_q(cX)=|c|N_q(X)$.

**Proof.** The extended $L^q$ norm is homogeneous under scalar multiplication: multiplying a function by $c$ multiplies its norm by the norm of the scalar. For real scalars that factor is $|c|$. Taking the real-valued norm from the extended norm preserves this scalar factor, giving $N_q(cX)=|c|N_q(X)$.
