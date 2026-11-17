<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmf_apply_toReal_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Point Mass Is at Most One

**Claim.** For any probability mass function $p$ on a type $\Omega$ and any point $x\in\Omega$, the mass $p(x)$, viewed as a real number, is at most $1$.

**Proof.** A probability mass function has $p(x)\le 1$ in the extended nonnegative reals. Since $1$ is finite, the map taking an extended nonnegative real to its real-valued version preserves this inequality. The real-valued version of $1$ is $1$, giving $(p(x)).\mathrm{toReal}\le 1$.
