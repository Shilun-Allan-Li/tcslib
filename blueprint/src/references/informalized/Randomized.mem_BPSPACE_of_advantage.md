<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.mem_BPSPACE_of_advantage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplifying Positive Advantage in Space

**Claim.** A finite nondeterministic Turing machine with space bounded by a constant multiple of $s(|x|)$, which halts on every choice string and recognizes the correct membership indicator with probability at least $1/2+\delta$ for some fixed $\delta>0$, implies that the language belongs to $\mathrm{BPSPACE}(s)$.

**Proof.** 1. Apply the amplification result `exists_bpDecides_of_advantage` with target error $\varepsilon=1/3$. Since both the original advantage $\delta$ and this target error are positive, it supplies a finite nondeterministic machine $N'$ and a constant $a$ such that $N'$ uses at most $a$ times the original space bound and, on every input, has some halting time at which its correct-output probability is at least $1-1/3=2/3$.

2. The original space bound is $c\,s(n)$, so the amplified bound is $a(c\,s(n))=(ac)s(n)$. By monotonicity of the space-use bound (`Turing.FinNDTM.UsesSpace.mono`), $N'$ therefore witnesses the space requirement for the constant multiple $(ac)s(n)$. Together with the halting time and success guarantee from amplification, this is exactly the definition of membership in $\mathrm{BPSPACE}(s)$.

**Key facts.** `Randomized.exists_bpDecides_of_advantage`, `Turing.FinNDTM.UsesSpace.mono`.
