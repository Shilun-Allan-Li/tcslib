<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.compl_mem_NSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of Nondeterministic Space

**Claim.** If $S(n)$ is at least logarithmic space at every input length and a binary language is decidable by a finite nondeterministic Turing machine within a constant multiple of $S(n)$ space, then its complement is also decidable within a constant multiple of $S(n)$ space.

**Proof.** Choose a finite nondeterministic machine $N$ witnessing membership of $L$ in the stated space class, with constant $c$. The proof builds a finite collection of deterministic logarithmic-space deciders for the components of the machine's configuration encoding: the input-length, initial-configuration, accepting-configuration, and one-step-transition tests. Their existence is supplied by the respective component-language results (inputLenLang_mem, initLang_mem, acceptLang_mem, stepLang_mem). Summing their individual space constants gives a uniform bound for all component deciders.

The construction chooses an encoding width $W(n)$ for configurations of $N$ on inputs of length $n$, and proves $W(n)\le C_W S(n)$ for a fixed constant $C_W$. This uses the fact that logarithmic space is at most $S(n)$, that the input encoding length is bounded by logarithmic space (size_le_logSpace), and elementary bounds on the code width. The assumption also gives $S(n)\ge1$. For each component decider's virtual input, its length is bounded exponentially in $\logSpace(n)+W(n)$; the logarithmic-space estimate for inputs bounded by a constant times a power of two (logSpace_le_of_le_mul_two_pow) then shows that each component computation fits within a constant multiple of $S(n)$.

The general nondeterministic register-machine simulation theorem (narm_decides_space) now applies to the configuration-checking components and the chosen width bound. Its simulated machine reaches the initial simulation state exactly when the encoded computation certifies that $x\notin L$: the generator theorem (gen_start) supplies this semantic characterization from the original decider, and the zero-register identity (toV_zero) identifies the simulation's initial registers. The register invariant gives the required space bound through the bit-width estimate (bits_succ_le). Hence the constructed finite nondeterministic machine decides the complement within a constant multiple of $S(n)$, as required.

**Key facts.** `Complexity.inputLenLang_mem`, `Complexity.Codec.initLang_mem`, `Complexity.Codec.acceptLang_mem`, `Complexity.Codec.stepLang_mem`, `Complexity.size_le_logSpace`, `Complexity.logSpace_le_of_le_mul_two_pow`, `Complexity.LogProg.narm_decides_space`, `Complexity.LogProg.ISGen.gen_start`, `Complexity.LogProg.ISCount.St.toV_zero`, `Complexity.bits_succ_le`.
