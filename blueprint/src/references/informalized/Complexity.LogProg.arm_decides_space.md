<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LogProg.arm_decides_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space simulation of register programs

**Claim.** A register program with the stated register-word bounds, side conditions, and correct halting behavior can be simulated by a Turing machine using space bounded by a constant multiple of $S(n)$.

**Proof.** Choose for each oracle language $A_j$ a decider using space $s_j(v)$, and combine these deciders into the finite bank machine used by the simulation. On an input $x$ of length $n$, let $B=CS(n)+1$. The assumed register-word bound ensures that each register's binary word has length at most $W(n)$ throughout the run. At any oracle-call configuration, the program's preconditions supply the required syntactic conditions, including distinctness for register comparisons, valid encodings for input comparisons, and no repeated argument registers. The call-input length estimate (`length_callSegs_le`) therefore bounds the virtual input length by $2n+2+m(2W(n)+2)$. By the hypothesis on $s_j$, the corresponding oracle decider uses at most $CS(n)$ space; its clean simulation fits within $B$ (`bank_cleanRun`, `cleanRun_mono`). The monotonicity of binary-word length (`length_bits_mono`) lets the register bounds control the words placed into each call.

The register simulation theorem (`arm_space`) now constructs a Turing machine that halts with the same answer as the register program. Its space usage is bounded by $m(W(n)+2)+k_D(2B+1)$, where $k_D$ is the fixed number of tapes in the bank machine. Using $W(n)\le CS(n)$, $B=CS(n)+1$, and $S(n)\ge1$, this is at most $(mC+2m+k_D(2C+3))S(n)$. The coefficient is independent of the input, so $L\in\mathrm{SPACE}(S)$.

**Key facts.** `Complexity.LogProg.bank_cleanRun`, `Complexity.LogProg.cleanRun_mono`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.length_callSegs_le`, `Complexity.LogProg.arm_space`.
