<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Separator Transition

**Claim.** When positions $i$ and $i+1$ contain $01$, the syntax pass consumes those two bits and leaves the work tape and head unchanged. Its resulting state is certificate-copy if $s$ is exact-end, and otherwise verdict with bit $1$.

**Proof.** The first step reads the $0$ and moves the input head right, changing the control state to the intermediate syntax state carrying $s$ and the bit just read. The second step reads the $1$ and again moves right. The machine’s separator transition sends the control to certificate-copy precisely when $s$ is exact-end, and to verdict with bit $1$ otherwise. Both moves preserve the empty work tape and head position; the two-step run laws give the stated final configuration.

**Key facts.** `Complexity.taut_read`, `Complexity.taut_move_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
