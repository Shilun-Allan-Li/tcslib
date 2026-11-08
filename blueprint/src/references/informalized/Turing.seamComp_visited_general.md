<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Seam.lean :: Turing.seamComp_visited_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Tape Cells Under Seam Composition

**Claim.** Every work-tape head position visited by the seam-composed run through time $T_1+1+T_2$ belongs either to the positions visited by $M_1$ through time $T_1$ or to those visited by $M_2$ through time $T_2$ from the entry-renamed exit configuration.

**Proof.** Take a position in the seam run's visited set. By the definition of the visited set, it is the head position at some time $t\le T_1+1+T_2$. If $t\le T_1$, the run-through-the-left-component theorem (`seamCompTM_runFrom_left`) identifies this configuration with the left embedding of the $M_1$ run at $t$. Thus the position occurs among the positions visited by $M_1$ through time $T_1$. If $t>T_1$, write $t=T_1+1+u$, with $u=t-(T_1+1)$. The run-through-the-right-component theorem (`seamCompTM_runFrom_right`) identifies the configuration with the right embedding of the $M_2$ run at $u$. The original bound on $t$ gives $u\le T_2$, so this position belongs to the second visited set. In either case it lies in the stated union.

**Key facts.** `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM_runFrom_right`.
