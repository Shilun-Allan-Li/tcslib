<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_pair_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Synchronized Rewind of Endpoint Heads

**Claim.** Under the stated transition rule, starting with both endpoint heads at $j-1$, tape zero storing $w$, the last tape blank, and state $q_r$, after $j+1$ steps both heads are at zero, the state is $q_a$, and the specified tape contents and other fields are as stated.

**Proof.** Induct on $j$. When $j=0$, the initial head position is $-1$, so tape zero is blank there. The machine therefore takes the blank-reading transition, moving both endpoint heads right and entering $q_a$. The action leaves tape contents and output unchanged; the endpoint-action identity gives the resulting configuration (`enumCont_ends_apply`). The run identities for zero and one step (`runFrom_zero`, `runFrom_succ_eq_step'`) identify this with the required two-step run. For the successor case, the assumption $j+1\le |w|$ implies $j<|w|$, so at position $j$ tape zero contains $w_j$. The machine takes the nonblank transition, moving both endpoint heads left and remaining in $q_r$. Again the endpoint-action identity shows that the tapes and output are unchanged and that the common head position becomes $j-1$. The run identity `runFrom_succ_eq_step` expresses the $(j+1)+1$-step run as the remaining $j+1$-step run from this new configuration. The induction hypothesis applies to that configuration and gives state $q_a$ and endpoint positions zero, as required.

**Key facts.** `Complexity.enumCont_ends_apply`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
