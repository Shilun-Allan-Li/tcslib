<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_rewind_candidate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Candidate Heads

**Claim.** For every $j\le |s|$, the preparation machine starting in phase $3$ with both candidate and copy tapes holding $s$, the third tape holding $v$, and the first two heads at displacement $j-1$, reaches phase $4$ after $j+1$ steps with those heads at the origin and all other frame data preserved.

**Proof.** We argue by induction on $j$. When $j=0$, the first two heads are at position $-1$, where the candidate tape is blank by the negative-position rule for `bufferTape` (`bufferTape_left`). In phase $3$, the machine therefore sees a blank on the candidate tape, enters phase $4$, and moves the first two heads one step toward the origin. This gives the claimed frame after one step; the input head does not move, and the third head and tape are unchanged.

For the inductive step, suppose $j+1\le |s|$. At displacement $(j+1)-1=j$, the candidate tape contains the $j$th symbol of $s$: this follows from the nonnegative-position rule identifying `bufferTape` with list lookup (`bufferTape_nat`), and the bound ensures that this symbol exists. In phase $3$, the machine sees that symbol and moves both heads one place left, leaving the tape contents, input head, flag, and third head unchanged. Thus one step takes the configuration to phase $3$ with displacement $j-1$. By the induction hypothesis, the next $j+1$ steps reach phase $4$ with both heads at zero. The run decomposition `runFrom_succ_eq_step` combines these steps, giving the total of $(j+1)+1$ steps.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.
