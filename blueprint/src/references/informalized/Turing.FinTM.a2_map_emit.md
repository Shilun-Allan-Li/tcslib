<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitting the encoded first word

**Claim.** Starting in the emit state with first buffer $a=pre\mathbin{++}rest$, the simulator emits each bit of $rest$ twice in order, then emits $0,1$, and enters the run state at $M$’s initial state with tag true and its first-buffer head at the end of $a$.

**Proof.** Proceed by induction on $rest$, retaining the decomposition $a=pre\mathbin{++}rest$. If $rest$ is empty, the first buffer has no bit at the current head, so the emit state outputs $0$ and moves to the separator state; the next step outputs $1$ and enters the run state with tag true. The buffer and head do not move. If $rest=d::rest'$, the buffer contains $d$ at position $|pre|$ (`bufferTape_nat`), so one step emits $d$ and enters the state that remembers $d$. The next step emits $d$ again and moves the first-buffer head one place right. Thus two steps emit the pair $[d,d]$ and leave the head at the end of $pre\mathbin{++}[d]$. Apply the induction hypothesis to the remaining suffix with this longer prefix and with the output extended by $[d,d]$. The decomposition of flat-map over a cons shows that the total emitted word is the two copies of every bit of $rest$, followed by the separator $[0,1]$. The action-to-configuration calculation records each move and output (`a2_map_move`), and `runFrom_add` combines the two initial steps with the remaining run.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.a2_map_move`, `Turing.MultiTapeTM.runFrom_add`.
