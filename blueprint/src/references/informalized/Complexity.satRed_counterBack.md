<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satRed_counterBack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Counter Rewind to the Destination State

**Claim.** Under the transition hypothesis, starting with counter head at $r-1$ and counter length $n$, after exactly $r+1$ steps the machine reaches the destination state with the same tapes and input position, counter head at $0$, second head at $b$, and unchanged output.

**Proof.** Proceed by induction on $r$. For $r=0$, the counter head is at $-1$. The counter left-boundary fact (`Complexity.satRedCounter_left`) says that this cell is blank, so the transition hypothesis selects the blank-cell branch: it moves the counter head right and enters the destination state. The input head does not move, by the zero-move identity (`Turing.moveInputPos_zero`), and the one-step description of the resulting frame is supplied by `Complexity.satRed_move`. The run of length zero is the starting configuration (`Turing.MultiTapeTM.runFrom_zero`), giving the required two-step count in this base case after accounting for the displayed run decomposition.

For the successor case, the starting counter head is at $r$. Since $r\le n$, the counter-reading fact (`Complexity.satRedCounter_read`) says this cell contains true. The transition hypothesis therefore chooses the occupied-cell branch, moving the head left while staying in state $q$. The resulting one-step configuration is the frame with head at $r-1$, as recorded by `Complexity.satRed_move`; the input head remains fixed. Decompose a run of $r+2$ steps into its first step followed by a run of $r+1$ steps (`Turing.MultiTapeTM.runFrom_succ_eq_step`), then apply the induction hypothesis, using $r\le n$ inherited from the successor bound. This yields the desired destination frame.

**Key facts.** `Complexity.satRedCounter_left`, `Complexity.satRedCounter_read`, `Complexity.satRed_move`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`.

**Caveat.** The proof source's base case invokes the one-step frame lemma with a blank-cell transition and then rewrites the run using the successor decomposition; the exact arithmetic/run normalization is compressed in the source, so that bookkeeping is not fully explicit in the account.
