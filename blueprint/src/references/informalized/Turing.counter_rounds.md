<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_rounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Rounds

**Claim.** Under the stated tape encoding, binary counter bound, and round hypotheses, the counter-loop machine completes the first $n$ rounds with the claimed state, tape, and work-head positions, while avoiding both exit anchors before the final time and keeping the counter head within its prescribed interval.

**Proof.** Proceed by induction on $n$. For $n=0$, the elapsed time and overhead are zero, and the machine is at its initial decrement phase. The initial counter word is $w$; the tape hypothesis shows that replacing its encoded segment by itself changes no tape cell. At time zero the counter head is in the required interval, and the work-head condition is witnessed by round $0$ at time $0$.

For the successor step, assume the assertion through round $n$. The hypotheses give that the base machine is at state $a$ at the start of round $n$, that the round duration is positive, and that its intermediate states are neither $a$ nor the designated exit. The induction endpoint is consequently redirected to the decrement phase. The binary-counter decrement identity says that the next counter word is obtained by one fixed-width decrement; the bound on $n$ ensures this decrement is defined. The counter-debit lemma runs that decrement in its prescribed cost, updates the encoded counter segment, and supplies the counter-head and work-head span conditions for that portion. The counter-body lemma then runs the base machine for the round duration, with its intermediate-state hypothesis ensuring that the redirect does not prematurely enter either exit anchor. The resulting configuration is exactly the next base orbit configuration with its state redirected, and with the updated counter tape.

Concatenate the debit and body spans, then concatenate that combined span with the span supplied by the induction hypothesis. The span-concatenation lemma preserves avoidance of the exit anchors and the counter-head interval across each join; the two work-head descriptions both imply the required round-by-round condition. Finally, the sum of the first $n+1$ round durations and the counter overhead splits into the previous elapsed time plus this round's decrement cost and body duration, giving the asserted total time.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.counterWord_length`, `Turing.counter_word_decrement`, `Turing.counter_patch_frame`, `Turing.counter_debit`, `Turing.counter_patch_twice`, `Turing.counter_body`, `Turing.counter_span_append`, `Turing.MultiTapeTM.runFrom_add`.
