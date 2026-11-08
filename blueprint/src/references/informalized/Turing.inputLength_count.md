<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLength_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Length Counting Run

**Claim.** For every $n\le |x|$, the machine reaches the count configuration storing the binary digits of $n$ at input position $n+1$, after a time $t$ satisfying $t+2c(n)=5n$, while its work head stays within the stated bounds at all earlier times.

**Proof.** Proceed by induction on $n$. For $n=0$, take $t=0$. The zero-step run leaves the initial configuration unchanged; the zero binary expansion is empty, so the required target configuration agrees with the given one in state and input position. The head bound at time zero follows immediately.

For the successor step, use the induction hypothesis at $n$ to obtain a time $t$ and the count configuration $c$ that stores the digits of $n$. The binary increment decomposition (`Turing.inputLength_digits`) supplies $p$ and $v$ describing the carry run from $n$ to $n+1$. The digit-count relation and the strict bound $p<|(n+1).bits|$ (`Turing.inputLength_charge`) provide the needed time arithmetic and ensure the new leading digit fits in the expanded segment. Monotonicity of binary digit length gives that the old segment lies within the initially blank region, and that the new segment is long enough for the successor.

The hypothesis that the work tape is initially blank, together with the configuration read lemma (`Turing.inputLengthCfg_read`), identifies the tape contents around the head in $c$ with the buffer tape holding the digits of $n$. Apply the one-round machine behavior (`Turing.inputLength_round`) to run for $2p+3$ more steps: it writes the successor digits, returns the work head to its starting position, and advances the input head by one. The right-move position lemma (`Turing.moveInputPos_pos_of_ne_right`) identifies that input position as $n+2$; the configuration merge lemma (`Turing.inputLengthCfg_merge`) then identifies the result with the required successor count configuration. The run composition law (`Turing.MultiTapeTM.runFrom_add`) combines these two stages. The charge identity from the digit lemma makes the new time $t+2p+3$ satisfy the required equation for $n+1$.

For the head bound, times at most $t$ are covered by the induction hypothesis; its upper bound is also at most the successor's larger bound. For later times, apply the within-round bound from `inputLength_round`, and use that the count configuration has the original work-head position. This yields both stated bounds throughout the extended run. The zero-time and successor-run identities used here are `Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_add`.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.inputLength_digits`, `Turing.inputLength_charge`, `Turing.inputLengthCfg_read`, `Turing.inputLength_round`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.inputLengthCfg_merge`, `Turing.MultiTapeTM.runFrom_add`.
