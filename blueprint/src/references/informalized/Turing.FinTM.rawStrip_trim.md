<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.rawStrip_trim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Removing the final marker

**Claim.** From the reverse-scan configuration in state $1$ with work word $w$ and head at its final position, the machine halts within $3(|w|+1)$ steps and outputs the prefix strictly before the last true bit, or the empty word if there is no true bit.

**Proof.** Induct on the word by removing its final bit, using reverse induction. For the empty word, one transition from the state-$1$ configuration halts with empty output; this is the required value of the last-true prefix when there is no marker. For a word $w$ followed by a bit, first apply the one-step erasure fact (`rawStrip_erase`). If the bit is false, this returns the machine to state $1$ with work word $w$ and head at its final position. Apply the induction hypothesis, adding that initial step to the time. The last true bit and its preceding prefix are unchanged by appending false. If the bit is true, erasure instead enters state $2$ with work word $w$ and head at its final position. The completion result (`rawStrip_finish`) halts after $2(|w|+1)$ further steps and outputs all of $w$, which is exactly the prefix before this newly appended last true bit. In both cases the time is at most the claimed bound: the false case adds one to the induction bound, and the true case takes $2(|w|+1)+1$ steps. The run recurrence (`runFrom_succ_eq_step`) accounts for the initial erasure step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.rawStrip_erase`, `Turing.FinTM.rawStrip_finish`.
