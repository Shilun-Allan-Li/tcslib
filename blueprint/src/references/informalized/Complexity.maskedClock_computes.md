<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.maskedClock_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Masked Clock Preserves Computation Bounds

**Claim.** If $W$ writes the binary digits of $T(|x|)$, halts within the stated time bound, and uses the stated space on every input, then the machine masking scanned symbols to false has the same output, halting guarantee, and space bound on every input.

**Proof.** Fix an input $x$. Apply the assumed guarantee for $W$ to the constant word of $|x|$ false symbols. Its length is $|x|$, so the assumed output and time and space bounds are those required for $x$. The lockstep theorem (`Complexity.maskedClock_lockstep`) identifies the masked configuration after the given number of steps on $x$, after replacing its input by that constant word, with the configuration of $W$ on the constant word. Consequently their states and outputs agree. The characterization of computation within time (`Turing.FinTM.computesInTime_iff`) says that the output and halting state at that time establish the desired time guarantee. The lockstep theorem also preserves the configuration’s tape data and head positions under masking, so the space usage agrees with that of $W$ on the constant word, giving the required space bound.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Complexity.maskedClock_lockstep`.

**Caveat.** The proof obtains the exact space equality through the lockstep configuration identity; this relies on masking leaving work tapes and head positions unchanged.
