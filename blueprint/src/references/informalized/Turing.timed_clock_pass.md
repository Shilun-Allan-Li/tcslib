<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_pass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete clock countdown pass

**Claim.** From the six-tape lift of a pending-action configuration with clock word $b_s$, after $2|b_s|+2$ steps the interpreter reaches the borrow phase with head at $|b_s|$ and with the clock word and carry produced by subtracting the incoming borrow from $b_s$.

**Proof.** The first transition enters the clock-rewind phase with the same clock word and head at $|b_s|-1$ (`timed_clock_start`). The rewind result (`timed_clock_back`), used with $j=|b_s|$, takes $|b_s|+1$ further steps to reach borrow control with incoming carry true, unchanged word, and head at $0$. The borrow-pass result (`timed_clock_borrow`) then takes $|b_s|$ steps to compute the fixed-width subtraction and move the head to $|b_s|$. Concatenate these three runs using the run-joining identity (`timedCut_run_join`). Their step counts sum to $1+(|b_s|+1)+|b_s|=2|b_s|+2$, as claimed.

**Key facts.** `Turing.timed_clock_start`, `Turing.timed_clock_back`, `Turing.timed_clock_borrow`, `Turing.timedCut_run_join`.
