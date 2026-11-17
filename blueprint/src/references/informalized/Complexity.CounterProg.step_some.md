<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.step_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step from a Running Configuration

**Claim.** A compiled counter-program machine in control state $q$, with the specified input and work tapes and output, takes one step by applying the transition action determined by $q$, the scanned input symbol, and the symbols under the work-tape heads.

**Proof.** The configuration has state `some q`, so the machine’s step definition selects its active-state branch. The compiled machine uses `tr P` as its transition function; therefore this branch returns the action `tr P q` evaluated at the configuration’s input symbol and work-tape symbols, applied to that same configuration. This is exactly the stated result.
