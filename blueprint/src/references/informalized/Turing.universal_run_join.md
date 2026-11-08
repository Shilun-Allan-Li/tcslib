<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_run_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Machine Runs

**Claim.** If running the machine for $s$ steps from $a$ yields $b$, and then for $t$ steps from $b$ yields $c$, running it for $s+t$ steps from $a$ yields $c$.

**Proof.** The run-addition law says that running for $s+t$ steps is the same as first running for $s$ steps and then running for $t$ more steps (`Turing.MultiTapeTM.runFrom_add`). Thus the first stage ends at $b$ by hypothesis, and the second stage ends at $c$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
