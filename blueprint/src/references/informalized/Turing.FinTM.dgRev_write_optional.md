<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgRev_write_optional -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optional write in a reverse-sweep configuration

**Claim.** Applying the specified stationary write action to the reverse-sweep configuration produces the configuration with the same state-independent data and output, and with right list $b$ followed by the tail of $r$.

**Proof.** The reverse-sweep write identity (`sweepRevCfg_write`) gives the desired result for the action that writes $b$, stays in place, emits no output, and enters the state represented by $q'$. The action in the claim has exactly these operational components; its state field is already the optional state $q'$. The two resulting configurations therefore agree in state, input position, work-tape contents, work-tape head positions, and output, which proves their equality.

**Key facts.** `Turing.FinTM.sweepRevCfg_write`.
