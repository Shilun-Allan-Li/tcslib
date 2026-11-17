<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBodySource_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the Extended Loop-Body Machine

**Claim.** Running the source machine from a configuration obtained by adjoining the chosen tapes and head positions produces, after any number of steps, the configuration obtained by adjoining those same tapes and head positions to the loop-body machine's run.

**Proof.** This is the fixed-tape extension principle for machine runs (`leftCfg_run`). Its transition hypothesis holds here directly from the definition of the source machine: on the original tapes it uses the loop-body transition, while the adjoined tapes receive no writes and make no head movements. Therefore each step of the source machine updates the state, input head, original tapes, and output exactly as the loop-body machine does, leaving the adjoined tapes and their head positions unchanged. Applying the extension principle for $t$ steps gives the asserted equality.

**Key facts.** `Turing.FinTM.leftCfg_run`.
