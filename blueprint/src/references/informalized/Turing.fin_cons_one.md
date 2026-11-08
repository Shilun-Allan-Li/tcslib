<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.fin_cons_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Consing onto a One-Entry Function

**Claim.** For every optional Boolean value $w$, consing $w$ onto the empty function on a zero-element type gives the constant function with value $w$ on the one-element type.

**Proof.** Two functions are equal if they agree at every input. There is only one index in the one-element type; evaluating both functions there gives $w$, so they agree.
