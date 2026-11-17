<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_dec_success_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width preservation under successful decrement

**Claim.** If the fixed-width decrement of a Boolean word $w$ returns a word $v$, then $v$ has the same length as $w$.

**Proof.** Use the specification of fixed-width decrement (`counter_dec_spec`). After substituting the hypothesis that the result is `some v`, the successful-decrement clause of that specification includes the equality $|v|=|w|$, which is the desired conclusion.

**Key facts.** `Turing.counter_dec_spec`.
