<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_dec_patch_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the decremented word

**Claim.** For every Boolean word $w$, the decrement result, using the all-true word of length $|w|$ when decrement is undefined, has length $|w|$.

**Proof.** Split according to whether `decFixed w` is undefined. In that case the fallback is the replicated all-true word, whose length is $|w|$. If it returns a word $v$, successful decrement preserves length (`sc_dec_success_width`), so the selected result also has length $|w|$.

**Key facts.** `Turing.sc_dec_success_width`.
