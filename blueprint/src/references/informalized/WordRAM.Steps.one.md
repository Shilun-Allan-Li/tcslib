<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.Steps.one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A One-Step Run

**Claim.** If one step of a program starting at configuration $c$ produces configuration $c'$ rather than halting, then $c$ reaches $c'$ in one step.

**Proof.** By definition, a run of one step consists of an intermediate configuration together with the fact that one machine step reaches it, followed by a zero-step run from that configuration to the endpoint. Choose $c'$ itself as the intermediate configuration. The given step equality supplies the first fact, and the zero-step run from $c'$ to itself follows from reflexivity of equality.
