<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Native input decoding

**Claim.** Decoding the embedded image of an optional enlarged-alphabet input symbol gives exactly its optional retracted symbol.

**Proof.** If the optional input is absent, both sides are absent. If it is present, embedding its retraction produces a left-tagged data symbol; the sweep-input decoder removes that tag and returns the retracted symbol. These are the two cases, and the equality follows directly from the definitions.
