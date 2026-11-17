<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBlock_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Snapshot Encoding

**Claim.** The encoding that concatenates a snapshot's state code and the two-bit codes of its input and work-tape symbols is injective.

**Proof.** Suppose two snapshots have equal encoded blocks. Applying the state-slice projection to this equality shows that their state codes agree (`Complexity.clBlock_state`); since decoding is a left inverse of state encoding, the states are equal. Applying the input-slice projection shows that their input-symbol codes agree (`Complexity.clBlock_input`), and the left-inverse property of the two-bit symbol decoder makes the input symbols equal. For each work tape, project to its work-symbol slice (`Complexity.clBlock_work`); the same left-inverse property makes the symbols on that tape equal. The two snapshots have equal state, input symbol, and work-symbol function, hence are equal.

**Key facts.** `Complexity.clBlock_input`, `Complexity.clBlock_state`, `Complexity.clBlock_work`, `Complexity.clSymbolDecode_code`.
