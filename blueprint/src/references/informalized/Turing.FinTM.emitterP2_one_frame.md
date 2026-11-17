<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_one_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Configuration Embedding

**Claim.** Embedding a one-tape configuration into the chosen host slot, with the given words on all other tapes and all heads at the origin, then mapping its state by $e$, gives the canonical configuration whose chosen slot contains $u$.

**Proof.** Apply the framed configuration embedding to the map from the unique source tape to the chosen slot. At that selected slot, the source word $u$ and its head at the origin give the target tape contents and head. At any other slot, the slot differs from the chosen one, so updating the family of words at the chosen slot leaves its given word unchanged; its head is also at the origin. Thus the ambient frame agrees with the target off the selected slot. State, input position, and output agree as well, and the framing result gives the configuration equality.

**Key facts.** `Turing.FinTM.emitterP2_frame`.
