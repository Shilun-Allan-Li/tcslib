<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationValidity_literals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variable Indices Stay Within the Bound

**Claim.** Under the stated lower bound on $C$, every variable in every clause of the configuration-validity formula has index less than $C(s+n+1)$.

**Proof.** A clause comes either from the relabeled core validity formula or from the padding constraints. For a core clause, relabeling sends each codec bit to its index under an equivalence with the finite interval of all codec bits. Each such index is below the number of codec bits, which is at most $C(s+n+1)$ by `codecBit_card_le`. For a padding clause, its index is the starting padding index plus an offset in the range used to enumerate positions below $C(s+n+1)$; hence it too is strictly below that bound.

**Key facts.** `Complexity.codecBit_card_le`.
