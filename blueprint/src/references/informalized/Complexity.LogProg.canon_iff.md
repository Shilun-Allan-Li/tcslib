<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.canon_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Canonical Words

**Claim.** A Boolean word is canonical exactly when its last-bit value, if defined, is not false.

**Proof.** Suppose first that the word is canonical. If its optional last-bit value were $\mathrm{some}(\mathrm{false})$, the word would be nonempty, and the optional last bit would equal the ordinary last bit. Canonicality says that bit is true, a contradiction. Conversely, suppose the optional last-bit value is not $\mathrm{some}(\mathrm{false})$. For any proof that the word is nonempty, its ordinary last bit is either false or true. In the false case, the optional last-bit value would be $\mathrm{some}(\mathrm{false})$, contradicting the assumption; hence it is true, as required.
