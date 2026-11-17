<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputLength.lean :: Turing.inputLengthCfg_merge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merging Configurations for Consecutive Counts

**Claim.** Under the given binary-expansion hypotheses, overlaying the bits of $n$ and then those of $n+1$ gives the same configuration as overlaying the bits of $n+1$ directly.

**Proof.** The binary carry-count fact gives $p<|(n+1).bits|$ (`Turing.inputLength_charge`). Compare the configurations componentwise. Their states, input-head positions, work-head positions, and outputs agree directly from the construction. For the tape contents, fix a cell coordinate $a$. Below the overlay origin, both constructions retain the original tape. Within the first $p+1$ cells at or to the right of the origin, the inner overlay is replaced by the outer overlay, and the direct overlay is also active there; the strict length bound ensures the direct word covers those cells. Beyond that prefix, the old and new overlay windows have the same endpoint, as follows from the two possible forms of the old bit expansion together with the assumed form of the next expansion. On this common suffix, the buffers for the two words agree: the expansions have the same symbols after the carry prefix, and the offset bound places the lookup in that shared suffix (or beyond both words, where both lookups are blank). Thus every tape cell agrees, proving equality of configurations.

**Key facts.** `Turing.inputLength_charge`.
