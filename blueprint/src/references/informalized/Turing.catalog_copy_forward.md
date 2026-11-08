<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_copy_forward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward copying step

**Claim.** If the source tape contains $w$ around its head as specified, then for $r<|w|$ one copying-machine step takes the prescribed forward configuration at progress $r$ to the one at progress $r+1$.

**Proof.** At progress $r$, the source head is at offset $r$ from its initial position. Since $r<|w|$, the tape hypothesis identifies the symbol there as $w[r]$. The copying machine writes that symbol at the current destination-head position and advances both heads, remaining in the sweep phase. The destination configuration therefore changes from the prefix of length $r$ to the prefix of length $r+1$: the equality of these tape functions is precisely the write-and-extend identity (Turing.catalog_write_take). The source tape is unchanged, and all other tapes and configuration data are unchanged; the distinctness of source and destination ensures these updates affect the intended tapes separately. Hence the resulting configuration is the prescribed forward configuration at progress $r+1$.

**Key facts.** `Turing.catalog_write_take`.
