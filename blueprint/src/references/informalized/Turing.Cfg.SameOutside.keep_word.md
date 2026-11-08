<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Cfg.SameOutside.keep_word -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A stored word is preserved outside a footprint

**Claim.** When two configurations’ tapes agree outside their footprints, any specified word stored on a tape at positions outside the footprint remains stored there in the second configuration.

**Proof.** Fix an offset $p$ in the stated range. The position $o+p$ lies outside the footprint, so agreement outside the footprint says that the second tape’s value there equals the first tape’s value there. By hypothesis, the first tape’s value is the value prescribed by the buffer representation of $w$ at $p$. Combining these equalities gives the required value on the second tape. This holds for every offset in the range.
