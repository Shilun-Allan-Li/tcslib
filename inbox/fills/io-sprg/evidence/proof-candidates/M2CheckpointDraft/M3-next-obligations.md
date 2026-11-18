# M3 next scope: all ten original obligations

Authority: the frozen `evidence/statements/proof-obligations-current.tsv`, filtered
by exact milestone `M3`; current anchors agree with the unchanged M1 files.
The next milestone includes both owners: five load lemmas and five Claim42 lemmas.
None of these ten is counted as completed by M2.

| Original full name (area prefix omitted) | Current source anchor |
| --- | --- |
| `Internal.binomial_bound` | `Claim42/Load.lean:54` |
| `Internal.bucket_tail` | `Claim42/Load.lean:67` |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:78` |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:88` |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:98` |
| `Params.errProb_nonneg` | `Claim42.lean:105` |
| `Params.badSet_expect_le` | `Claim42.lean:114` |
| `Params.cond1_prob_le` | `Claim42.lean:126` |
| `Params.errProb_le_decomposition` | `Claim42.lean:139` |
| `Params.claim42` | `Claim42.lean:155` |

The final Claim42 cutoff must be independent of the public prime parameter.
Complete the existing probability and bucket-load obligations, not only the final
`claim42` body. Additional specialized theorem-only helpers, if needed, require
explicit inventories and later seal coverage; they do not reduce this original
obligation count by renaming it.
