<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Field_fields -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Packed Fields

**Claim.** For a finite list of bit strings $w_0,\ldots,w_{m-1}$, a tail $r$, and any $i<m$, selecting field $i$ from the packed encoding of the list followed by $r$ returns $w_i$.

**Proof.** Induct on the list of fields, allowing the selected index to vary. For the empty list there is no index below its length. For a nonempty list $w::ws$, index zero selects the first field: the encoding is a pair of $w$ with the encoding of the remaining fields and tail, and decoding a pair encoding recovers both components (`pairDecode_pairEncode`), with `clPair_append` ensuring the tail stays in the second component. For a successor index, first decode and discard the leading field. The tail operation composes according to `clA5Tail_add`; after this shift, decoding the selected field is exactly the induction hypothesis for the shorter list.

**Key facts.** `Turing.pairDecode_pairEncode`, `Complexity.clPair_append`, `Complexity.clA5Tail_add`.
