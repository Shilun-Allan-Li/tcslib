# R1 source-envelope correction

Independent helper review found one blocker for USING the R1 declaration
attachments: every line beginning `@[` was treated as an attribute-only line,
including an inline attributed theorem. This misidentifies three of115
historical source-key envelopes as the following theorem:

- Complexity.BinArith.uHead_nil and uRest_nil become decodeNat_eq.
- TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val becomes one_div_card_primes_le.

Thus R1's three per-key source/equality interpretations are invalid; they must
not establish canonical declaration identity, an unchanged-body disposition or
an actual-Name correspondence. R1's original reports, source blobs and ZIP stay
immutable. All230 original raw ranges independently match exact Git bytes;
that byte-preservation fact does not establish declaration identity. All115
keys,145 old head+7 separate S2 base-source diagnostics remain retained.

The peer report gives actual lines and witnesses. The source-line inverse map
in the native runner is independent and exact; its legacy qualified-name
annotations are not actual Name identities. Root assigned a fresh R2 parser,
regression cases and rebuilt preflight. Future attachments must use the raw
source_line and corrected envelopes, with ambiguity unresolved. No R1 attachment
has been executed or used for merge acceptance. The native replay does not use
this parser and continues on unchanged Lean source.

This corrects the broader source/equality wording in the historical preflight
and backup descriptions. It is not evidence of a changed Lean statement/body
or a failure in the native bootstrap. Current seals/axioms and complete failure
dispositions remain pending; no inherited waiver is inferred.

**Not yet clear to merge — use corrected R2 attachments and complete native/Rule10 checks.**
