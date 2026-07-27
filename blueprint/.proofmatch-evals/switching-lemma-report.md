# Switching Lemma fixture evaluation

- Source: `blueprint/src/references/switching-lemma.pdf`
- Local extraction: `blueprint/src/references/switching-lemma.raw.md`
- Validated Markdown: `blueprint/src/references/switching-lemma.md`
- PDF SHA-256: `b5e074215b9e0121d54f205bd83f4ab4e47b00b42a5b8d7e2691117e5b3b7ec3`
- TCSlib theorem: `SwitchingLemma2.switching_lemma`
- Automated verdict: `same`
- Confidence: `0.98`
- Estimated OpenAI spend: `$0.199915`
- Budget cap: `$1.00`
- Blueprint status: approved and linked
- Upstream mapping status: validated; theorem-level approval inherited

## Conversion evaluation

The local extractor recovered all four pages but exposed the expected failure modes:
fragmented reading order, detached overbars, split inequalities and exponents,
broken function/set notation, display equations emitted out of order, ligature
substitutions, and repeated page furniture. Codex repaired those passages while
preserving page provenance. The validated document has stable block anchors and
retains the full lecture notes rather than only the target proof.

## Matched proof source

The theorem statement is:

- `pdf-b5e074215b9e-p001-b008`

The proof is:

- `pdf-b5e074215b9e-p002-b001`
- `pdf-b5e074215b9e-p002-b002`
- `pdf-b5e074215b9e-p002-b003`
- `pdf-b5e074215b9e-p002-b004`

The automated comparison found the same mathematical structure: canonical
decision-tree construction, extraction of a length-`d` path from badness,
encoding into a shorter restriction with auxiliary data, decoding/injectivity,
the `(4w)^d` fiber bound, and the final restriction count yielding
`(10σw)^d`. Lean makes the construction, invariants, and arithmetic lemmas
explicit, but no mathematical discrepancy was found.

The proof-source annotation was written to the corresponding blueprint theorem
after explicit human approval.

## Upstream declaration mapping

The dependency-level stage mapped all 173 declarations in the flattened Lean
proof closure to the approved Markdown proof context:

- 57 declarations were classified as `direct`.
- 116 declarations were classified as `context`.
- Every declaration cites at least one validated block.
- No declaration name or block ID is duplicated or omitted.
- The estimated additional mapping spend was `$0.222141`, for an estimated
  fixture total of `$0.422056` under the `$1.00` cap.

The generated manifest and grouped audit passed deterministic fingerprint,
closure, relation, and block validation. Granular provenance inherits the
approved theorem-level correspondence and does not require a second review
gate. All 173 `\proofstep` entries were written atomically to the theorem
environment, and the dataset parser preserves their dependency order.
