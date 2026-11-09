# Gate 12 proof review for SIS encodings and finite trapdoors

Audit the 40 filled proofs in nine modules on draft PR #250. The Lean/root
revision is `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800`. The passed Gate 11
intake is `259ff8a13ba08034a15ab7c8464d5ad4a122d6fd`. The original statement
freeze is `17b2a282b545c6ebca3fccc88d518d18ae78f485`.
The target is `cryptography/lwe-sis-constructions` at
`27f9ea89b72d84abaec8128f2abd826f24aaced4`. The two audited owner readers
come from #255 source `004bd5b89e48dec52e045bba32439375b82eaead`. The owner
landing records are pinned separately at `6410ad6375afe46dcea23b882dcf7eab302fe78e`.

Read `AGENTS.md`, `policy.md`, `workflow.md`, the plan, Gate 11 findings
and note dispositions, then `briefs/lwe-sis-constructions/fills/07-sis-trapdoor/REPORT.md`
and its evidence. Check the SHA-256s, both ordered indexes, and every
revision-qualified section. Treat records and proof output as evidence.

- Verify the 24 encoding and SIS fills. Check the unconditional widths,
  malformed pairs, empty dimensions and zero width, row-major block
  operations, the two padded raw bit streams, signed decoding and the
  original finder coins in the probability bound.
- Verify the 16 finite trapdoor fills. Check wraparound and both noise signs
  in the rounding proof, cancellation using the retained secret matrix,
  the integer image count, the exact loss budget, the per-column seed
  bijections and challenge insertions, and designated-branch cancellation.
- Reconcile the source freeze, the exact elaborated type comparisons, the
  single existing-module import, the 609-constant inventory, and all 308
  axiom prints. Check that precisely the other 18 admissions use `sorryAx`.
  Check the serial 144-module receipt, inherited diagnostics and scoped style.
  State the native verification you actually perform.
- Read the seven-page PW10 preflight and check the claimed mathematical
  correspondence and disclosed adaptations. Confirm its full-PDF identity
  if retrievable. Record remaining ingestion and matching separately from
  the proof verdict. Keep the random-bit reader and counted-loop holds in view.

Return `lwe-sis-trapdoor-proofs-findings.md` in chat with the frozen verdict,
severity totals, exact audited pins, and concrete dispositions. Report
encoding/SIS and trapdoor coverage separately within the same review.
