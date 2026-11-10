# Foundation representation proof fill

Frozen statements: `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`.
Filled source: `893e921bf2afeca293be9da9d495613bb1486796`.
PR branch: `cryptography/lwe-sis-encoding-proofs`, targeting `cryptography/pass-shelat-ch2-4`.
The earlier published `cryptography/lwe-sis-constructions` snapshot is left unchanged.

## Result

All 14 audited representation statements are proved. The 61 source declarations,
their order, signatures, definition bodies, instances, attributes and namespaces are
unchanged after stripping comments and theorem proof bodies. The only new import is
`Mathlib.Algebra.BigOperators.Group.List.Lemmas`, already present in the own pinned
cache inventory. No cache archive or package revision changed.

The common encoders recover blocks through the public `List.eq_iff_flatten_eq`, then
use existing numeral and vector injectivity. SIS signed decoding uses public prefix-sum
block extraction, checks its sign and magnitude, and applies the public numeral round
trip. The norm-bound corollary uses `Int.natAbs_le_self_sq` and `Finset.single_le_sum`.
All remaining lengths and budgets are direct composition and monotonicity arguments.

No new public/private helper, machine host, copied proved material, unsafe declaration
or hardness axiom was introduced. Two internal agents supplied read-only lemma/proof
research; root alone edited, checked and committed the source. Their review found no
signature/API drift or foreign-definition unfolding. This is not an external verdict.

## Verification

* Fresh serial dependency sweep: 55 modules, 146.628 seconds, zero errors, zero new
  admissions and 17 warnings in unchanged dependencies. The olean tree was newly created
  for this sweep; root's build fallback does not exist. The whole library root was not built.
* Final axiom probe: all 61 source declarations and all 166 imported elaborated constants
  use only `propext`, `Classical.choice`, `Quot.sound`; none depends on `sorryAx`.
* Elaborated constants: 61 source declarations, 100 structure-generated names and five
  compiler auxiliaries. Two new `.congr_simp` constants belong to the common encoders;
  they are explicitly inventoried and axiom-checked, not new handwritten APIs.
* Source freeze check: `verify_freeze.py` reuses the repository's comment stripper and
  compares complete source surfaces after masking theorem bodies. All 14 changed bodies
  are exactly the audited admission inventory; all 50 other frozen files are unchanged.
  This is a source invariant, not an elaborated type-hash comparison.
* Style: zero FAIL, two accepted acronym-reader heuristic WARNs over ten mathematical
  files. No linter or reader rename was made.

The 15 iteration checks include one early failed vector-length attempt, corrected by
reading `List.ofFn_comp'`. Those logs are preserved as development history. They are
not the passing gate evidence: the complete final fresh sweep and final probe supply
that evidence. No `lake build`, unfiltered cache fetch, foreign package mutation or
borrowed scratch object was used. Native jobs ran serially with owned PIDs recorded.

## Outstanding boundaries

Phase-0 statement audit PASS 0/0/0/3 is preserved verbatim under `audits/`. N01 source
PDF archival/ingestion remains open; a fresh shell download attempt still failed DNS.
N02's inherited admissions and scoped verification limits remain explicit. N03's
sampler efficiency, representation-machine bridges and useful profiles remain future
consumer obligations. This fill proves no cryptographic construction or security reduction.

Codex was freshly selected for proof review. The input packet belongs under
`lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/` on the orphan exchange;
Codex returns Markdown in chat. The user dispatches the job. Code is published only
to the own PR branch; no campaign destination or merge is authorized. Connector PR
creation returned HTTP 403 and shell GitHub access still fails DNS, so no PR is claimed
until the prepared client publication command succeeds.

**Not yet clear to merge — the proofs and native checks pass; external proof review,
source archival and user-controlled integration remain open.**
