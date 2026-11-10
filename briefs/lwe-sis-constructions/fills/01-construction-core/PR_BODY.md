The direct Regev and SIS construction-core modules now prove their 31 audited
obligations: canonical modular parsing, bounded-error bit decoding, every-coin
symmetric-encryption correctness, the concrete two-DLWE-advantage bound, binary
collision-to-SIS reduction, and compression/nontriviality/bit budgets for the
dyadic SIS profile. Definitions and signatures are unchanged from the passing
statement freeze `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`.

Validation: a fresh serial 68-module sweep through `scripts/lean_check_tree.sh`,
full owned-constant axiom inventory, source freeze comparison and scoped style
checks. There are zero new admissions and 17 inherited warnings. Evidence and
precise counts are under `briefs/lwe-sis-constructions/fills/01-construction-core/`.
No whole-library root build or machine-level primitive-security theorem is claimed.

This PR targets `cryptography/lwe-sis-constructions` and depends on audited PR
#236. The user approves and merges. The statement audit passes 0/0/0/3; the proof
audit is not yet selected or dispatched. Reference ingestion/matching, relevant
integration checks and later sampler/efficiency/primitive bridges remain open.

Shared overlap: the earlier small root/Encoding/LWE facade export changes remain
in their separate export commit; the proof fill adds no export or shared-owner
edit. Three precise Mathlib imports use the existing pinned cache. Pins,
Pass–Shelat/Arora–Barak records and shared interfaces are unchanged.
