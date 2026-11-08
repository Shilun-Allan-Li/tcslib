# Gate119 pre-pack reuse and collision search

Read-only candidate enumeration and source inspection,2026-11-07. No Lean, screen, source/cache
change, Git mutation, fetch, commit or push ran. No gate or design/debt decision is made here.
The approvals are the current rulings.json; older proposal README labels UNAPPROVED are historical.

**Result:** no occurrence of the three proposed new names was found in the pinned committed
source population: `Turing.pairDiagTM_spaceUsed`, `Turing.FinTM.incFixedTM_spaceUsed`, and
`Turing.MultiTapeTM.exists_first_entry_of_fixed`. Related statements are classified below.
`Turing.FinTM.redirectTM_spaceUsedByTape` is intentionally an existing public name: all48
unique-blob name-hit lines belong to that theorem/index. Its one header family occurs in
Catalog. Its approved move is a relocation, not a new-name collision or a second copy.

## Exact population and method

The authoritative expanded capture is **all-local-expanded/**:531 locally available refs,
328 unique peeled commits,277 distinct TCSlib source trees,2511 distinct Lean blobs,
1167 distinct source paths and115237366 bytes read. It includes every local ref namespace,
not only heads/origin: refs/remotes/deliver/mig1-mega-{cp07,r2}, refs/deliv, refs/delivery,
fill/review/prhead refs and the archive tag are included. The initial396-ref scan is retained
as an explicitly narrower preliminary generation; its omissions were corrected by expansion.
No live GitHub open-PR list or network freshness is attested.

Full ref→commit, commit→root/source-tree, source-tree→path/blob and blob→path/size/SHA256
maps are retained without caps. Full commit hashes came from rev-parse and were object-checked;
root trees were checked and each Lean blob was read through cat-file and independently
verified against Git's full blob hash. Alias refs sharing a tree/blob are not independent
proof copies. Screen-like text-tiling tools were not used.

The pinned campaign and prepared/open PR refs include:

| Context | Full commit |
| --- | --- |
| campaign |7e5aa5f61ec05161b2fc5e5a8a2903b76ce01ac6|
| SG1 / #215 origin branch |478cd3a8dfb46094b9d8b971662f2ddadb1eccdb|
| reading API / #230 |1160c18f03fd318f0dec25738790935fa61379d4|
| MIG1 / #233 |b1f553b315f31b949076e91119473ce4070e7d53|
| new gate119 branch, pre-implementation tip |1160c18f03fd318f0dec25738790935fa61379d4|
| delivery cp07 |cbfdba8102e6a5d956a1fdd2be7518b490a5abac|
| delivery r2 |246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5|

Exact full root/source trees and source counts for these are in current-and-delivery-pins.json;
all other refs are in the expanded population. The gate119 branch is explicitly covered.
Mutable uncommitted implementation files are not represented as a new committed API head.
The pack should link/recheck the eventual committed own additions as expected additions,
not misreport their names as collisions. This review does not freeze that future implementation.

The all-blob name search is complemented by multiline declaration/body shape searches for
canonical machine resource facts, generic zero tapes, first halt, predicate stop/fixed-step
and redirect per-tape equality.150 source-blob declaration occurrences form12 full header
families. The primary header delimiter parser respects nested input := fields, delimiters,
strings and comments. Full candidate blocks and full headers are retained. All12 families
are source-inspected and classified exactly once in classifications.json.

A supplemental all-blob fixed-step/existential search has no known-file prefilter:154
occurrences form12 additional/overlapping named families, all inspected in
broad-header-inspection.json/broad-classifications.json. Its presentation-only snippets
are not declaration-freeze evidence; full blocks are retained. Literal git-grep receipts
also cover all328 pinned commits: names626 lines; shape terms23199 lines, retained without
caps. Those line counts include repeated snapshots and are not unique proofs or findings.

## Contract-by-contract reuse assessment

- **pairDiagTM_spaceUsed and incFixedTM_spaceUsed:** the exact approved all-input/all-time
  operational zero equations are absent under those names. The existing public
  `MultiTapeTM.spaceUsed_zero_tapes_eq_zero` has statement
  `tm.spaceUsed cfg t = 0` under `h_zero:k=0` (Deterministic:313). It supplies the mathematical
  proof; owner-local zero-tape shape reduction supplies its hypothesis. The new non-simp
  equations publish the useful canonical-machine specialization without a tape-count reader.
  Existing Catalog pairDup/incFixed specifications quantify some machine and bound space
  by an existential constant. They are motivating consumers, not direct equations for the
  two canonical machines. StripLast/pairConcat body hits concern other resource contracts.
- **exists_first_entry_of_fixed:** the two known private predicate lemmas emCall_first_entry
  (Loop) and emitter_first_entry (Primitives) have the intended Bool contract, with an extra
  DecidablePred stop instance. The proposed contract generalizes the alphabet and removes
  that unnecessary instance while preserving fixed whole configurations, endpoint and cut.
  Additional old private singleton/predicate variants include catalogFirstEntry and its
  f2 copy, clFirst, and xr_firstArrival/xr_firstArrival′. They are reuse candidates, not
  legally published cross-file substitutes or name clashes. Private splitEmbed/splitRestore
  rows additionally assert host safety or a concrete machine endpoint; they are not the
  same public contract. The one broader public hit, exists_exhaustiveDecider, is a concrete
  decider-existence theorem whose proof contains fixed-step reasoning, not a generic interface.
- **First-halt distinction:** published exists_first_halt (Finite:218) gives a least time
  reaching halted state none and equality with the later halted configuration. The new
  contract reaches a LIVE `some q` satisfying stop and assumes whole-configuration fixedness
  there. The existing theorem cannot directly discharge that conclusion by choosing a stop
  predicate: no such predicate represents none as some q. Both use the least-absorbing-hit
  principle, but their exposed stopping cases differ. No false collision or automatic
  claim that one is a literal instantiation of the other is made.
- **redirectTM_spaceUsedByTape:** every name/header occurrence found is the expected old
  Catalog declaration/index. The raw index i:Fin M.k is frozen; the opacity/header limitation
  is why owner relocation was approved. This search does not reinterpret that limit, add a
  k reader/cast header or verify a new proof. Root must move the exact CURRENT MIG body/doc/
  header beside redirectTM_runFrom, remove the Catalog declaration and preserve global
  uniqueness. Older source bodies sharing the header do not authorize substitution for
  that current body. Existing proposal/full-owner receipts remain separate evidence.

The complete12-family primary and12-family supplemental dispositions are machine-readable;
no candidate family was dropped because it was old, delivered, private or a false positive.
No additional design is requested by this inspection. It does not acknowledge any old
first-entry duplication or extend gate119 beyond the approved3 additions and exact move.

This is candidate enumeration plus inspection, **not an exhaustive semantic equivalence
proof**. It is limited to TCSlib/**/*.lean at locally present refs; records/proposal .lean.txt
and source inside delivered ZIPs are not falsely counted as public declarations. Named
proposal/ruling records were read as data. The actual delivery refs are covered, including
previously missed remotes/deliver namespaces. Compilation, current merge state, final
source freeze, seals and gate/replay remain other evidence.
