# F6 post-#234 context and fresh validation review

The actual standard workflow is adequate and its completed source/replay/native checks pass.
The F6 proof does not require a new API, proof rewrite or design ruling after #234. This review
is evidence for root's packet refresh; it does not close external gate120 or authorize merging
PR235. Fresh 25-file BASE/HEAD screens and final packet/index bindings remain separately owned.

## Current source and whole-tree provenance

The campaign merge is `bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c`. Its complete 1003-file Lean
tree equals the audited gate119 F1 tree at `f1ca767a10551960faf36ad9c8ff17bea3a2d88c`.
The F6 PR source is the clean, pushed actual merge head
`073baa518700adc3d4b241cb48d2c78401549309`, with both the campaign merge and the original F6
proof component `0d0950caeb39300b5cc9bf41e5f07392fb26d3e5` as ancestors. Across all 1003 Lean
paths, the current source tree is exactly the campaign tree with its single Hierarchy blob
replaced by the unchanged F6 proof. Hierarchy's SHA256 remains
`550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3`.
All five API home blobs at the actual PR head exactly equal bf64/F1. The proof, theorem header,
imports, model constants and 19 proof chunks were not rewritten for this context change.

The unpushed prospective-commit shortcut was abandoned before execution. Root merged the
actual campaign into the existing F6 branch, pushed that actual head, and replayed its exact
two-module downstream closure from the whole MAC5 baseline. No new F6 Lean source edit was
made by this review.

The whole MAC5 adoption is bound to records commit
`750987d674899d97db3c73c7278c891fa8772b40`. All six frozen adoption files match that commit's
blobs. Its manifest SHA256 is
`cbb2cd3b2d3dc12ca7d60da8ef661529731279701f16800c2164325193b148f1`.
The entire passed 895-object MFUP2 snapshot was adopted as MAC5; it was not assembled from F6
or other generations. Its original 401-module replay and 0/77 static total remain inherited
history, not a new F6 replay claim.

Root's current MF63 folder is `campaign/fills/f6/landing/replay-mf63/`, frozen manifest SHA256
`4da1e19d6508fb9aa593d9e526b725e17a7a70bdd6b7e8dadbf153bdfa5b6515`.
Every manifest member was checked. The current actual replay has exactly Hierarchy followed
by SpaceComplexity, two successful effective-j4 launches, zero failed modules/error rows,
zero Hierarchy admissions and static 0/0. Its 895 input objects exactly match the MAC5 adoption
list; its 895 output objects differ only at Hierarchy. Every object in both actual snapshots
was hashed before and after this review's native jobs and remained unchanged. The preserved
MF63 receipt's metadata/screens-pending sentence is its earlier as-of status; the fresh results
below supersede that status without modifying the receipt.

## Applicability of the newly available API

The five-source diff is exactly the previously gated addition/rehome: three new non-simp
theorems and the same-statement redirect home adoption, plus one generated proof auxiliary.
Reversing each sole proof-block insertion/deletion recovers every old source byte. Existing
imports, definitions, instances, runtime code and attribute commands are unchanged. The
3778-to-3782 compiled API comparison has no removed declarations or shared type, kind,
universe, privacy, attribute or axiom changes; the redirect theorem's owner alone moves from
Catalog to Wrappers. The source captures and exact delta hashes are retained here.

| API | Current F6 reuse assessment |
| --- | --- |
| `exists_first_entry_of_fixed` | Requires a specified live stop endpoint and global whole-configuration fixedness. The 19 F6 chunks do not re-derive that least-live-time result. Their row/host/seam cuts use existing stronger first-return contracts. Generic `f6_seam` has no fixed-stop premise and already directly consumes `seamCompTM_step`. The native live halt leaf takes a step to none, so is not fixed. `forwardLoop_forward` supplies the distinct first-none-halt contract and full later halted endpoint. No drop-in public re-point remains. |
| `pairDiagTM_spaceUsed`, `incFixedTM_spaceUsed` | Neither canonical zero-work-tape machine occurs in the 19 chunks. Pure `pairEncode` is not `pairDiagTM`. F6's physical K+4 bank and mirror/auxiliary/idle/ruler ledger require their actual per-tape bounds, rather than these canonical zero-space equations. |
| `redirectTM_spaceUsedByTape` | Global name/type are unchanged by the gated home adoption. None of the 19 chunks uses redirect; earlier non-simp availability requires no F6 source change. |

The existing FE-LIVE-1 scope/window is not broadened here. In particular, the first-none-halt
family is not silently brought into its live-stop contract. This is an applicability review,
not acceptance of debt or creation of a design exception.

## Fresh native and complete compiled accounting

All seven jobs used the reviewed byte-identical probe/control sources, pinned Lean 4.25.0,
a new private project and only the managed wrapper, with one job running at a time. All
requests, actual receipts, complete raw gzip plus Base64 archives and verification code are
retained. The inventory prints complete types, metadata, value-presence flags and axiom lists;
it does not pretty-print theorem proof values. No compiled output was written to a snapshot.

| Fresh job | Elapsed seconds including slot wait | Result |
| --- | ---: | --- |
| BASE inventory, whole MAC5 | 28.908 | 0 errors/warnings |
| HEAD inventory, whole MF63 | 28.057 | 0 errors/warnings |
| Native current owner | 7.578 | 0 errors/warnings |
| 19-section scoped owner | 6.151 | 0 errors/warnings |
| 72 native paired controls | 2.147 | 72 kernel-checked identities |
| 72 sealed paired controls | 2.224 | Exactly 72 intended `rfl` errors; expected exit 1 |
| Arbitrary-local-Fintype diagnostic | 6.061 | 0 errors/warnings; conditional check |

The BASE and HEAD inventory jobs are both fresh in this merged context. Their complete raw
outputs happen to equal the historical outputs byte for byte: BASE 15,714,695 bytes, SHA256
`19e93cc4ef86b99e20bdda7dfaf49f1fa0d7c7773e8a8aef371bb849a0042c2f`; HEAD 24,764,752 bytes,
SHA256 `fbab3bc46ebd79c996d34fa29c91432287169332522a1ca6bc2f27118cb4fb4e`.
This is verified output equivalence, not a relabeling of the old run receipts.

| Complete owner accounting | BASE | HEAD |
| --- | ---: | ---: |
| All owned constants | 138 | 193 |
| Private | 133 | 179 |
| Nonprivate, including internal names | 5 | 14 |
| Nonprivate and noninternal | 4 | 4 |
| Theorems | 125 | 180 |
| Definitions | 13 | 13 |
| ALLAX rows | 138 | 193 |
| PUBLICAX rows | 5 | 14 |
| Owned `sorryAx` dependencies | 1 | 0 |
| Target/F6 subset | 1 | 56 |

All 55 additions are classified: 18 authored private proofs, 28 generated descendants of
private proofs and 9 generated nonprivate/internal descendants of the public target proof.
There are no removals, public source API additions, shared metadata/type/attribute changes
or definition additions. The sole shared axiom-list change is `space_universal`, from
`sorryAx` to the standard three axioms. Every one of the 193 current owned constants and all
56 target/F6 rows was checked; each axiom set is the standard set or a subset. The target
uses exactly `propext`, `Classical.choice`, `Quot.sound`. Private `f6_seam` and public
`seamCompTM_step` use exactly `propext`, `Quot.sound`. Full uncapped types and both axiom views
are retained, including generated auxiliaries.

## Scoped controls and witness limitations

The exact existing guard population is retained: 35 ordinary TCSlib definitions plus
`Nat.bits`, all 19 scoped proof chunks, with the three established simp removals. Removing
only the instrumentation recovers the exact native owner source. The 72 positive identities
and all 72 precise negative goal identities/error kinds were checked individually; duplicate,
missing identity, wrong outcome, wrong exit, admitted warning and wrong-error corruptions are
rejected by the validator. The paired `MetaM` reflexivity probe uses default transparency;
there is no unsafe or transparency override.

The already disclosed 14 abbreviation/projection limitations and two ineffective regular
Fintype controls remain limitations. The fresh diagnostic preserves the exact two additional
local Fintype binders, two inference equations, all 19 guards and the target's standard axiom
set. Its success is conditional on those arbitrary local witnesses. It is not a certificate
that the actual compiled Fintype instances are opaque, proof-value-equivalent, or globally
sealed. Neither controls nor axiom inspection establishes an unrestricted imported-theorem
opacity claim.

## Disposition and publication requirements

No concrete source, ABI, axiom, provenance, scoped-control or witness blocker remains in this
bounded review. The standard actual-merge route resolves the context change without a
new public design or gratuitous proof edit. All 100 prior `compiled-accounting-final/` files
are hash-identical before/after and remain historical 3023/0d component evidence. The old
23-file screen, previous 624-prefix packet, 815 scope, complete old records and lossless
aliases must likewise retain their own exact generations.

The current screen population is 25, adding Primitives and Wrappers to the old 23 context
files so all five API homes are included. Its owner is running fresh bf64 BASE and 073 HEAD
captures/classification. This review ran no screen and makes no claim that those jobs have
finished. No API-inclusive current screen may be inferred from the old 0d captures.

Before publication, root must incorporate the separately frozen new25 evidence and this
complete folder, update the current source/base/replay/status claims, retain all historical
scope/aliases uncapped, and verify the final mixed-pin bundle and index after its records
commit: every TCSlib section from git source073, all other sections from final records. The
required downloadable-findings paragraph must remain last. This review supplies no merge,
closure or debt-acceptance action; gate120 remains externally open.

`API-context-check.json` and the early plan retain their as-of observations. The completed
results are `final-context-verification.json`, `refresh-context.json` and
`fresh-validation/summary.json`, with full maps, controls, archives and validators alongside.
