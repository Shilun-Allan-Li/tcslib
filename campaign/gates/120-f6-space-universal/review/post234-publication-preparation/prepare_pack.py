from pathlib import Path
import hashlib,difflib,json
P=Path('/private/tmp/f6-post234-publication-preparation');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G='campaign/gates/120-f6-space-universal';H='073baa518700adc3d4b241cb48d2c78401549309';B='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c'
s=(R/G/'review/root-adoption/canonical-pack-after.md').read_text();original=s
assert hashlib.sha256(s.encode()).hexdigest()=='d274eb2a236a13ce9f5dccff51618ade1d78a1a89080598b4acfac812cf20ff6'
def replace(old,new):
 global s
 assert s.count(old)==1,old[:100];s=s.replace(old,new)
replace('**Clear to merge: #234 — separate gate119 is CLOSED PASS0/0/0/17; it is still unmerged and none of its new APIs is a prerequisite imported here.**','**Merged prerequisite: #234 — gate119 CLOSED PASS0/0/0/17; Seyoon merged it at\n`bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c`. The actual F6 branch now contains that campaign\nmerge, with the existing F6 proof bytes unchanged.**')
replace('- Candidate source: `0d0950caeb39300b5cc9bf41e5f07392fb26d3e5`.','- Candidate source: `'+H+'` (the actual clean pushed post-#234 merge head).\n- Unchanged proof component: `0d0950caeb39300b5cc9bf41e5f07392fb26d3e5` (historical source pin).')
replace('- Exact proof/comparison base: `3023dc1408c3d216fc07a7cbba9ae30135b861ed`, including merged #229/#230.','- Current exact comparison/campaign base: `'+B+'`, including merged #234.\n- Historical pre-#234 comparison: `3023dc1408c3d216fc07a7cbba9ae30135b861ed`; its old runs keep that pin.')
replace('Later #234/MIG-1 interfaces were not imported into this proof base.','The current import context contains the merged #234 API homes. The19 F6 proof chunks do\nnot consume the new fixed-live-stop or canonical zero-tape APIs: their exact contracts do not\nreplace F6\'s first-None-halt/first-return and physical-bank ledger obligations. MIG-1 remains\na separate unmerged fill; no prospective MIG proof is assumed here.')
replace('Current0d directly cites that theorem,','Current073 directly cites that theorem,')
start=s.index('## Executed maintainer evidence — distinct from producer claims');end=s.index('## Producer execution, checkpoints and process limits')
new='''## Executed current maintainer evidence — post-#234 context

The primary current evidence is `review/post234-context-review/` (86files), actual MF63 and
the fresh full25 source comparison below. Historical metadata/seals/native1/native2 and
MF61/MF62 remain supplied at their original source pins. Identical proof bytes or identical
outputs do not relabel an old execution as a new one.

**Both current compiler endpoints were freshly executed:** BASE imports whole895-object MAC5
at the merged campaign bf64; HEAD imports whole895-object MF63 at actual source073. Their
unfiltered native inventory runs pass28.908s/28.057s,0errors/warnings. Every Hierarchy-owned
constant is retained, including private/internal/generated auxiliaries; full raw types,
metadata, ALLAX/PUBLICAX, exact maps and complete target/F6 subset are supplied losslessly.
No theorem proof value was pretty-printed by these fresh probes. The BASE15714695-byte and
HEAD24764752-byte raw outputs are byte-identical to the old outputs, as a verified metadata
comparison only; actual fresh requests/receipts establish these new contexts.

| Population | Current BASE | Current HEAD |
| --- | ---: | ---: |
| All owner constants / ALLAX |138|193|
| Nonprivate / PUBLICAX |5|14|
| Nonprivate and noninternal |4|4|
| Private |133|179|
| Definitions |13|13|
| Theorems |125|180|
| sorry-dependent ALLAX / PUBLICAX |1/1|0/0|

Exactly55 added theorems are classified:18 authored private proofs,28 generated private
descendants and9 nonprivate/internal target auxiliaries. No source public export is added;
no constant is removed. All shared complete raw types and checked metadata fields agree.
The sole shared AX change is the target losing sorryAx. Every193 current owner closure,
the full56 target/f6 subset and all9 target auxiliaries use only propext, Classical.choice,
Quot.sound or subsets. `space_universal` uses exactly those three; private f6_seam and public
seamCompTM_step use propext/Quot.sound. Unrelated inherited admissions are not proved or erased
by this scoped accounting. The producer's56-inventory/47-individual-AX omission remains
resolved by complete maintainer accounting, without rewriting its delivered records.

**Fresh actual-source native and19-section scoped checks:** current073 copies pass
7.578s/6.151s,0errors/warnings/sorries, against complete MF63. All35 ordinary TCSlib guards
plus Nat.bits remain36 effective definitions; model default3 simps are disabled and guards
precede complete docs/headers/bodies. Exact instrumentation removal recovers the unchanged
550c59source. Fresh72 kernel-checked positive identities and72 precise intended negative rfl
identities reconcile individually; six synthetic corruptions are rejected. Current control
runs pass2.147s/2.224s, with the latter's72 expected failures/exit1, not a proof-owner failure.
All seven fresh job raw gzip/Base64 archives, exact sources, guard/identity checks and full
maps are preserved in the86-file folder.

**Explicit limits remain:**14 reducible projection/abbreviation exclusions are separate;
there is no unsafe or transparency override. The two regular public
instFintypeRewindPhase/instFintypeSeekPhase instances are not abbrevs, and their original
point/whole-equation controls close on both sides. No effective actual-instance opacity
coverage is claimed. The existing structural observations locate new use in f6_prefix's
compiled existential witness value, not its type; old sph_valid_machine also uses Rewind.
These observations do not establish that no reduction happened.

The fresh current073 arbitrary-local-Fintype diagnostic passes6.061s, retaining the exact two
extra local class binders, two inference controls and all19 guard blocks; its target has the
standard three axioms. Its1385-byte output equals the old diagnostic output. This is a
conditional diagnostic under supplied arbitrary local witnesses, not the actual frozen
header, actual-instance full opacity, theorem proof-value equivalence or a public API change.
The0d6.251s and f727.76s diagnostics remain separately pinned historical executions.

All895 objects in both MAC5/MF63 snapshots were hashed before/after the fresh checks and
remain unchanged. The source is the clean pushed073 merge head; all1003 Lean blobs equal
bf64 plus the unchanged Hierarchy proof blob. All100 prior compiled-accounting-final files
remain hash-identical. Read the current context review's exact API applicability/ABI checks:
#234 adds three non-simp theorems and the approved same-statement home adoption, with no
old definition/import/instance/simp/runtime change. No F6 source rewrite or new ruling follows.

**Preserved history:** f72 native1/full229 and old scoped6.733s/6.086s,0d native2 compilation
14.165s and its plain/scoped6.265s/6.283s, and old compiled-accounting-final100/92UTF8 remain
literal component evidence. Earlier reserved-name failures, a completed optional980644140-byte
proof-value rendering, analyzer corrections, instance-control limits and stopped/obsolete
screen attempts retain their original statuses. The optional rendering is complete lossless
data, not semantically reviewed, rerun or required for the primary current census.

'''
s=s[:start]+new+s[end:]
replace('Current root comparisons must use23 full\nfiles: issued21 **plus Inclusions and ConfigCount**. Full sources and reasons are supplied;\nneither the old21-file screen nor another campaign\'s population substitutes for this union.','The primary current comparison uses25 full files: issued21 plus Inclusions, ConfigCount,\nPrimitives and Wrappers, so every cited merged API home is included. The producer21 and\npre-#234 maintainer23 comparisons remain historical; neither substitutes for the new25.')
start=s.index('## Current replay and final source comparisons');end=s.index('## Publication input fidelity')
new='''## Current merged-tree replay and full25 source comparison

**Current actual MF63 PASSED:** actual source073 is merged/pushed over bf64. The exact
Hierarchy/SpaceComplexity two-module downstream closure ran from a WHOLE895-object MAC5
clone, with2 successful modules,0failures/errors/sorries, static0mismatches/0admissions and
2effective-j4 launches under managed pinned4.25/nice10. The complete895 input/output maps
show only Hierarchy's object changed; every other object is exact. Source/precheck/order/
generators/graph helper/logs/flags/receipt and whole MAC5 adoption are supplied. No snapshot
splice or unpushed prospective-tree shortcut was used.

MAC5 is the complete passed MFUP2 tree adopted after Seyoon's #234 merge; all1003 Lean source
blobs at bf64 equal gate119's audited F1. That adoption is not a new elaboration. Its inherited
401-module/static0/77 scope and unrelated admissions remain distinct from current MF63's
2-module/static0/0 result. The fresh metadata/owner/scoped/control/witness evidence above
uses actual MAC5/MF63; the fresh screen below uses exact bf64/073 source. Earlier pending
sentences in merge/prelaunch receipts are as-of chronology, superseded by completed evidence
without modifying those receipts.

**Historical chain only:** MF61 passed229modules at
`f72a807e2376a2b986675c992745d6affc23b96f` from complete MAC4/3023 with21 inherited admissions.
MF62 passed the two-module tail at0d from a whole MF61 clone, reproducing native2's owner.
All229/native1 object comparisons and all895 MF62 maps remain supplied. They do not become
a fictional current full229 execution after #234, nor certify a campaign free of admissions.

**Fresh current full25 comparison PASSED on both sides:** bf64 BASE1070.449s and073
HEAD1140.506s, each actually executed unmodified v3 under the shared lock, Python3-I/nice10,
with HEAD starting only after BASE success and lock release. Old3023 BASE output was not
adopted. All50 full source blobs/archives/inert captures/actual exports match exact Git bytes
and remain plaintext packet sections. Population is issued21 plus Inclusions, ConfigCount,
Primitives and Wrappers, covering every five-home merged API context cited here.

Eligible source spans1385→1396, directed candidates1454→1455, reproduced source-span
characters477526→477688. All1454BASE rows persist with exact retained scores; the only new
row is the already examined E3 f6_native_halt→UniversalK.ss_inputRewind_done162/321. There
are0gone/0changed retained measurements, and every1455HEAD row is classified without caps.
The new leaf's None halt and old absorbing LIVE run retain their different exact contracts.

All five concrete merged-API BASE rows are retained and dispositioned. The four first-entry
rows concern the canonical fixed-LIVE-stop kind already covered by explicit FE-LIVE-1,
with its maintainer/12.2c window, None-halt/state-only/future-copy exclusions intact. The
redirect/startup-loop row compares a shared card/membership-equation pattern in different
per-tape-equality versus total-space-bound contracts. Both new zero-tape facts cite the
public zero-tape theorem; complete short bodies remain supplied below the raw floor. F6
introduces no new pair against these merged APIs. These bounded dispositions grant no new
API/debt exception or whole-library one-fifth clearance.

The complete weighted BASE classification/file-pair matrix and all raw rows/indexes preserve
overlapping weights, floor60 and parser/type-let/scope-tail limits. Scores are normalized
source-span characters, not a pure-proof-size or semantic-copy census. All25 source checks
preserve old code/imports/attributes/terms/instances/names/privacy/order except the target
body and18private proof helpers; Hierarchy stays4→4public and43→61private. Complete19new
headers/chunks, corrected old truncated header inventories and9delimiter controls pass.
Fresh full25CLI lints have115style findings each side and campaign0FAIL/26WARN/30INFO on each
side; the private43→61INFO change is explicit. Inherited style exit1/warnings are not clean
lint claims or newly waived findings.

Current expanded25 has144 frozen files, inside the complete181-file post234 screen folder.
The prepared23 capture in its parent was never screened. Original source-screen23's95files
and the254-file resumed pre-#234 folder, including its132-file completed final23 generation,
remain byte-identical history. The original incomplete HEAD and the obsolete interrupted
f72 attempt remain failed/stopped attempts, never current successful25 comparisons.

'''
s=s[:start]+new+s[end:]
start=s.index('## Publication input fidelity');end=s.index('## Adversarial/model review and return')
new='''## Publication input fidelity

The packet retains the exact624 issued path/order prefix, full815 earlier draft scope and
all1430 pre-#234 final-preparation/root-adoption/peer sections, plus complete new current
folders and the two additional current source homes. Every original input remains literal
or explicitly losslessly represented. All old aliases, source captures, raw scores, controls,
deliveries, historical packets/reviews and attempts remain supplied uncapped. Current50source
captures are plaintext; no frozen record is relabeled or replaced in its original location.

Read post234-publication-preparation's full issued-to-current partition, inventories, folder
coverage, source bindings and reversible alias receipts. ALL root TCSlib paths are read from
git source073; every other section uses the records candidate, matching mkbundle-mixed.py.
The candidate explicitly overrides the currently HOLD-prefaced old canonical pack for root
adoption; it is not an instruction to execute or dispatch that historical draft. Fresh old
captures cover every changed issued input. The original mixed3023/f41 bundle independently
reconstructs exactly8707327bytes/SHA8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be.

Whole MAC5 adoption, actual post234 source merge/MF63, fresh193/19/72/witness context and
full fresh25 evidence are primary. Exact graph.py/transitive helpers and older gate119
closure/return context remain supplied, with #234 now MERGED. No semantic waiver, external
auditor verdict, GitHub mergeability or merge clearance is inferred. Root adopts the concrete
pack, binds the final records/source commits, verifies all rendered sections/index/checksums
and the final below100MiB size, then owns publication/dispatch. No future self-commit hash is
invented by this preparation.

'''
s=s[:start]+new+s[end:]
old='''End with `Verdict: PASS` or `Verdict: HOLD` and blocker/major/minor/note counts. An auditor PASS
is not merge permission. **Deliver your findings as a downloadable file named
`gate120-f6-space-universal-findings.md`** (the findings table and verdict line, no other
wrapping), and also paste its content in your reply.'''
new='''End with `Verdict: PASS` or `Verdict: HOLD` and blocker/major/minor/note counts. An auditor PASS
is not merge permission.

**Deliver your findings as a downloadable file named `gate120-f6-space-universal-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply.'''
replace(old,new)
assert s.rstrip().endswith(new.split('\n\n')[-1])
assert not any(x in s for x in ['still unmerged','Current0d','current0d HEAD','Final current23','must use23'])
(P/'canonical-pack-draft.md').write_text(s)
(P/'canonical-pack.patch').write_text(''.join(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile=G+'/review/root-adoption/canonical-pack-after.md',tofile=G+'/pack.md (prospective post234 candidate)')))
(P/'pack-changes.json').write_text(json.dumps({'base_draft_sha256':hashlib.sha256(original.encode()).hexdigest(),'draft_sha256':hashlib.sha256(s.encode()).hexdigest(),'source':H,'base':B,'primary_evidence':'current073/MAC5/MF63 and fresh25; all0d/23/MF61/MF62 retained history','last_delivery_paragraph_exact':True,'canonical_files_unchanged':True},indent=2)+'\n')
print('draft',len(s.encode()),hashlib.sha256(s.encode()).hexdigest())
