# Gate127: Two existing equation readers in one private offset proof

**Prepared for Codex audit. Not yet clear to merge: #247 — external audit pending.**
Seyoon alone dispatches, rules on design/debt and merges; no audit is dispatched here.
PR https://github.com/Shilun-Allan-Li/tcslib/pull/247; branch `codex/ab34-canonoffset-bit-reader`.
BASE `9b5dcf46408db681bcbc721930ef2203fa6bc47d` / whole MAC8; audited HEAD `e16049ad20823b3e6abba171e328489746062080`.
Final records/exchange pins and bundle SHA/section count are supplied by the published
exchange README and issued prompt. Frozen private preparation wording remains historical
data; this pack and STATUS.md give the current remit.

## Source and exact scope

Only `TCSlib/Complexity/TuringMachine/CodeSimulator.lean` changes. Exactly two
reader lines change inside existing private
`Turing.MachineFormat.canonOffset_spec`:

- `change Nat.bit true (codeBitsNat w.length.bits + 1) = _` becomes
  `rw [← codeBitsNat_eq]`.
- `simp [Nat.bit]` becomes `simp only [Nat.bit_val, Bool.toNat_true]`.

Reversing only those two target lines recovers the entire BASE owner byte for
byte. All existing formal headers, docstrings, definitions, names, imports,
attributes and all other source text are exact. Public12/private196 stay exact.
No new API, import, statement, definition, machine, routing or mathematical fill.
The offset value/length contract and its complete formal header are preserved.

HEAD owner SHA256:
`8f1b19cf6893b7129e6d98ced5572633f6ed04a1b2fcd5767d04e136e7cef9c8`.
See `review/actual-BASE-HEAD.patch`, `review/qa/source-freeze.json` and
`review/literal-source-and-scope-binding.json`, plus complete BASE/HEAD source captures.

## Exact evidence table

| Input | Actual binding | Evidence |
|---|---|---|
| Actual source | BASE9b5 and HEAD e160; sole changed source is CodeSimulator | Complete `review/source/BASE` and `review/source/HEAD`; source/header freeze |
| Full replay | Exact e160 full23/static0, valid whole895 input/output, source unchanged | `review/replay/` RESULT/request, all23 module logs and compiled-source captures, full1003 source map and object maps |
| Selected compiled ABI/AX | One existing private root, all selected raw fields exact to BASE; private type-auxiliary records exact | `review/metadata/` actual request/run/raw logs and selected JSON; `review/selected-ABI-comparison.json` |
| BASE metadata reuse | Original successful fixed private-root run at identical9b5/probe/current MAC8 owner object; original attempt label retained | `review/metadata/BASE-reuse-binding.json`, raw receipt/source |
| Full target opacity | Entire target doc/header/body under codeBitsNat, incFixed and Nat.bit guards; six effective paired controls | `review/inputs/exact-adopted-full-target-preflight/` and byte-identity binding |
| Actual48 source population | Full48 captures at each side, including2 Mathlib files/root facade; no fake absent Ladner source | `review/screen-population.txt`, `review/source-capture-index48.json`, root `review/screen/REQUEST.json` |
| Fresh QA | Actual BASE/HEAD style/campaign(--check8b)/size stdout byte identical; inherited exits1 disclosed | Complete `review/qa/` receipts, raw stdout and comparison |
| Extended48 screen | Completed exact BASE/NAT exit0, 0 new/0 BASE-only directed pairs, all dispositioned | `review/screen/` full raw outputs/results/pair records and request |
| Historical old d725 | Old226-file packet is complete immutable history, with its narrower one-head seal and old33 screen | `review/historical-d725-packet/`; no old output substitutes for e160 |
| Publication | Exact source/records/bundle binding is in exchange README and issued prompt | `arora-barak-ch3-4/outbox/gates/127-nat-reader-gate/` |

## Canonical readers and contract preservation

`Turing.codeBitsNat_eq` is already imported and already used elsewhere in the
same owner. Its canonical source is
`TCSlib/Complexity/TuringMachine/CodeParser.lean:132`:
`codeBitsNat xs = xs.foldr Nat.bit 0`. Reversing this public equation replaces
the previous implicit foreign-definition conversion. `codeBitsNat_bits` then
uses the unchanged binary-decoding law.

`Nat.bit_val` is at `Mathlib/Data/Nat/BinaryRec.lean:93`:
`Nat.bit b n = 2*n + b.toNat`. `Bool.toNat_true` supplies the low true bit;
the existing arithmetic step remains. The entire length branch is exact.
The full pinned Mathlib BinaryRec source and package provenance are included.

The named48-file screen covers CodeParser and the other exact listed homes,
including Mathlib/Data/Nat/Log.lean and the actual root facade TCSlib.lean.
Convention.lean, incFixed's home, is included in the corrected named48
population and the full-target preflight inputs. The original47 request was
replaced while waiting, before any screen ran; its exact wait-only disposition
is preserved. No broader screen-coverage claim is inferred. Ladner's new module is absent in
actual BASE and NAT and omitted from both tool argument lists; no empty source
is invented. Ladner49 is a separate root-owned comparison, not this source scope.

## Complete target seal and limits

The frozen53-file preflight's proposed whole owner equals this exact actual HEAD
byte for byte. Complete-owner native check and full-target native/sealed checks
all pass with zero errors/warnings/sorry warnings. Root and same-owner helper
THEOREM/DEFINITION types AND values are traversed for the ordinary-head footprint;
imported theorem proof values remain boundaries. Projection/kernel-abbreviation
exclusions are explicit. Exact ordinary foreign TCS heads are codeBitsNat and
incFixed, with Nat.bit as the additional non-TCS guard. No default-simp
definitions need removal. All3 guards precede the complete target doc/header/body.

Six final positive kernel-checked controls and six matching negative identities
show effectiveness. incFixed uses its nil/false-cons equations; the first generic
reflected incFixed body controls fail even normally and are preserved, not counted.
No transparency/reducibility override is used. Full raw sources/logs/receipts,
explicit argument review and the full uncapped inventory are supplied.

This seals ONE complete target, not all CodeSimulator or earlier same-owner helper
proof bodies. Those earlier helpers are inspected for footprint but are unchanged
and outside this target's seal. Own canonOffset unfolding is allowed. Other
Mathlib/Core internals and imported theorem proof values stay outside the claim.
All actual target AX are standard: propext, Classical.choice, Quot.sound.

The replay-bound actual e160 metadata query passes with zero errors/warnings and
unchanged owner object. Full raw type/universes/kernel/module/privacy/kind/type
constants/simp/AX are exact to BASE. Source imports/attributes are exact and the
selected root simp flags are exact; this is not a whole environment/generated-
auxiliary metadata or proof-value equality certificate. Full raw type repr is
authoritative; consumeMData removes only outer metadata. No pp.width option.

Actual new extended48 BASE/NAT screens both exit0, source unchanged; directed
pairs2275→2275, 0 new/0 BASE-only, every identity
dispositioned in `review/screen/pair-dispositions.json`. Full raw stdout preserves all
persistent ratios/order. Extraction counts use the normalized-body>=60 filter,
not source-interface declaration counts. No helper screen was launched and no
old33 result is promoted to the new source/population. No automatic validity after another source PR merges or
composed snapshot is inferred. Root owns final actual merged-tree replay.

## Auditor checks

1. Check source pins, exact two-line whole-owner reversal and preserved private
   header/value/length contracts. Inspect every change/simp/rw/unfold argument,
   including implicit foreign conversion. Check the public equations' exact
   orientation and the complete full-target proof source/context.
2. Check exact three-head footprint through same-owner helper types/values,
   guard placement before the complete header/body, default-simp facts and all
   six positive/negative identities. Respect the explicit earlier-helper,
   projection/abbreviation and imported theorem boundaries.
3. Check one selected PRIVATE root's actual full raw type/universes/privacy/
   kind/simp/AX and type-auxiliary records against BASE, exact e160 full23/static0
   replay and complete895/source1003 provenance. Do not compose snapshots.
4. Compare complete fresh BASE/HEAD QA stdout and the exact root extended48
   screen outputs supplied here. Disposition every new directed pair. Source
   inspection/candidate enumeration and a local screen do not prove global absence.

Preserve the seven accepted SG1 kinds, FE-LIVE/FH1/BLIVE separation,54 named affected
union (not54 copies), bounded class-image residual and nine inherited Primitives
AX closures. Do not convert inherited closures or failed negative scratch controls
into new library admissions. No blanket debt permission, global clear/retirement,
new interface/import/home ruling or mathematical sorry fill follows.

Standards are complete at `review/standards/policy.md`, `review/standards/workflow.md`,
`review/standards/campaign/standards/TEMPLATE.md`, `review/standards/campaign/maintainer/` and
`review/standards/campaign/duplication-ledger.md`. Report a new unapproved copy at major;
exact acknowledged-kind accounting remains minor. Root owns adoption and gate status.

## Findings

Use `# | Severity | File · declaration | Claim | Evidence/counterexample | Proposed fix`
with blocker/major/minor/note per TEMPLATE, then verdict/counts. Identify any
unresolved source/evidence gap. Do not edit source, push, dispatch another auditor
or declare merge clearance.

**Deliver a downloadable `gate127-nat-reader-findings.md` containing the findings
table and verdict line, and also paste its complete contents in your reply.**

## Independent provenance and current context

The actual23-module exact-head replay has0 failures and static0 mismatches/0
inherited admissions. Both895 input/output maps and the unchanged MAC8 input are supplied.
Independent public input anchors are the three files under
`campaign/status/2026-11-08-mig1-merge/`: receipt.json, object-hashes.json and Lean-tree.json.
The replay input895 hashes equal that adoption, not merely a self-reported count.
Actual static helper and diagnostic helper/context are in reproduction-tools/.

Campaign changes after MAC8/9b5 are records only. Later source merges require the standing
current-tree validity check; no unmerged proposal is assumed landed. Retire only the stated
proof implementations after external audit closure and Seyoon’s merge; no global absence,
all-owned-type equality or new debt exception follows.

## Publication preparation clarifications

`review/proof-source-identity-binding.json` retains the preparation-time string
“extended48 screen PENDING root shared queue”. That field is superseded by the
completed actual48 request/results/stdout and `review/screen-status.json`; it is
not the current status. Frozen preparation is not rewritten. All512 payloads are
verified and mapped by `PATH-MAP.json`. Source indexes distinguish `.lean.txt`
captures from library sources, including the two pinned package Mathlib inputs.
Independent MAC8 anchors and the full reproduction helper/configuration set are
included beside the final canonical pack. No extra Lean module is added as evidence.

## Independent publication peer

`publication-peer/findings.md` and its complete30-payload verification inputs report
0 blockers/0 majors,2 publication minors resolved in this canonical wrapper and2 notes.
The stale preparation field and missing portable execution context are explicitly
resolved above. Every512 frozen payload and all current source/native/meta/screen
claims were independently checked within their recorded limits. The peer is not
an external gate verdict, new replay, debt ruling or merge clearance. Final bundle
pins are supplied separately after the exact mixed rebuild and archive checks.
