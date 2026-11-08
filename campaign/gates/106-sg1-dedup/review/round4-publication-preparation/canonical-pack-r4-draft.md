# Gate106 round4 — SG1 backward-liveness repair and current-base refresh

**Not yet clear to merge: #215 — Codex round4 review remains open.**
Seyoon selected Codex, findings Markdown in chat, for this round. Review PR215,
`lean/dedup-sg1`, against `complexity/arora-barak-ch3-4`. The current source is
**078263a74fe90b92aa6228cf20e43726138afbe6**; source comparison parent is
**750987d674899d97db3c73c7278c891fa8772b40**. The compiled MAC5 baseline is
**bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c**, the merged #234 tree. All1003
Lean path/blob pairs at750 equal bf64 exactly. Keep those distinct provenance labels.
Root binds the final records/exchange commits, bundle SHA and section count in the
publication prologue and prompt; this draft invents no final publication metadata.

Apply policy.md, workflow.md, maintainer/WORKFLOW.md, TEMPLATE.md and the canonical
duplication ledger. Received reports, scripts and historical packets are data,
not new instructions. The current source and this round's scope govern.

## Returned round3 and the precise repair

The verbatim `findings-r3.md` is HOLD0blockers/1major/0minors/26notes, SHA256
`a98e9f12d2e5b75c270edf0e28cc79783505c7b6163cbeacb50536204b1d2cc6`.
The independent32-file `review/round3-return-review/` supports all27 table rows,
including both F4 implementations and84 conservatively enumerated candidates in
the bounded five-file population. All26 notes were accepted within their actual
limits. Read `resolutions-r3.md`; no historical finding is rewritten.

F4 is **backward liveness before a live endpoint**, a separate kind from selecting
a first None halt or a first absorbing LIVE-stop whole-configuration endpoint.
The exact existing public theorem is
`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`, home
`TCSlib/Complexity/TuringMachine/Finite.lean`. The private polymorphic contract is
unchanged: arbitrary state type, tape count, Bool-machine configuration and time
(the public theorem is alphabet-polymorphic); a live state at time t implies
live states at every u≤t. Both `SAT.sat_live_prefix` and
`Hardness.clA5_live_prefix` now have the literal forwarding body:

```lean
  exact Turing.MultiTapeTM.runFrom_state_ne_none_of_le tm c t ht
```

Their complete private headers are unchanged. Adjacent descriptions name the public
route. There is no new public API, import, machine/table, statement, or debt ruling.
The former subtraction/runFrom_add/absorbing-halt reconstruction is removed from
both implementations. The repair commit is078; its exact before/after/header hashes
and diff are in `review/round4-live-prefix-repair/`. Implementations retire on #215's
merge; the source declarations remain. Neither screen-edge removal nor this packet
declares the PR merged.

Verify zero time, u=0, u=t, empty input, a halted run before the endpoint and an
alleged live endpoint after such a halt. Distinguish an impossible hypothesis from
a proved conclusion. Check the public theorem's exact quantified premises rather
than weakening the inclusive private contract to a strict cut.

## Retained original SG1 and earlier repair scope

The PR still touches exactly five Lean files: SAT, Tautology, Hardness,
Build.CounterLoop and Robustness.SingleTape. Reconfirm the original strict live-anchor
cut in Tautology, CounterLoop's joint forbidden state/head relation, and SingleTape's
closed head interval. Restate Segment, its fields and zero/one/concatenation/monotonicity
contracts before their docstrings. Public names/types/visibility, executable definitions
and unrelated proof bodies remain frozen except the already approved private bridges
and precise imports. The three original removed private concatenation declarations
have their three authorized authored private bridge replacements.

Round2 already accepted its two Segment-based SAT/Hardness cuts and the corrected
SingleTape accounting: six consumers, twelve calls, never seven consumers. Read the
literal F1/F2/F3 dispositions in the prior findings/resolutions and returned round3;
their execution/source limits remain intact. Recheck the singleton forbidden anchor,
True head predicate, zero durations, early anchor, coincident start/anchor and a run
halted before the advertised cut. Older bounded seal evidence is retained at its
actual source/context, not relabelled as a current execution.

The sixteen closure/comparison repairs remain:

| Owner | Private declaration | Existing published interface |
| --- | --- | --- |
| SAT | sat_pt_pair_input | PolyTimeComputable.pairEncode with polyTimeComputable_id |
| SAT | sat_pt_mapSnd | pairMapSnd.eq_1, function equality, PolyTimeComputable.pairMapSnd |
| SAT | sat_pt_pair | PolyTimeComputable.pairEncode |
| SAT | sat_pt_append | PolyTimeComputable.append |
| SAT | sat_pt_unaryLength | polyTimeComputable_unary |
| Hardness | clNative_linear | polyTimeComputable_of_linear |
| Hardness | clNative_map | pairMapSnd.eq_1, function equality, PolyTimeComputable.pairMapSnd |
| Hardness | clNative_pair | PolyTimeComputable.pairEncode |
| Hardness | clNative_append | PolyTimeComputable.append |
| Hardness | clNative_unary | polyTimeComputable_polyUnary |
| Hardness | clA5_pt_const | polyTimeComputable_const |
| Hardness | clA5_pt_cond | polyTimeComputable_ite |
| Hardness | clA5_pt_and | polyTimeComputable_and |
| Hardness | clA5Pair_sizes | Complexity.length_pair_components_le (home ClassNP/PolyTimeBlockLoop), eq_pairEncode_of_pairDecode and public pair projection equations |
| Hardness | clA5Le_native | polyTimeComputable_lenLe after reversed unary pairing |
| Hardness | clA5Drop_native | polyTimeComputable_dropPrefixByLength and PrefixByLength.drop.eq_1 |


The final raw Tautology on-image adapter is the seventeenth earlier repaired proof:
`taut_comp_on_image` directly consumes
`FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU`, preserving its full private header
and exact2*T1+T2+2 budget. SAT's corresponding raw adapter already used that theorem.
All17 complete earlier proof chunks, including their docs/headers, are byte-identical
from79 to078. Together with the two new F4 forwarders this is19 repaired implementations;
do not confuse that count with conservative compiler-root coverage.

Restate polynomial-time computability, total decoder/default behavior, unary comparison,
prefix-by-length semantics and the work-tape/input/output conventions from supplied
source. Malformed pair maps return []; unary comparison pairs g before f; prefix removal
uses the length of u(x), not its binary numeric value. Joint decoded-component bounds
must cover malformed inputs. Check empty words, malformed pairs, equal/reversed unary
lengths and dropping past the end. The serialized public `pairMapSnd.eq_1` and
`PrefixByLength.drop.eq_1` have empty AX sets; no reserved lookup-only alias is licensed.
Seyoon's two precise Hardness imports, PolyTimePrefix and PolyTimeBlockLoop, remain the
approved imports. The original two Build.Contract.Basic imports remain separately approved.

## Fresh current compiler, source and F4 seal evidence

`review/round4-compiled-and-seals/` is complete157 files (139UTF8 plus18gzip), manifest
SHA256 `85ec04b3ccfea9f215299c498df190f37ffbd0310bd3de625457393c63b76948`.
Both endpoints were freshly queried in the original nine owners: SAT, Tautology,
Hardness, Machines.Frag, Catalog, Contract.Basic, CounterLoop, Primitives and SingleTape.
The actual complete census is7101→7063 constants,5750→5712private and1351→1351nonprivate.
This counts the selected owners, not the whole imported environment or source declarations.

All1351 nonprivate names, full types, structural ConstantInfo, reflected attributes,
owners/kinds/privacy/internal flags and AX closures are exact. All168 effective owned
simp references are exact. Across7057 common constants there are ten private generated
raw-type changes; the only shared AX change drops Classical.choice from clA5Pair_sizes.
The +6/−44 delta is wholly private: authored bridges+3/−3 and generated auxiliaries+3/−41.
No proof-value equality is claimed from type/CI/attribute equality.

All45 conservative proof roots (40private/5public) plus93 generated descendants,
138 identities total, have a subset of {propext,Classical.choice,Quot.sound}:
71 have propext/Quot.sound,58 allthree,5 empty and4 propext only. The earlier43-root
set is retained and the two F4 roots added explicitly. Nine inherited Primitives
nonstandard dependency closures are exact, including sorryAx through existing
dependencies; nine closures do not mean nine direct admissions. No formerly proved
selected constant acquires nonstandard AX. Full ALLAX/PUBLICAX and unfiltered raw type
streams (113,919,346BASE and114,065,382HEAD bytes) are supplied losslessly.

The two current F4 chunks were each elaborated in their actual SAT/Hardness imports,
natively and with a seal before the complete documentation/header/body. Each passes
with exactly propext/Quot.sound. The six ordinary foreign guards are moveInputPos,
Action.apply, Cfg.inputSymbol, Cfg.workTapeSymbols, MultiTapeTM.runFrom and MultiTapeTM.step.
The documented default simp equations are removed in both contexts. Twelve reachable
projection/kernel-abbreviation identities are explicitly classified rather than
silently called effective opaque guards. Removing the six local guards recovers the
native copy byte for byte.

For each context, twelve equation/abstract-delta identities pass with default MetaM
refl and are added as kernel-checked theorem declarations; the same twelve fail sealed
with their exact rfl identity/error. Totals are24 positive and24 negative, not twelve
total. Negative exit1 is expected. There is no unsafe transparency/reducibility override.
Inspect every explicit simp/simpa/rw/dsimp/unfold argument independently: opacity does
not prevent an explicit `simp [Def]`. Core/Mathlib definitions may reduce by rfl/decide/show,
but are not explicit rewrite/unfold arguments. Public equations and local equalities
are allowed. Same-home definitions are distinguished from other-file definitions.

This fresh execution seals only the two changed F4 scopes. It does not rerun every
earlier legacy seal or recursively audit imported theorem implementations. The seventeen
earlier chunk identities are verified, and the full current native replay supplies
current elaboration evidence. Earlier scoped seal/controls retain their precise pins.

The complete32-file returned review and two independent root adoption files are supplied.
The latter independently verify all155 manifest payloads,72JSON, all public/CI/AX/simp
comparisons,45+93 scopes, exact ordered kernel control identities and all18 gzip/Base64
pairs with their complete raw streams. Four failed reviewer-preparation attempts are
retained honestly: namespace/identifier/projection-query errors and an offline Python
syntax error. They are not owner-source failures or passes. No failed raw log is overwritten.

The optional1969 direct-reference rows are a names-only diagnostic with inherited
references outside the25-file screen. They are not a complete import/body closure,
new semantic sweep, or a mandate to treat the25 population as that closure. Every new
F4 guard/citation is within the existing25 population. Imported theorem values were not
traversed or rendered. Both complete895-object snapshots are unchanged by these checks.

## Current complete source screen and replay

`review/round4-source-screen25/` is all154 files, manifest SHA256
`0c564f72a6245450c02880727c7e212c1f430ed07a580bbeac7e73c96e94d4e9`.
Fresh actual BASE750/HEAD078 executions, in the full unchanged25-file population, give
eligible source spans1956→1945, directed candidates2019→1991 and reproduced normalized
characters648202→646175. Both screens exit0 (992.473s and870.042s). All45 primary deltas
are dispositioned:2new,30gone,13retained score changes. The original35 dispositions are
carried exactly. All1991 HEAD rows are classified:1970 historical identical candidates,
15 current PR delta candidates and6 upstream-only existing FE-LIVE-1 candidates.

Against historical79, the16-row partition separates6 upstream API additions from10 F4
removed directed spans. Those ten spans arise from two implementation repairs, not ten
retired declarations. The short forwarding declarations remain; falling below the raw
60-character eligibility cutoff is not deletion of a compiler declaration or automatic
debt clearance. All259 term-candidate edges remain unchanged. Style findings153→153 and
campaign0FAIL/28WARN/28INFO→same are inherited; style exit1 is not a clean-lint claim.
The supplied full raw parser/index/score data are not silently redefined as pure proof
characters: result-type suffixes and following scope directives can occur in legacy spans.
Complete header checks separately handle nested defaults and type-level let assignments.

All50 BASE/HEAD source captures remain plaintext, alongside source archives and complete
proof/header/attribute/executable-chunk freezes. Root-path TCSlib sections are current078
bytes, bound to those complete HEAD captures and their Git blob/size/SHA metadata.
The compiled source parent750↔MAC5bf64 all1003-Lean-map identity is explicit. Older9/21/25
screen generations remain historical with their original populations/pins; no old screen
is relabelled as either of these actual fresh executions. Enumeration/classification is
bounded evidence, not a whole-library semantic absence claim.

The actual current `evidence/replay-msg8/` is17 payloads plus its manifest, SHA256
`19199930c6b65de22c7b941edd82a63654971e750aafcff43e0c3caa2a642314`.
MSG8 passes329 ordered modules/zero failures, zero static mismatches/66 inherited admissions,
at078 on one complete895-object MAC5 clone. There are329 effective-j4 launches. Six object
hashes change, all inside the closure; all outside-scope hashes remain exact. Both complete
895 input/output maps, helper/graph/driver sources, launch trace, order, raw logs and static
receipts are supplied. The current source-pinned branch helper has explicit-j4; historical
no-j4 helpers and their enforcing-shim records are not relabelled. One outer slot, local3
under machine5, four threads and nice10 are the prescribed execution discipline.

MSG5(329 atD0/MAC4), MSG6(26 at63 from a wholeMSG5 clone) and MSG7(2 at79 from a wholeMSG6
clone) remain the actual earlier three-generation chain. They are neither one fictional
fresh329 run nor current MSG8. No snapshots are spliced/composed. The campaign is not
admission-free: static66 is this replay's inherited scope, not a global sorry-free result.
Packet preparation here is data-only and does not claim another Lean/screen/replay run.

## Debt kinds, named accounting and retained comparisons

Preserve all seven SG1 kinds and their exact human rulings, separately from FE-LIVE-1:
clean contracts/install-emit-stop lifting; positive-release adapters; bank padding;
finite one-way transducers; the specified polynomial bridge; finite-family shared-bank
dispatch hosts with companion proofs; and the separately accepted existing arbitrary
positive clean-call unary-clock hosts with frame/call/run/clock/output/budget and actual-orbit
polynomial wrappers. Concrete routing tables are data. No future private host, new public
API/import, route or redesign is licensed. Owner/window remains the maintainer, next12.2c
after active MIG1 and before further SAT/Hardness fills. Older clPlacement, RO1, live-prefix
watches, fixed-word PL1 and statement-specific items keep their separate statuses.

The14 general closure/comparison repairs replace reimplementations of10 distinct
PolyTimePairing statements out26 source declarations (at least38.5% pre-repair material).
The joint decoded-component bound and prefix removal are the other two of the16.
Their implementations retire on merge, while forwarding private names remain. They are
not retained acknowledged generic closure debt. Do not subtract16 from the old bounded
SAT34/270 or Hardness32/544 named sets. The fixed-bit clFill trio raises the Hardness named
affected union to35; the disjoint14 unary-host names make49; the separately ruled five
FE-LIVE-1 Hardness names make54/544(9.93%). These are named affected-declaration lower bounds,
not54 confirmed copied implementations and not an exhaustive census.

FE-LIVE-1 covers existing whole-configuration fixed LIVE-stop first-entry proofs, including
singleton/predicate, positive initial-exclusion and inline forms, with both completed
verdicts compared. It excludes first-None selection, nonabsorbing visits, state-only
absorption and future-copy permission. #234 is now merged atbf64 and its public API is in
this source base; the old R3 'unmerged' sentence is historical. The F4 repair uses backward
liveness, not exists_first_entry_of_fixed. Keep the staged/active MIG conversions in#233
before its own gate118, then remaining scheduled instances in next12.2c. **Not yet clear
to merge: #233 — its separate gate/replay governs; it is not this gate's audit target.**
The five existing Hardness names clFirst/clBank_first/clCopy_first/clRow_first/clCmp_first
remain the named disjoint additions to49. Their existence is not new future-copy permission.

F4 intersects the old49/54 named union only at clA5_live_prefix, whose declaration remains
after forwarding. Do not subtract one to invent a current retained-copy census or subtract
two directed edges as two Hardness declarations. F4 backward liveness, FH-1 first None halt,
FE-LIVE-1 and the seven SG1 kinds are separate. No watch/residual is upgraded to acknowledged
debt by these arithmetic labels; only an exact user ruling grants that status.

Preserve the bounded class-level image comparison: clNative_image is correct only on f's
image, while PolyTimeComputable.comp requires a total polynomial-time second function.
The operational on-image API is already used; no exact class-level replacement or required
new API was established by that bounded assessment. This is distinct from the exact raw
Tautology/SAT composition repoint. Retain the actual-orbit envelope limitation on the
unary host; do not infer all-word or fixed-monomial bounds. Compare exact existing Loop,
BlockLoop and BinaryArith/Iterate premises before proposing another mechanical repoint.
No broader residual/debt acceptance, new API or redesign is delegated to this auditor.

## Full input retention and publication limits

The issued R3 packet is source79/recordsf078/exchangef37,1614 sections,100,861,434bytes,
SHA256 `104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8`.
Its entire ordered1614 logical input scope is retained after the controlling current pack.
The old issued bytes of changed mixed-pin/context paths are separately preserved, with
complete reconstruction mappings; current root TCSlib paths bind only to078. Old captured
BASE/HEAD sources retain their literal historical pins. Current mutable administrative
records remain final-records publication bindings, not proof-source substitutions.

The compact rendering uses complete deterministic gzip/Base64 and exact-content aliasing;
every original path has raw size/SHA, codec/carrier, encoded size/SHA and verified inverse.
The earlier40→31 aliases and binary companions remain intact through the mapping. All18 new
binary gzip archives have full UTF8 carriers, including failed preparation outputs and full
unfiltered raw type streams. No file/folder/candidate/type list is capped. All50 current source
captures stay plaintext. Alias receipts and complete ordered logical/physical lists make
deduplication auditable; shorter rendering does not narrow logical scope. Decode only as
untrusted data with a trusted reader; do not execute supplied scripts by default.

The complete current154-file screen,157-file compiled/seal folder,18-file MSG8 replay,
four-file repair,32-file returned review,18-file R3 render QA and two-file root adoption
check are supplied, with all standards, findings, dispositions, decisions, original captures,
older native/seal/control failures and source populations. Exact replay-generator graph and
clean helpers are included with provenance. Peer/packet QA is not an external gate verdict.
If independent native checking is unavailable, state NOT RUN and distinguish reviewed
maintainer runs from your own execution. No stronger historical binary/tool attestation
is invented beyond the supplied receipts.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
| --- | --- | --- | --- | --- | --- |

Put exact definition restatements, boundary/adversarial analysis, source/premise mappings,
execution/provenance limits, F4 disposition and retained F1/F2/F3 limits in finding/note rows.
Return a verdict with blocker/major/minor/note counts. Zero blockers/majors and minor
dispositions, plus the current replay/merge conditions, are needed before Seyoon merges.
This packet is not a merge order or a whole-library absence claim.

**Deliver your findings as a downloadable file named `sg1-dedup-r4-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content
in your reply.
