# MIG-1 revision 2: independent source review

**Recommendation: retain r2 as producer delivery data; adopt no r2 source into the current
landing.** No useful new repair beyond the captured current source was identified. The producer
labels this delivery **PARTIAL**. This is a read-only source comparison, not native validation,
integration, debt acknowledgment, API approval or external-gate clearance.

## Inputs and exact delta

Parent's receipt records the exchange commit `952c0bbb70a242a00975438bc64af4bcde537f7d`, zip
4721145 bytes / SHA-256 `283c0d2771c37a59844ead5d4516309f6098260b76153fe19c3233d7ca025eca`,
4028 passing payload checksums and inert renaming of all eleven original Lean files. The producer's
reported head `246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5` is **not independently verified as a Git
object here**. No bundle, patch, script, proof or tool from the delivery was executed.

All eleven source blobs were mechanically compared against revision 1 / cp07 and an archived
snapshot of all eleven actual current wt-epad files. The snapshots and SHA-256 pins are retained
under `current-source/` and `source-inputs.json`; every r1→r2 patch hunk and all sixteen changed
proof regions were source-reviewed. This is not a fresh manual re-audit of every unchanged proof.
The one intentional concurrent update is separately archived in
`current-primitives-followup.lean.txt`: Primitives `8602e690…` → `72226a29…`, solely the private
`fwdMapVirtual_run` body/sketch using the existing `Set.MapsTo.iterate` invariant route. Its full
header, all names/imports/data and surrounding source are unchanged; the other ten pins stayed
fixed. Parent's `landing/final-tag-adoption/receipt.json` records that adoption and its separate
actual native follow-up. Reading that small delta does **not** change any recommendation here.

Revision 1 → r2 changes exactly **four** files and **sixteen existing proof bodies**:
Primitives twelve, Loop two, CertShell one, CodeSimulator one. It adds two private Loop proof
lemmas and removes private `catalogRewind`. All retained **full headers and docstrings are
literal-equal**, including the bank statements' top-level `let frame := …`; all executable
definition/table bodies, imports, attribute/option commands, visibility and retained order are
unchanged. No new public statement or definition appears in r2. Source declarations:
public **354→354**, private **751→752**. This preserves the prior delivery's already-reviewed
authorized public +3/−6 delta; the original pinned-base Git object was not re-verified here.

All three snapshots retain exactly the same three static RAM admissions:
`WordRAM.WordSizeComputable.mono`, `WordRAM.wordSizeComputable_logSpace`, and
`WordRAM.wordSizeComputable_of_spaceConstructible`. No target admission is reintroduced.

## Per-file source recommendations

| File | r2 versus r1 | Comparison with captured current landing; recommendation |
|---|---|---|
| TimeConstructible | Byte-identical | Also byte-identical to current. No adoption. |
| WordSize | Byte-identical | Current differs only in comments/prose; code is identical. No adoption. |
| Catalog | Byte-identical | Current has the later row-reader repairs, canonical clip/word endpoint/framed-increment factoring and shared extraction-space proof. R2 supplies none of them. Keep current. |
| Composition | Byte-identical | Current has the actual branch-independence consumer and two approved zero-space facts. Keep current. |
| Simulation | Byte-identical | Current has three approved branch shape/operation readers and the later tagged-run proof repair. Keep current. |
| Wrappers | Byte-identical | Current uses the approved branch view and explicit carrier transports; two private headers are deliberately re-expressed there. R2 does not supersede those transports. Keep current. |
| Encoding | Byte-identical | Current includes approved `CodeTM.toFinTM_eq` and the already-retired `length_bits_le_self` wrapper is absent. Copying r2 wholesale would lose that reader and restore the retired wrapper. Keep current. |
| Primitives | Deletes `catalogRewind`; edits twelve proofs | T1 retirement/four `timed_rewind` call sites and `poly_space` zero-step read already match current. Other forwarding repairs are incomplete versions of the current reader-based repairs; no new repair to adopt. |
| Loop | Adds two disjointness lemmas; changes both bank proofs | Earlier stage of our T3 work. Current uses one whole-bank reconstruction helper through published `embedEmitCfg_mapState_eq`, has the common terminal certificate helper, and has pruned the obsolete two disjointness helpers. Keep current. |
| CertShell | Four state-premise reader substitutions inside `cert_prepare_exists` | The same four substitutions are already retained within the complete current proof repair, together with vhost fields/index equations and the local initial-state override transport. Keep current. |
| CodeSimulator | Three state-premise substitutions inside `canonPreserveInstall` | Already retained inside the current complete canonical-map/embedding-state/initial-state transport repair. Keep current. |

Of the sixteen r2-edited bodies, **five** are code-identical to current: `lenStart`, `poly_space`,
`splitRestore_run`, `splitBody_rewind`, and `emitterP2_prepare_run`. The other eleven differ because
current contains fuller repairs/factoring; their original headers remain fixed. The old
`catalogRewind` is absent from both r2 and current, with exactly four current `timed_rewind` uses.

Current public source count is **361**, versus r2's 354, because these eleven files include eight
later approved prerequisite readers/facts and omit the already-retired encoding wrapper. This
different prerequisite context is not new public drift introduced by the worker. Exact names
and header differences are in `declaration-comparisons.json`. Its only current retained `def`
body differences are the `inj'` proof fields of private `emitterP2SmallIndex/PairIndex`;
their headers and `toFun` code are unchanged (`current-private-proof-field-deltas.json`).
No executable public table difference was found in this comparison.

## Confirmed remaining source limits

1. **The r2 Primitives cleanup is partial.** `fwdMap_move` now reads three action fields through
   equations, and the run-zero/run-two steps use public equations, but its work-tape cases still
   name foreign `Action.apply` in `simp` (r2 Primitives:2735–2742). `fwdMap_block` and
   `fwdMap_emit` still explicitly unfold foreign `MultiTapeTM.step` (2782, 2948, 2973).
   `fwdMap_parse` also still unfolds `pairDecode` inside its old recursion. These retained gaps
   are consistent with an overall PARTIAL verdict and are superseded by current repairs.
2. **The specific finish-prose claim is too broad.** REPORT:24–26 says `fwdMap_finish` no longer
   passes `initCfg/Cfg.init` to `simp`. Source **Primitives:3010** still says
   `simp [fwdMapCfg, fwdMapVirtual, MultiTapeTM.initCfg, Cfg.init]`; only the output subgoal at
   3011 was changed to `pairEncode_eq`. Retain the report verbatim, but do not repeat this claim
   as source-verified. The new public `pairMapSndTM_computes` pairing rewrite itself is a routine
   existing-reader repair already covered in current.
3. **The Loop bank seal has a narrower scope than the standing strong check.** Both complete
   bank proofs still explicitly unfold `Cfg.mapState` at **4465, 4489, 4528, 4554**, in
   `simp only [emCallEmbeddedCfg, Cfg.mapState]`. The delivered `Seal_LoopR2` uses only the
   model14/Simulation5 guard; `Cfg.mapState` and `embedEmitCfg` are absent. Moreover explicitly
   naming a definition in `simp` would bypass irreducibility anyway. Its producer-reported PASS
   cannot certify these full proof regions against our stronger foreign inventory. The large
   repeated bank scaffold and the common terminal suffix also remain in r2; current factors them.
4. **E3 does not establish a new API requirement for the current context.** VirtualInput's
   existing `simps` fields publish `vhostCfg_state/inputPos/workTapes/workTapePos/output`
   (VirtualInput:147–148), and the current CertShell consumes them plus the existing buffer/bank/cap
   equations. Current CodeSimulator derives its local canonical-map equality through the
   published `Cfg.mapState_eq_of_fields` and existing `Cfg.ofWords_*` fields. A new public
   `Cfg.ofWords_mapState` is unnecessary for that tested repair route. This is not an assertion
   that every possible earlier import context has the same API, or approval to add a new reader.

These are source observations about retained gaps, not new debt acknowledgments. R2's admitted
incomplete T2/T2b/T3/T5 and E1/E2 descriptions do not discharge any current landing hold or user
decision. Shared-first-entry, constant-space and home decisions remain parent-owned; this review
adds no new approval and neither resolves nor reopens them.

## Validation boundary

The producer claims a 641-module sweep at its second revision commit, then a 223-module Primitives
closure sweep at the reported r2 head, sixty selected standard axiom walks, fresh screens and its
own census/freeze. Those are **producer claims / supplied artifacts**, not runs performed here.
Root is independently checking that evidence and bundle identity. Different-base compiled
non-private counts must not be compared directly with our prerequisite-baseline census, and
compiled constants must not be confused with the 354 public source declarations.

No native elaboration, seal, screen, replay or compiled-metadata verification of r2 was run by
this review. It does not extend previous passed probes to these r2 blobs, nor certify every
current proof. Root retains its current frozen source/test pins and decides any adoption.

The retained parser is our own pure data code: no payload/repository tool script was executed.
No source outside this review folder was changed; no Git operation, fetch, integration, cache,
snapshot, screen, Lean, push or commit occurred.
