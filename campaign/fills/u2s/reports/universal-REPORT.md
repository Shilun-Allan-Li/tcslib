# U2 universal machines — final fill report

Both target proofs are complete and all final Lean and source audit checks pass.
The checkpoint packaging deviation E-CHK below is disclosed separately; no mathematical
obstruction or missing-API escalation remains.

Branch: `fill/u2s-universal`. Base: `ed8f2e87146be90eb76216e9bc34f7838ec79574`.
Final commit: `2410022fee818a1206616571e6a972db9338a150`. Original UniversalK blob:
`4de5324eee700c701b0199f509084b26f77d5802`.
Item started 2026-10-25T23:35:24.422113+00:00; ended 2026-10-26T00:56:06.742322+00:00.
Agent: Codex. Delivery is this zip, with local commits only: no push or PR, no rebase, merge,
or cherry-pick. The repository was cloned once from the campaign branch; the ancestor check
passed at campaign tip `11f420d1b60711e8e77847fce3a5a6991c526eee` before branching at the exact base.

## Result and frozen scope

Both frozen contracts are proved: `Turing.exists_selfUniversalK` (time, space, converse,
and positive code-dependent constant) and `Turing.universalK` (suffix-input time and converse).
Checkpoints 1.1–1.5 and 2.1–2.5 are complete. There are no open owned declarations and no new
admissions. Both targets and downstream `Turing.exists_selfUniversal` depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

Only the five authorized regions of `TCSlib/Complexity/TuringMachine/UniversalK.lean` changed.
The first edit was exactly the supplied one-import overlay. The initial module prefix,
header/status, scheme, startup and its 39 private declarations are byte-identical to the base
apart from that authorized import. Both target statements and their complete original
docstrings are byte-identical. No Implementation status paragraph remains because neither
target is open. The maintainer-owned module status still says the contracts are sorried;
it was deliberately left frozen as instructed.

Final size: 2887 lines, 12 public and 67 private declarations, versus
1762 / 12 / 39 at the base. There are 28 new private declarations, all under `uk_`, with
docstrings and literal **Proof sketch.** paragraphs for proofs longer than 20 lines.
No new line exceeds 100 characters. There is no new public declaration, import beyond the
overlay, section/open/variable leakage, host, forwarding loop, input device, layout machine,
or input rewind. The sole new finite-state leaf is the authorized header-ruler scan.

## Construction and bounds

| Notation | Meaning |
|---|---|
| k | Number of work tapes in the coded machine |
| M | Machine `E.machine α` decoded from code α |
| R, T, B | Proved startup and its per-code time and space bounds |
| K | Startup tapes beyond its first k+2 simulation tapes |
| L, entry, C_L | H2-F forwarding loop, entry state, and additive cost constant |
| D | `50 * (length (tableBitsK M.tr) + 1) + C_L` |
| N | `K + (k + 2)`, the self-universal machine's tape count |
| ℓ | `2 * α.length + 2`, the code header length |
| H, inj, C_R | H5 ruler host, its state map, and time factor |

**U2-U.** The public R2 seam dispatches from R's first exit into the public R1 emitting
embedding of L on the first k+2 tapes. The initial-state override is explicit and read through
published equations. Initial-encoding field equations reconstruct the startup endpoint.
The least source halt supplies H2-F's live prefix. Summing its costs gives at most D*t steps.
The selected tapes use the source's visited-set ledger; auxiliary tapes use H2-F's finite
interval. Public visited-set and card equations combine this with startup space. After a
halt, the public visited-set splitting lemma shows that no new head cells are visited.
A single sufficient constant is

`C = T + 1 + D + B + N * (2 * D + 1) + N`.

It is positive and covers both `C*(t+1)` time and `C*(s+1)` space. For the converse, the startup
prefix is live by the public live-prefix lemma, and positive lockstep costs keep L live forever
if M is live forever. A completed loop output therefore comes from a source halt; public
halted-output preservation identifies the output.

Term by term, T+1 pays startup and its seam dispatch; D pays each simulated step; B pays
startup space; N*(2*D+1) pays the auxiliary interval allowance on all N tapes; and N pays
the coefficient of source space. The proved ledger is
`B + N*(s + (2*D+1)) = N*s + (B + N*(2*D+1))`. This deliberately loose bound also covers
unselected embedding tapes, whose continuation head visits a singleton.

**U2-E.** The generic leaf reads one aligned doubled header from any native input position
`1+p` satisfying `z.drop p = pairEncode u v`, marking exactly `2*u.length+2` consecutive
ruler cells. It preserves all cells outside that interval, other tapes and heads, and output.
Its return occurs first at that exact time. No private prefix index lemma is reused: input
symbols are obtained with `inputSymbolInner`, `List.getElem_drop`, and `pairEncode_eq`.
The stronger overwrite/frame statement permits consecutive scans for a two-header consumer.

The public work-tape rewind then costs ℓ+2, restores the ruler head, and has its inherited
first-return cut. The scan/rewind seam costs `2*ℓ+3` total. The original startup is embedded
with one extra tape; the ruler occupies tape k+2 immediately after the simulation bank.
The resulting endpoint has native input position ℓ+1, all work heads zero, the original
simulation bank, the ruler buffer, and empty output.

This endpoint is reconstructed as H5's presentation of L's initial configuration on suffix x.
The initial virtual input position is one, hence the tag is false. H5 is consumed exactly as
stated; `inj` is only a state map, with no injection assumption, and no device exit is treated
as stationary. The generic seam/run helper is shared with phase 1.

Set `T_A = T + 1 + (2*ℓ+3)`. A sufficient evaluator constant is

`C = T_A + 1 + C_R * (ℓ+1) * D`.

Every term depends on the code and fixed machines, never on suffix length. H5's live-prefix
clause and its lower time bound rule out a host halt while L stays live. The shared loop
converse then produces M's completed output on x. The proof covers k=0, empty α, empty
suffixes, a zero-work-tape canonizer, arbitrary canonizer time, and nonhalting coded machines.

Here T_A pays the startup and header preparation, the extra 1 pays the final seam into H5,
and C_R*(ℓ+1)*D pays the host's slowdown of each forwarding-loop step. The final evaluator
has K+(k+3) tapes: source tapes 0 through k-1, table tape k, summary tape k+1, ruler tape k+2,
and K auxiliary startup tapes. The host embeds on the first k+3 tapes.

Proposed paragraph for the maintainer (the original target docstring remains frozen):

> **Implementation.** Run the proved self-startup first, embedded with one extra tape.
> From its endpoint, the finite-state header scan marks one ruler cell per doubled-header
> symbol, and the public work-tape rewind restores the ruler head. Present the resulting
> initialized simulation bank and ruler to the public ruler host for the forwarding loop,
> with native input at the suffix boundary and initial virtual-input tag false. Reuse the
> self-universal proof's loop run, divergence, and seam lemmas. All preparation costs depend
> only on the code; the host adds the code-header factor to the simulated time.

U2-U follows its frozen construction sketch; no replacement Implementation paragraph is needed.

## New declarations and semantic duplication

Search groups below were applied to the base tree and every open PR branch (#135, #164,
#165, #166, #167), with their exact fetched SHAs and raw queries logged. No in-flight API is
cited. Every new private theorem was also posed to `exact?` with only the new definitions,
not the new helper proofs, available. All 22 sealed statements fail to close. Unsealed,
21 fail and uk_loop_init offers only `rfl`; that definitional closure is rejected, and the
implementation instead cites the proved initial-configuration transport lemma.
No public theorem states any new private theorem or a generalization that replaces it.

- S0: `forwardLoopCfg.*initCfg`, `forwardLoopCfg.*state.*none`, embedding/initial encoding,
  and the supplied route/duplication probes.
- S1: `initCfg.*mapState|mapState.*initCfg`, initial state transport, seam run and embedding run.
- S2: lockstep halt/divergence, encoded first halt, costs, cut, and live-prefix statements.
- S3: `spaceUsedByTape.*S`, `seamCompTM_visitedByTapeHead_ofCfg`, emitting visited-set frame.
- S4: ruler/header scan, `drop.*pairEncode`, writing tape action, and replicate-length ruler.
- S5: ruler-host/forwarding-loop presentation, startup embedding, and header/rewind seams.

| New private | Role | Search/result |
|---|---|---|
| uk_encode_init_tapes | Initial forwarding-loop tapes | S0; exact? fails; authorized route proof |
| uk_encode_init_fields | Initial state, input/work heads, output | S0; exact? fails; authorized route proof |
| uk_encode_halt | Encoded halt/output equivalence | S0; exact? fails; authorized route proof |
| uk_embed_init | Startup endpoint as initial loop embedding | S0/S1; exact? fails |
| uk_loopTM | R2 into R1 emitting embedding, explicit q₀ | S1; definition using public combinators |
| uk_init_mapState | General initial-state transport | S1; exact? fails |
| uk_loop_init | Initial presentation of the shared composition | S1; only unsealed rfl, sealed exact? fails |
| uk_loop_pre_live | Live startup prefix of the shared composition | S1/S2; exact? fails |
| uk_loop_run | Generic run after seam, native loop or suffix host | S1/S2; exact? fails |
| uk_loop_forward | Encoded first halt and accumulated time | S2; exact? fails |
| uk_loop_live | Loop divergence from source divergence | S2; exact? fails |
| uk_loop_converse | Completed loop output comes from source | S2; exact? fails |
| uk_loop_space | Startup plus embedded-loop space ledger | S3; exact? fails |
| uk_scanTM | Authorized finite-state header-ruler leaf | S4; no public row writes this ruler |
| uk_scanCfg | Framed marked-interval presentation | S4; owned configuration definition |
| uk_scan_zero | Zero-step scan presentation | S4; exact? fails |
| uk_scan_step | One writing/advancing scan step | S4; exact? fails; public tape-action equation |
| uk_scan_pair | One aligned doubled pair or separator | S4; exact? fails |
| uk_scan_header | Header induction from arbitrary offset | S4; exact? fails |
| uk_scan_run | Framed exact run, first return, silence | S4; exact? fails |
| uk_scan_ruler | Marked interval equals public unary buffer | S4; exact? fails |
| uk_headerTM | Public seam from scan to public rewind | S4/S5; composition definition |
| uk_header_run | Framed scan/rewind endpoint and cut | S4/S5; exact? fails |
| uk_suffixStartupTM | Embedded original startup, then header preparation | S5; composition definition |
| uk_suffixCfg | Initialized bank and ruler presentation | S5; owned configuration definition |
| uk_suffixStartup_run | Combined startup endpoint and cut | S5; exact? fails |
| uk_ruler_fields | Ruler-host field presentation | S0/S5; exact? fails; authorized route proof |
| uk_embed_suffix | Prepared endpoint equals H5 embedding | S5; exact? fails |

No external private is cited, and none of the six forbidden canonical R3 rows is used.
The only startup interface consumed is its proved public statement. The full admission
walk traverses all dependencies; the direct-citation walk stops at this existing contract,
so inherited startup implementation details are not misreported as new citations.

## Verification

- Full 97-module final sweep: zero errors; 24 sorry warnings, exactly the supplied base set
  minus the two owned targets. Every other warning header equals the bootstrap's.
  UTC 2026-10-26T00:33:26.364834+00:00 to 00:43:47.530924+00:00; peak module RSS
  2994408 KiB (Build/CfgRecord). Raw logs and the named sorry comparison are shipped.
- The last proof-only scan repair changed UniversalK after that sweep. The changed module
  and all six subsequent modules in the order were therefore rebuilt on the final commit,
  then the sealed module, axiom walk, import probe, argument audit and downstream axiom probe:
  12/12 checks pass, UTC 00:46:49.450286 to 00:49:07.274596 on 2026-10-26.
  Peak module RSS in this tail is 3018088 KiB (NDCodeSimulator). All tail warning headers
  equal the preceding full sweep; UniversalK and its seal have no diagnostics.
- The extended import probe performs **593 checks of 593 distinct names**, covering all
  **563 names** in the final elaborated external-constant walk (plus the original probe's
  additional API checks). It has zero errors. The complete list is
  `evidence/logs/final-citations.txt` and is also quoted below.
- All 28 new privates and both targets have axiom prints and complete admission walks:
  no sorryAx or other nonstandard axiom. The downstream `exists_selfUniversal` print is
  likewise within the standard three. Five cited infrastructure theorem prints also pass.
- Rule 11's added-diff grep has no match for any of the six forbidden canonical rows or
  external private-name patterns; the elaborated walk independently finds no external
  private citations. Commands and exit statuses are in `final-rule11-grep.log`.
- The final source freeze and lint checks pass. The full sweep's unaffected first 90
  sources remain byte-identical on the final commit; the final seven were rechecked as above.


The seal marks 25 external TCSlib definitions irreducible and removes the two definition
simp attributes. The exact list is in UniversalKFinalSealed.lean. All 25 corresponding
`rfl` controls close unsealed and fail sealed, with exit statuses and raw outputs shipped.
The checks use the same final import closure. These expected negative-control and
semantic-probe failures are not compilation failures of the delivered module.

The tactic-argument inspection contains 229 occurrences, including complete multiline
arguments and nested tactics. Its environment-based classification finds no foreign
TCSlib definition argument, and no explicit core/Mathlib definition passed to rewriting or
simplification. The only named definition among audited arguments beyond uk_ definitions
is the owned EffectiveCodeK.toFinTM. The dependency name heuristic flags
List.IsPrefix.eq_of_length_le solely because its name begins with eq_; the environment audit
confirms it is a published theorem, not an unfolding equation. No external private-name
findings occur in the new proof bodies.

Lint: 0 FAIL, 67 WARN over 84 files, matching a fresh measurement of the overlay. The brief's
68 WARN / 83 files is stale at this base; the exact baseline and final outputs are included.
All source freezes pass byte-for-byte, with the sole authorized import exception.

## Text duplication screen

Before: `declarations screened: 1057; copy pairs (target reproduces >= half of source): 788; reproduced text: 213,847 chars`.

Final: `declarations screened: 1085; copy pairs (target reproduces >= half of source): 793; reproduced text: 214,252 chars`.

There are five new in-file pairs and no new cross-file pair with an owned declaration.
No new pair reaches 90%; no baseline pair was removed. **new copies: none**.

| New in-file pair (target / source) | Match | Justification |
|---|---|---|
| exists_selfUniversalK / uk_encode_halt | 62/109 (57%) | Both read the public encoded state and output equations; the target applies the result to its loop endpoint. |
| uk_embed_suffix / uk_ruler_fields | 140/236 (59%) | The endpoint reconstruction uses the public ruler-host field equations summarized by the field helper. |
| uk_encode_init_fields / uk_encode_halt | 66/109 (61%) | Shared public state/output equations are read at initialization and at an arbitrary halted configuration. |
| uk_loop_pre_live / uk_loop_run | 75/131 (57%) | Both read the explicit initial-state override and public seam equations, for the left prefix and right continuation respectively. |
| universalK / uk_encode_halt | 62/109 (57%) | The evaluator reads encoded halt/output fields after the ruler-host and loop run. |

The before screen ran on the frozen overlay commit and is byte-identical to the supplied
base. Every later screen ran on its own frozen worktree, one screen at a time. The earlier
checkpoint findings were retained in their archives and repaired: initial-state transport
was factored once, the generic seam is shared by both targets, and the halted-run space
argument now uses the published visited-set splitting lemma. No finding is waived.
The last scan-pair finding was removed by composing two one-step runs with the public
run-addition theorem and one shared local step equation.
Both complete final before/after outputs are quoted in the appendix and also shipped as raw
files with commands, frozen commits, times, exit status, and maximum memory.

## Environment and dispatch integrity

| Attachment | Verified SHA-256 |
|---|---|
| megafill-C.md | 132031ca6056939473cb429ff54ace29c40b0947d9aa20680475bd8f80087b96 |
| u2s-fill-universal.md | 7213901f62c2c68b314ae9fd748df20223b49c83eec94ec1f84043dbe7376350 |
| fill-environment-addendum.md | 90851511cf164dfa84ac9264cb5ba7acd54b7f551c823ae5d1000e43e233abf0 |

The cover and item equal their repository copies at the exact base after the permitted
@ANCESTOR@ substitution; the addendum equals its copy exactly. The dispatch files were read
locally. Part 1 preflight ran once, before the item: 9 CPUs; cgroup memory.max 8589934592 bytes;
anon+kernel+shmem 206270464 bytes; computed headroom 8383664128 bytes (7.807896 GiB), above 4 GiB.
Free disk was 31028391936 bytes (28.897442 GiB), above 12 GiB. The clone, parent, /tmp and /root
share the overlay filesystem. Before-item free disk was 25202954240 bytes. No E-RES stop,
OOM, resource retry, or cache cleanup occurred.

Lean 4.25.0 was downloaded from its official release. The unmodified executable failed with
exactly `error: failed to locate application`. Part 2's executable-path shim was compiled
from the addendum's exact source, SHA-256
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`, and scoped to Lean/Lake
invocations. The shimmed compiler reports v4.25.0, commit cdd38ac. No other runtime workaround
was used. The source, commands, original failure and success logs are included.

The cache archive store was logged first: /root/.cache/mathlib absent, zero files/bytes.
One filtered fetch used exactly the order list's 40 direct Mathlib roots and
TAR_OPTIONS=--no-same-owner; 1002 archives were downloaded and decompressed, no failed fetches.
There was no unfiltered cache invocation and no lake build. The manifest checks verify URL
and revision for all 11 present packages. Its last line is:
`MANIFEST PASS: 11 present packages; 4 absent; 0 mismatches or absent-package imports`. Four absent documentation packages (doc-gen4,
UnicodeBasic, BibtexQuery, MD4Lean) are outside the order. There are no empty oleans.

The authorized overlay was followed by a fresh 97-module bootstrap, starting
2026-10-25T23:35:25.531950+00:00 and ending 23:45:13.216418+00:00: zero errors and exactly
26 named base sorry warnings. Peak module maximum RSS was 2985964 KiB. Every check runs
serially through scripts/lean_check_tree.sh under nice -n 10. Per-module start/end UTC,
exit status, maximum RSS, user and system time are recorded with os.wait4 because
/usr/bin/time is absent. The first timing wrapper failed before invoking Lean and was
replaced; it was not a Lean/cache failure or retry.

## Checkpoints, promotions and escalation

| Archive | Commit/state | SHA-256 |
|---|---|---|
| fill-u2s-universal-cp1.zip | 64d629fb; seam and input-generic loop lemmas; screen finding disclosed | 6313b2eeaeed59d43242d01b38a935951855b2dd15be6cdbd036601f142ffd88 |
| fill-u2s-universal-cp2.zip | 59c24034; full U2-U proof; screen findings and warning disclosed | 985e37f022fa3f44eb48c50e6bf38c713e98cce8da2d2bbae1c74794555f60c8 |
| fill-u2s-universal-cp3.zip | 2410022f; both proofs and all final audits complete | 777220b2a768442b4cabc2c06cebef193d3f4fc92df9cf8e1139c68d17bc2e48 |

Checkpoint archives were delivered immediately when written. This final delivery supersedes
their pending audit repairs. Archive checkpoints grouped numbered milestones: cp1 records 1.1
and the loop parts of 1.2/1.4; cp2 records 1.1–1.5; cp3 records 1.1–1.5 and 2.1–2.5.
There was not a separate archive at each of the ten numbered milestones; see E-CHK below. Promotion candidates remain notes only: the shared startup-to-
emitting-continuation seam (self-universal and space-universal consumers), and the generic
header-ruler scan (one-header evaluator and two-header space-universal startup).

Mathematical/API escalations: **none**. No statement was changed or weakened.

**E-CHK (process deviation).** The brief requested a commit and zip after every numbered
checkpoint. Work was instead committed and archived in the grouped checkpoints listed above.
The omitted intermediate archive boundaries cannot be reconstructed as contemporaneous
deliveries. The actual archives, commits, and times are retained without backdating. This
does not leave a proof gap, but it is an unmet checkpoint-delivery requirement.

The archive contains the full source, the complete format-patch series against the base,
a git bundle whose only prerequisite is that base, shared environment logs, bootstrap and
final sweep logs, final axiom/import/argument checks, seals and both controls, semantic probes,
screen outputs, and SHA256SUMS. No toolchain archive, binary, olean, or other build product is
included. SHA256SUMS covers every member except itself.

## Complete before screen output

```text
declarations screened: 1057; copy pairs (target reproduces >= half of source): 788; reproduced text: 213,847 chars
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Admin_apply: 264/264 = 100%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 264/264 = 100%
   UniversalInterpreter.lean::universalStateTape_append  reproduces  Universal.lean::timedCut_StateTape_append: 218/218 = 100%
   Universal.lean::timedCut_StateTape_append  reproduces  UniversalInterpreter.lean::universalStateTape_append: 218/218 = 100%
   UniversalStartup.lean::universal_pair_separator  reproduces  Universal.lean::timed_pair_separator: 207/207 = 100%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 207/207 = 100%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Universal.lean::timedCaptureCfg: 184/184 = 100%
   Universal.lean::timedCaptureCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 184/184 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Finite.lean::runFrom_state_ne_none_of_le  reproduces  Catalog.lean::f2_loop_live_prefix: 156/156 = 100%
   Catalog.lean::f2_loop_live_prefix  reproduces  Finite.lean::runFrom_state_ne_none_of_le: 156/156 = 100%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   UniversalStartup.lean::universal_live_before  reproduces  Universal.lean::timedCut_live_before: 121/121 = 100%
   Universal.lean::timedCut_live_before  reproduces  UniversalStartup.lean::universal_live_before: 121/121 = 100%
   UniversalInterpreter.lean::universalInterpreterInitial  reproduces  Universal.lean::timedCut_InterpreterInitial: 113/113 = 100%
   Universal.lean::timedCut_InterpreterInitial  reproduces  UniversalInterpreter.lean::universalInterpreterInitial: 113/113 = 100%
   UniversalInterpreter.lean::universalInterpreterBase  reproduces  Universal.lean::timedCut_InterpreterBase: 102/102 = 100%
   Universal.lean::timedCut_InterpreterBase  reproduces  UniversalInterpreter.lean::universalInterpreterBase: 102/102 = 100%
   UniversalInterpreter.lean::universalEval_reads  reproduces  Universal.lean::timedCut_Eval_reads: 88/88 = 100%
   Universal.lean::timedCut_Eval_reads  reproduces  UniversalInterpreter.lean::universalEval_reads: 88/88 = 100%
   Rewind.lean::rw_cfg  reproduces  Catalog.lean::catalogSeekCfg: 79/79 = 100%
   Catalog.lean::catalogSeekCfg  reproduces  Rewind.lean::rw_cfg: 79/79 = 100%
   UniversalInterpreter.lean::universal_table_read  reproduces  Universal.lean::timedCut_table_read: 61/61 = 100%
   Universal.lean::timedCut_table_read  reproduces  UniversalInterpreter.lean::universal_table_read: 61/61 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   UniversalInterpreter.lean::universalStartupBound  reproduces  Universal.lean::timedStartupBound: 130/131 = 99%
   Universal.lean::timedStartupBound  reproduces  UniversalInterpreter.lean::universalStartupBound: 130/131 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Universal.lean::timedCut_skip_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 647/665 = 97%
   Universal.lean::timedCut_table_rewind  reproduces  UniversalInterpreter.lean::universal_table_rewind: 637/655 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_initial_skip: 934/970 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   UniversalStartup.lean::universalCapture_transfer  reproduces  Universal.lean::timedCapture_transfer: 119/124 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_unary_copy: 942/985 = 96%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedCut_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_state_rewind  reproduces  UniversalInterpreter.lean::universal_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_unary_copy: 942/987 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Interpreter_first: 272/288 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_count_run: 2197/2342 = 94%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 272/290 = 94%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_get: 257/276 = 93%
   Universal.lean::timedCapture_transfer  reproduces  UniversalStartup.lean::universalCapture_transfer: 119/128 = 93%
   Universal.lean::timedSix  reproduces  Universal.lean::timedFive: 78/84 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_initial_skip: 934/1008 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 647/705 = 92%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedCut_table_rewind: 637/695 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_count_run: 2197/2414 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Universal.lean::timed_universal_concrete  reproduces  Universal.lean::timed_universal: 384/424 = 91%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_get: 257/284 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 911/1008 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Universal.lean::timedCut_Interpreter_initialize  reproduces  UniversalInterpreter.lean::universalInterpreter_initialize: 1802/2036 = 89%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   UniversalStartup.lean::universalCapture_step  reproduces  Universal.lean::timedCapture_step: 1089/1241 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timedCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   UniversalStartup.lean::universalCapture_init  reproduces  Universal.lean::timedCapture_init: 276/318 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Universal.lean::timedCapture_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   UniversalInterpreter.lean::universalInterpreter_initialize  reproduces  Universal.lean::timedCut_Interpreter_initialize: 1802/2105 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCapture_start: 434/508 = 85%
   Universal.lean::timedCapture_step  reproduces  Universal.lean::timedCapture_init: 271/318 = 85%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   Universal.lean::timedCapture_step  reproduces  UniversalStartup.lean::universalCapture_step: 1089/1281 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universalCapture_start: 434/512 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1440/1718 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 802/970 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Universal.lean::timedCapture_init  reproduces  UniversalStartup.lean::universalCapture_init: 276/334 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1396/1718 = 81%
   InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Simulation.lean::bufferedFirstCfg_init  reproduces  Universal.lean::timedCapture_init: 255/318 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1670/2086 = 80%
   Catalog.lean::skipBackTM  reproduces  Rewind.lean::rewindTM: 140/175 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   InputDevice.lean::exists_rulerTestTM  reproduces  InputDevice.lean::rd_test_return: 108/136 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedPrefix_penultimate: 318/401 = 79%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_clock_separator: 236/298 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Universal.lean::timedCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Universal.lean::timedCaptureTM  reproduces  UniversalStartup.lean::universalCaptureTM: 291/372 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Universal.lean::timedFive  reproduces  Universal.lean::timedSix: 78/102 = 76%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timed_clock_back: 401/541 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timed_output_back: 401/543 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  Universal.lean::timedCut_serialization_actions: 589/809 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 911/1254 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Universal.lean::timedCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedCapture_run: 122/169 = 72%
   Universal.lean::timed_clock_get  reproduces  UniversalStartup.lean::universal_pair_get: 205/284 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Universal.lean::timedBorrow_length  reproduces  Universal.lean::timedBorrow_fold: 64/89 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 704/985 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   StepBlock.lean::roundTM_iterate  reproduces  Deterministic.lean::visitedByTapeHead_step_subset: 180/253 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   StepBlock.lean::roundData  reproduces  Simulation.lean::leftCfg: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 704/1008 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  Universal.lean::timedCut_ActionBits_decode: 133/191 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   UniversalInterpreter.lean::universalEval_step  reproduces  Universal.lean::timedCut_Eval_step: 138/199 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipBackTM: 140/202 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1440/2086 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_run: 112/163 = 69%
   Universal.lean::timedCut_Eval_step  reproduces  UniversalInterpreter.lean::universalEval_step: 138/201 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Universal.lean::timedBorrow_value  reproduces  Universal.lean::timedBorrow_underflow: 91/133 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 671/985 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_run: 110/163 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1670/2482 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 678/1008 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_initial_skip: 675/1008 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Universal.lean::timed_clock_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 138/207 = 67%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_pair_separator: 138/207 = 67%
   Universal.lean::timed_replay  reproduces  Seam.lean::seamCompTM_runFrom_left: 112/168 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Universal.lean::timedBorrow_fold  reproduces  Universal.lean::timedBorrow_length: 64/96 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 644/970 = 66%
   Universal.lean::timed_replay  reproduces  UniversalStartup.lean::universalCapture_run: 112/169 = 66%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedCapture_run: 112/169 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Universal.lean::timedFrame_run: 83/126 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Universal.lean::timedFrame_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 110/168 = 65%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 644/985 = 65%
   Universal.lean::timedPrefix_live  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Universal.lean::timedPrefix_live  reproduces  Universal.lean::timedCut_live_before: 79/121 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 644/987 = 65%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 135/207 = 65%
   Universal.lean::timed_pair_get  reproduces  Universal.lean::timed_pair_separator: 135/207 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Universal.lean::timedFrame_run  reproduces  UniversalStartup.lean::universalCapture_run: 110/169 = 65%
   Universal.lean::timedFrame_run  reproduces  Universal.lean::timedCapture_run: 110/169 = 65%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedPrefix_complete: 507/780 = 65%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Admin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Universal.lean::timedCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 802/1254 = 64%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 644/1008 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timedClockPrefix_length: 89/140 = 64%
   Universal.lean::timed_output_step  reproduces  Universal.lean::timedClock_step: 158/249 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Universal.lean::timedCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Universal.lean::timedCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_pair_get: 173/276 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_clock_get: 236/377 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 611/987 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   NDCodeSimulator.lean::rc_replay_table  reproduces  StepBlock.lean::tableBitsK_groups: 87/141 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Deterministic.lean::timed_input_bound  reproduces  Catalog.lean::f2_loop_input_run_le: 224/364 = 62%
   Catalog.lean::f2_loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   UniversalStartup.lean::universalCaptureTM  reproduces  Universal.lean::timedCaptureTM: 291/486 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 420/705 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::catalog_redirect_loop  reproduces  Universal.lean::timedFrame_run: 75/126 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Universal.lean::timedClock_step  reproduces  Universal.lean::timed_output_step: 158/266 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   StepBlock.lean::roundTM_restore  reproduces  StepBlock.lean::roundData_shift: 115/194 = 59%
   StepBlock.lean::roundTM_prepare  reproduces  StepBlock.lean::roundData_shift: 115/194 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  Universal.lean::timedCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   StepBlock.lean::roundTM_restore  reproduces  StepBlock.lean::roundTM_prepare: 3079/5215 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   NDCodeSimulator.lean::rc_rounds  reproduces  NDCodeSimulator.lean::rc_skip: 131/224 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timed_pair_separator: 121/207 = 58%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Universal.lean::timedCapture_step: 725/1241 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Interpreter_first: 168/288 = 58%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   StepBlock.lean::roundTM_payload  reproduces  StepBlock.lean::roundData_shift: 113/194 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Embed.lean::embedThroughHalt  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Catalog.lean::a2_mapSetup_heads  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Universal.lean::timed_universal  reproduces  Universal.lean::timed_universal_concrete: 384/671 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::a2_mapVirtual_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_unary_copy: 558/985 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_skip_unary: 709/1254 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   UniversalK.lean::ss_inputRewind_run  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock_end  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedCut_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Universal.lean::timedCanon_run  reproduces  UniversalStartup.lean::prefixCanon_run: 156/277 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Finite.lean::step_output_prepend  reproduces  Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  Seam.lean::seamComp_step_right: 76/135 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1396/2482 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   UniversalInterpreter.lean::universalRecords  reproduces  StepBlock.lean::tableBitsK: 79/141 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::seekStartTM  reproduces  Rewind.lean::rewindTM: 98/175 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   UniversalK.lean::ss_capturedPrefix_fields  reproduces  UniversalK.lean::ss_capturedPrefix_run: 648/1163 = 56%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timedClockPrefix_length: 78/140 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   Catalog.lean::f2_extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   UniversalStartup.lean::universalPrefix_start  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Seam.lean::seamReleaseTM_runFrom_pos  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Seam.lean::seamCompTM_runFrom_left: 93/168 = 55%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_unary: 694/1254 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   UniversalK.lean::ss_inputRewind_run  reproduces  UniversalK.lean::ss_inputRewind_done: 177/321 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipTM: 71/129 = 55%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Universal.lean::timedCapture_init: 175/318 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timedClockPrefix_length: 77/140 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Universal.lean::timedCut_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   NDCodeSimulator.lean::rc_workReads_snoc  reproduces  StepBlock.lean::tableBitsK_groups: 77/141 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   StepBlockForward.lean::fl_restore  reproduces  StepBlockForward.lean::fl_home: 78/143 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_clock_get: 205/377 = 54%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_skip_fixed: 383/705 = 54%
   VirtualInput.lean::vhostCfg  reproduces  Simulation.lean::bufferedSecondCfg: 126/232 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   StepBlockForward.lean::fl_round  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_counter_carry  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backB  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backA  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   StepBlock.lean::roundTM_effect  reproduces  StepBlock.lean::roundData_stateCell: 69/128 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   Finite.lean::output_prefix  reproduces  UniversalStartup.lean::universal_live_before: 65/121 = 54%
   Finite.lean::output_prefix  reproduces  Universal.lean::timedCut_live_before: 65/121 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timed_replay  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_skip_unary: 671/1254 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 518/970 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_counter_increment  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 513/970 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timed_clock_timeout: 513/975 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::seekEndTM  reproduces  Rewind.lean::rewindTM: 92/175 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Catalog.lean::f2_loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_counter_rewind  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_fixed: 369/705 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::leftCfg: 68/130 = 52%
   StepBlock.lean::roundData  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   StepBlock.lean::seekTM_groups  reproduces  StepBlock.lean::seekTM_lookup: 1011/1938 = 52%
   Universal.lean::timed_input_layout  reproduces  Universal.lean::timedClockPrefix_length: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   StepBlock.lean::roundTM_iterate  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   InputDevice.lean::rd_host_block  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Catalog.lean::a2_mapSetup_run: 84/163 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_initial_skip: 518/1008 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   StepBlock.lean::recordSkipTM_path  reproduces  StepBlock.lean::recordSkipTM_run: 555/1083 = 51%
   StepBlock.lean::succFieldTM_trace  reproduces  StepBlock.lean::succFieldTM_run: 127/248 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Universal.lean::timedClockPrefix_length  reproduces  UniversalStartup.lean::universal_pair_length: 77/151 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_fixed: 355/705 = 50%
   Universal.lean::timedCanon_complete  reproduces  UniversalStartup.lean::prefixCanon_complete: 161/320 = 50%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Universal.lean::timedCut_Actions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   UniversalK.lean::ss_bufferAdvance_run  reproduces  UniversalK.lean::ss_bufferClear_run: 1040/2075 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Universal.lean::timedFrame_apply  reproduces  Simulation.lean::leftCfg_apply: 94/188 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
   Universal.lean::timedClockCfg  reproduces  Universal.lean::timed_laneCfg: 60/120 = 50%
```

## Complete final screen output

```text
declarations screened: 1085; copy pairs (target reproduces >= half of source): 793; reproduced text: 214,252 chars
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::f2_space_of_time: 713/713 = 100%
   Catalog.lean::f2_space_of_time  reproduces  Simulation.lean::ComputesInTime.spaceUsed_le: 713/713 = 100%
   Simulation.lean::timed_rewind  reproduces  Catalog.lean::f2_catalogRewind: 435/435 = 100%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::timed_rewind: 435/435 = 100%
   Catalog.lean::f2_finSumEquiv  reproduces  Catalog.lean::a2_mapSumEquiv: 362/362 = 100%
   Catalog.lean::a2_mapSumEquiv  reproduces  Catalog.lean::f2_finSumEquiv: 362/362 = 100%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Admin_apply: 264/264 = 100%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 264/264 = 100%
   UniversalInterpreter.lean::universalStateTape_append  reproduces  Universal.lean::timedCut_StateTape_append: 218/218 = 100%
   Universal.lean::timedCut_StateTape_append  reproduces  UniversalInterpreter.lean::universalStateTape_append: 218/218 = 100%
   UniversalStartup.lean::universal_pair_separator  reproduces  Universal.lean::timed_pair_separator: 207/207 = 100%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 207/207 = 100%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Universal.lean::timedCaptureCfg: 184/184 = 100%
   Universal.lean::timedCaptureCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 184/184 = 100%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_tapeAction_move: 167/167 = 100%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_tapeAction_write: 167/167 = 100%
   Finite.lean::runFrom_state_ne_none_of_le  reproduces  Catalog.lean::f2_loop_live_prefix: 156/156 = 100%
   Catalog.lean::f2_loop_live_prefix  reproduces  Finite.lean::runFrom_state_ne_none_of_le: 156/156 = 100%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_right: 135/135 = 100%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipTM: 129/129 = 100%
   UniversalStartup.lean::universal_live_before  reproduces  Universal.lean::timedCut_live_before: 121/121 = 100%
   Universal.lean::timedCut_live_before  reproduces  UniversalStartup.lean::universal_live_before: 121/121 = 100%
   UniversalInterpreter.lean::universalInterpreterInitial  reproduces  Universal.lean::timedCut_InterpreterInitial: 113/113 = 100%
   Universal.lean::timedCut_InterpreterInitial  reproduces  UniversalInterpreter.lean::universalInterpreterInitial: 113/113 = 100%
   UniversalInterpreter.lean::universalInterpreterBase  reproduces  Universal.lean::timedCut_InterpreterBase: 102/102 = 100%
   Universal.lean::timedCut_InterpreterBase  reproduces  UniversalInterpreter.lean::universalInterpreterBase: 102/102 = 100%
   UniversalInterpreter.lean::universalEval_reads  reproduces  Universal.lean::timedCut_Eval_reads: 88/88 = 100%
   Universal.lean::timedCut_Eval_reads  reproduces  UniversalInterpreter.lean::universalEval_reads: 88/88 = 100%
   Rewind.lean::rw_cfg  reproduces  Catalog.lean::catalogSeekCfg: 79/79 = 100%
   Catalog.lean::catalogSeekCfg  reproduces  Rewind.lean::rw_cfg: 79/79 = 100%
   UniversalInterpreter.lean::universal_table_read  reproduces  Universal.lean::timedCut_table_read: 61/61 = 100%
   Universal.lean::timedCut_table_read  reproduces  UniversalInterpreter.lean::universal_table_read: 61/61 = 100%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1304/1306 = 100%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::rewind_from_any: 465/466 = 100%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_transfer_endpoint: 478/480 = 100%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1304/1314 = 99%
   UniversalInterpreter.lean::universalStartupBound  reproduces  Universal.lean::timedStartupBound: 130/131 = 99%
   Universal.lean::timedStartupBound  reproduces  UniversalInterpreter.lean::universalStartupBound: 130/131 = 99%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 228/230 = 99%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 227/230 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 225/230 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   Seam.lean::seamComp_step_left  reproduces  Seam.lean::seamComp_step_right: 132/135 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalEval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_lenParse_first: 312/320 = 98%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 385/395 = 97%
   Universal.lean::timedCut_skip_fixed  reproduces  UniversalInterpreter.lean::universal_skip_fixed: 647/665 = 97%
   Universal.lean::timedCut_table_rewind  reproduces  UniversalInterpreter.lean::universal_table_rewind: 637/655 = 97%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairConcat_spaceUsed: 305/314 = 97%
   Catalog.lean::f2_scanTrues_run  reproduces  Catalog.lean::f2_scanStep_right: 159/164 = 97%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank: 122/126 = 97%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_initial_skip: 934/970 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 305/317 = 96%
   Catalog.lean::computesFunInTime_pairConcat_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 305/317 = 96%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::copyTM_run: 388/404 = 96%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::copyMapTM: 478/498 = 96%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   UniversalStartup.lean::universalCapture_transfer  reproduces  Universal.lean::timedCapture_transfer: 119/124 = 96%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 220/230 = 96%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_unary_copy: 942/985 = 96%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedCut_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_state_rewind  reproduces  UniversalInterpreter.lean::universal_state_rewind: 393/411 = 96%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_unary_copy: 942/987 = 95%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_rawStrip_replay: 393/412 = 95%
   VirtualInput.lean::vhostEmitTM_visitedByTapeHead_bank  reproduces  VirtualInput.lean::vhostEmitTM_visitedByTapeHead_buffer: 122/128 = 95%
   Universal.lean::timedCut_serialization_actions  reproduces  UniversalInterpreter.lean::universal_serialization_header: 589/619 = 95%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::a2_call_run: 299/315 = 95%
   Catalog.lean::f2_loopCall_reframe  reproduces  Catalog.lean::f2_loopCall_frame: 500/527 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Interpreter_first: 272/288 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalEval_reads: 83/88 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   Catalog.lean::f2_incFixed_computes  reproduces  Catalog.lean::f2_scanStep_right: 154/164 = 94%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_count_run: 2197/2342 = 94%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 272/290 = 94%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_get: 257/276 = 93%
   Universal.lean::timedCapture_transfer  reproduces  UniversalStartup.lean::universalCapture_transfer: 119/128 = 93%
   Universal.lean::timedSix  reproduces  Universal.lean::timedFive: 78/84 = 93%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanStep_right: 152/164 = 93%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_initial_skip: 934/1008 = 93%
   Catalog.lean::computesFunInTime_pairSnd_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairFst_spaceUsed: 293/317 = 92%
   Catalog.lean::computesFunInTime_pairFst_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairSnd_spaceUsed: 293/317 = 92%
   Catalog.lean::f2_branch_space  reproduces  Catalog.lean::catalog_space_one: 115/125 = 92%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 647/705 = 92%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedCut_table_rewind: 637/695 = 92%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::a2_map_move: 331/362 = 91%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_count_run: 2197/2414 = 91%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Simulation.lean::rewind_heads  reproduces  Catalog.lean::f2_catalogRewind: 395/435 = 91%
   Universal.lean::timed_universal_concrete  reproduces  Universal.lean::timed_universal: 384/424 = 91%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_get: 257/284 = 90%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_loop_rewind_bounded: 465/514 = 90%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 911/1008 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamReleaseTM_step_inr: 122/135 = 90%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_right: 122/135 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::clearTM: 369/409 = 90%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_move: 326/362 = 90%
   Catalog.lean::incrementTM_run_succ_ofCfg  reproduces  Catalog.lean::incrementTM_run_overflow_ofCfg: 617/686 = 90%
   Simulation.lean::bufferedSecondCfg_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 241/268 = 90%
   Catalog.lean::copyMapTM  reproduces  Catalog.lean::transferMapTM: 478/533 = 90%
   Catalog.lean::f2_loopHost_halt_return  reproduces  Catalog.lean::a2_call_run: 279/315 = 89%
   Universal.lean::timedCut_Interpreter_initialize  reproduces  UniversalInterpreter.lean::universalInterpreter_initialize: 1802/2036 = 89%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   UniversalStartup.lean::universalCapture_step  reproduces  Universal.lean::timedCapture_step: 1089/1241 = 88%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::transferTM_spaceUsedByTape: 625/713 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timedCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::clearTM_run: 336/385 = 87%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 632/725 = 87%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Catalog.lean::f2_loopBorrow_run: 414/476 = 87%
   UniversalInterpreter.lean::universalInterpreter  reproduces  UniversalInterpreter.lean::universalSkipDone: 60/69 = 87%
   Catalog.lean::a2_map_backB  reproduces  Catalog.lean::a2_map_backA: 806/927 = 87%
   UniversalStartup.lean::universalCapture_init  reproduces  Universal.lean::timedCapture_init: 276/318 = 87%
   Catalog.lean::f2_loopHost_body_capture  reproduces  Catalog.lean::f2_loopHost_fuel_capture: 96/111 = 86%
   UniversalStartup.lean::universalCapture_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Universal.lean::timedCapture_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  UniversalStartup.lean::universalCapture_run: 146/169 = 86%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::copyTM_spaceUsedByTape: 625/727 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   UniversalStartup.lean::universalCapture_step  reproduces  UniversalStartup.lean::universalCapture_init: 287/334 = 86%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedFrame_run: 108/126 = 86%
   UniversalInterpreter.lean::universalInterpreter_initialize  reproduces  Universal.lean::timedCut_Interpreter_initialize: 1802/2105 = 86%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 664/776 = 86%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCapture_start: 434/508 = 85%
   Universal.lean::timedCapture_step  reproduces  Universal.lean::timedCapture_init: 271/318 = 85%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   Universal.lean::timedCapture_step  reproduces  UniversalStartup.lean::universalCapture_step: 1089/1281 = 85%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Simulation.lean::bufferedSecondCfg_run: 241/284 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universalCapture_start: 434/512 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   Catalog.lean::transferMapTM  reproduces  Catalog.lean::clearTM: 344/409 = 84%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::seekEndTM: 173/206 = 84%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1440/1718 = 84%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::a2_fuel_heads: 515/615 = 84%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 1092/1306 = 84%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::copyTM_run: 336/404 = 83%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 1092/1314 = 83%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_initial_skip: 802/970 = 83%
   Catalog.lean::a2_map_backA  reproduces  Catalog.lean::a2_map_backB: 806/975 = 83%
   Universal.lean::timedCapture_init  reproduces  UniversalStartup.lean::universalCapture_init: 276/334 = 83%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_rewind: 632/767 = 82%
   Catalog.lean::f2_loopHost_fuel_capture  reproduces  Catalog.lean::f2_loopHost_body_capture: 96/117 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 664/814 = 82%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::clearTM_run: 314/385 = 82%
   Catalog.lean::f2_sum_add  reproduces  Catalog.lean::a2_map_sum: 153/188 = 81%
   Catalog.lean::a2_map_sum  reproduces  Catalog.lean::f2_sum_add: 153/188 = 81%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferFinish_run: 1396/1718 = 81%
   InputDevice.lean::rd_trace_step  reproduces  InputDevice.lean::rd_read_nat: 73/90 = 81%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 1077/1329 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   Catalog.lean::step_of_tapeAction_write  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::step_of_tapeAction_move  reproduces  Catalog.lean::step_of_inputMoveAction: 68/84 = 81%
   Catalog.lean::f2_counter_count_space  reproduces  Catalog.lean::f2_counter_count: 363/452 = 80%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipBackTM: 162/202 = 80%
   Simulation.lean::bufferedFirstCfg_init  reproduces  Universal.lean::timedCapture_init: 255/318 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   UniversalStartup.lean::universal_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   Universal.lean::timed_pair_separator  reproduces  UniversalStartup.lean::universal_pair_length: 121/151 = 80%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1670/2086 = 80%
   Catalog.lean::skipBackTM  reproduces  Rewind.lean::rewindTM: 140/175 = 80%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1092/1366 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   UniversalInterpreter.lean::universalInterpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 210/264 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   InputDevice.lean::exists_rulerTestTM  reproduces  InputDevice.lean::rd_test_return: 108/136 = 79%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_extract_first: 238/300 = 79%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedPrefix_penultimate: 318/401 = 79%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_clock_separator: 236/298 = 79%
   UniversalStartup.lean::universalCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Universal.lean::timedCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::skipTM: 102/129 = 79%
   Catalog.lean::a2_call_heads  reproduces  Catalog.lean::f2_loopCall_heads: 520/658 = 79%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_scan: 526/666 = 79%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_return: 1077/1366 = 79%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::branchTM_computes: 632/802 = 79%
   Catalog.lean::transferTM_run_ofCfg  reproduces  Catalog.lean::copyTM_run_ofCfg: 89/113 = 79%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_run: 128/163 = 79%
   Catalog.lean::seekStartTM  reproduces  Catalog.lean::skipTM: 101/129 = 78%
   Universal.lean::timedCaptureTM  reproduces  UniversalStartup.lean::universalCaptureTM: 291/372 = 78%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::incrementTM_run_overflow: 383/491 = 78%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_prepare: 1165/1499 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::clearTM_run: 299/385 = 78%
   Catalog.lean::compareTM  reproduces  Catalog.lean::incrementTM: 408/526 = 78%
   Universal.lean::timedFive  reproduces  Universal.lean::timedSix: 78/102 = 76%
   Simulation.lean::bufferedFirstCfg_init  reproduces  UniversalStartup.lean::universalCapture_init: 255/334 = 76%
   Catalog.lean::f2_counterTape_write  reproduces  Catalog.lean::f2_loopBuffer_write: 311/408 = 76%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanStep_right: 125/164 = 76%
   Catalog.lean::f2_loopBorrow_run  reproduces  Catalog.lean::f2_loopHost_borrow_run: 414/544 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  UniversalStartup.lean::universalCapture_run: 128/169 = 76%
   Catalog.lean::a2_mapSetup_run  reproduces  Universal.lean::timedCapture_run: 128/169 = 76%
   Catalog.lean::f2_loopBorrow_step  reproduces  Catalog.lean::f2_loopReplay_step: 258/341 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   Seam.lean::seamCompTM  reproduces  Seam.lean::seamReleaseTM: 148/196 = 76%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_run: 123/163 = 75%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 356/472 = 75%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_start: 600/797 = 75%
   UniversalInterpreter.lean::universalRecords  reproduces  Universal.lean::timedCut_Actions: 105/140 = 75%
   Catalog.lean::f2_extract_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 230/307 = 75%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_run: 122/163 = 75%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::clearTM: 305/409 = 75%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::catalog_redirect_loop  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::a2_mapSetup_heads: 73/98 = 74%
   Catalog.lean::compareTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_run: 286/384 = 74%
   Catalog.lean::f2_counterInc_potential  reproduces  Catalog.lean::f2_counterInc_length: 106/143 = 74%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timed_clock_back: 401/541 = 74%
   Catalog.lean::clearTM  reproduces  Catalog.lean::copyMapTM: 369/498 = 74%
   Catalog.lean::f2_extract_block  reproduces  Catalog.lean::f2_extract_first: 222/300 = 74%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_call_heads: 520/703 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timed_output_back: 401/543 = 74%
   Catalog.lean::incrementTM_run_overflow_ofCfg  reproduces  Catalog.lean::incrementTM_run_succ_ofCfg: 617/839 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::Cfg.ofWords_copy_endpoint: 169/230 = 73%
   Catalog.lean::f2_loop_find_run  reproduces  Catalog.lean::a2_loop_halted_run: 484/659 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Catalog.lean::a2_mapVirtual_run: 190/259 = 73%
   Catalog.lean::f2_loopFrame  reproduces  Catalog.lean::f2_loopControlAction: 110/150 = 73%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_pairDupTM: 283/386 = 73%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::a2_call_heads: 515/703 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   Catalog.lean::f2_counterTape_read  reproduces  Catalog.lean::f2_loopBuffer_read: 65/89 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::f2_catalogPoly_emit: 384/527 = 73%
   UniversalInterpreter.lean::universal_serialization_header  reproduces  Universal.lean::timedCut_serialization_actions: 589/809 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 706/970 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  UniversalStartup.lean::universalCapture_run: 123/169 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Universal.lean::timedCapture_run: 123/169 = 73%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 911/1254 = 73%
   UniversalStartup.lean::universalCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Universal.lean::timedCapture_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::a2_mapSetup_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopBody_capture: 270/372 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::a2_mapSetup_heads: 71/98 = 72%
   Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   UniversalInterpreter.lean::universalAdmin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Universal.lean::timedCut_Admin_apply  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 210/290 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  UniversalStartup.lean::universalCapture_run: 122/169 = 72%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedCapture_run: 122/169 = 72%
   Universal.lean::timed_clock_get  reproduces  UniversalStartup.lean::universal_pair_get: 205/284 = 72%
   Catalog.lean::f2_loopBuffer_write  reproduces  Catalog.lean::f2_counterTape_write: 311/432 = 72%
   Universal.lean::timedBorrow_length  reproduces  Universal.lean::timedBorrow_fold: 64/89 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Catalog.lean::f2_splitRestoreScan  reproduces  Catalog.lean::f2_splitPrepareScan: 74/103 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   Catalog.lean::f2_splitRestore_append  reproduces  Catalog.lean::f2_splitPrepare_extra: 338/472 = 72%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 706/987 = 72%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 704/985 = 71%
   Catalog.lean::f2_splitCount_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 120/168 = 71%
   Catalog.lean::a2_loop_halted_run  reproduces  Catalog.lean::f2_loop_find_run: 484/678 = 71%
   StepBlock.lean::roundTM_iterate  reproduces  Deterministic.lean::visitedByTapeHead_step_subset: 180/253 = 71%
   Catalog.lean::f2_loopHost_borrow  reproduces  Catalog.lean::f2_loopBorrow_correct: 261/367 = 71%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::a2_map_move: 257/362 = 71%
   Catalog.lean::a2_mapVirtual_run  reproduces  VirtualInput.lean::vhostEmitTM_runFrom: 190/268 = 71%
   StepBlock.lean::roundData  reproduces  Simulation.lean::leftCfg: 92/130 = 71%
   Catalog.lean::f2_rawStripTM  reproduces  Catalog.lean::f2_loopReplayTM: 92/130 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   Seam.lean::seamCompTM_firstReturn  reproduces  Seam.lean::seamCompTM_run: 151/214 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::transferTM_run: 478/680 = 70%
   Catalog.lean::f2_cond_ledger  reproduces  Catalog.lean::f2_timed_start: 754/1073 = 70%
   Catalog.lean::f2_splitRestoreTM  reproduces  Catalog.lean::f2_splitPrepareTM: 280/399 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::clearTM_run: 270/385 = 70%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 215/307 = 70%
   Catalog.lean::a2_heads_halted  reproduces  Catalog.lean::a2_heads_join: 72/103 = 70%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 704/1008 = 70%
   UniversalInterpreter.lean::universal_record_shape  reproduces  Universal.lean::timedCut_ActionBits_decode: 133/191 = 70%
   Catalog.lean::f2_loopBody_step  reproduces  Catalog.lean::f2_loopBody_stop: 245/352 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   UniversalStartup.lean::universalPrefix_start  reproduces  UniversalStartup.lean::universalPrefix_bits: 600/864 = 69%
   Catalog.lean::f2_lenParse_block  reproduces  Catalog.lean::f2_lenParse_first: 222/320 = 69%
   UniversalInterpreter.lean::universalEval_step  reproduces  Universal.lean::timedCut_Eval_step: 138/199 = 69%
   Catalog.lean::incrementTM_run_overflow  reproduces  Catalog.lean::copyTM_run: 280/404 = 69%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipBackTM: 140/202 = 69%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogCompareR: 63/91 = 69%
   Catalog.lean::a2_mapVirtual  reproduces  Catalog.lean::a2_mapCfg: 92/133 = 69%
   Catalog.lean::catalogIncF  reproduces  Catalog.lean::catalogIncR: 152/220 = 69%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferSeek_run: 1440/2086 = 69%
   Catalog.lean::copyTM_run_ofCfg  reproduces  Catalog.lean::transferTM_run_ofCfg: 89/129 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::seekStartTM: 173/251 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamReleaseTM_step_inr: 93/135 = 69%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Seam.lean::seamComp_step_right: 93/135 = 69%
   UniversalStartup.lean::universalPrefix_bits  reproduces  UniversalStartup.lean::universalPrefix_penultimate: 272/395 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   Universal.lean::timed_replay  reproduces  Catalog.lean::a2_mapSetup_run: 112/163 = 69%
   Universal.lean::timedCut_Eval_step  reproduces  UniversalInterpreter.lean::universalEval_step: 138/201 = 69%
   Catalog.lean::computesFunInTime_incFixed_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 74/108 = 69%
   Universal.lean::timedBorrow_value  reproduces  Universal.lean::timedBorrow_underflow: 91/133 = 68%
   Catalog.lean::f2_counter_heads  reproduces  Catalog.lean::f2_counter_computes: 666/977 = 68%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 671/985 = 68%
   Catalog.lean::f2_counterInc_bits  reproduces  Catalog.lean::f2_loopValue_bits: 96/141 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  UniversalStartup.lean::universal_live_before: 82/121 = 68%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::a2_mapSetup_run: 110/163 = 67%
   Catalog.lean::f2_loopHost_anchor_return  reproduces  Catalog.lean::f2_loopHost_halt_return: 342/508 = 67%
   UniversalK.lean::ss_bufferSeek_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1670/2482 = 67%
   Catalog.lean::computesFunInTime_pairDup_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 74/110 = 67%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 678/1008 = 67%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_clear_trace: 1086/1617 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay_finish: 206/307 = 67%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 276/412 = 67%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_initial_skip: 675/1008 = 67%
   Catalog.lean::f2_rawStrip_replay  reproduces  Catalog.lean::f2_extract_replay: 393/587 = 67%
   Catalog.lean::a2_mapVirtual_run  reproduces  Simulation.lean::bufferedSecondCfg_run: 190/284 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 872/1306 = 67%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_lenParse_run: 1137/1703 = 67%
   Catalog.lean::catalogIncR  reproduces  Catalog.lean::catalogIncF: 152/228 = 67%
   Universal.lean::timed_clock_separator  reproduces  UniversalStartup.lean::universal_pair_separator: 138/207 = 67%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_pair_separator: 138/207 = 67%
   Universal.lean::timed_replay  reproduces  Seam.lean::seamCompTM_runFrom_left: 112/168 = 67%
   Catalog.lean::scanResult_fold  reproduces  Catalog.lean::scanResult_map: 92/138 = 67%
   Universal.lean::timedBorrow_fold  reproduces  Universal.lean::timedBorrow_length: 64/96 = 67%
   Catalog.lean::incrementTM_run_succ  reproduces  Catalog.lean::copyTM_run: 269/404 = 67%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 874/1314 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanStep_right: 109/164 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   Universal.lean::timedCut_unary_copy  reproduces  UniversalInterpreter.lean::universal_initial_skip: 644/970 = 66%
   Universal.lean::timed_replay  reproduces  UniversalStartup.lean::universalCapture_run: 112/169 = 66%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedCapture_run: 112/169 = 66%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_first: 232/351 = 66%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitRestoreScan: 74/112 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::leftCfg_apply: 124/188 = 66%
   Catalog.lean::f2_incFixedTM  reproduces  Catalog.lean::f2_splitRewindTM: 122/185 = 66%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Universal.lean::timedFrame_run: 83/126 = 66%
   UniversalInterpreter.lean::universal_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 637/970 = 66%
   Catalog.lean::f2_branch_space  reproduces  Simulation.lean::rightCfg_apply: 126/192 = 66%
   Universal.lean::timedFrame_run  reproduces  Seam.lean::seamCompTM_runFrom_left: 110/168 = 65%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 644/985 = 65%
   Universal.lean::timedPrefix_live  reproduces  UniversalStartup.lean::universal_live_before: 79/121 = 65%
   Universal.lean::timedPrefix_live  reproduces  Universal.lean::timedCut_live_before: 79/121 = 65%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_frame: 344/527 = 65%
   Universal.lean::timedCut_initial_skip  reproduces  UniversalInterpreter.lean::universal_unary_copy: 644/987 = 65%
   Universal.lean::timed_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 135/207 = 65%
   Universal.lean::timed_pair_get  reproduces  Universal.lean::timed_pair_separator: 135/207 = 65%
   Catalog.lean::f2_poly_space  reproduces  Catalog.lean::f2_space_radius: 239/367 = 65%
   Universal.lean::timedFrame_run  reproduces  UniversalStartup.lean::universalCapture_run: 110/169 = 65%
   Universal.lean::timedFrame_run  reproduces  Universal.lean::timedCapture_run: 110/169 = 65%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedPrefix_complete: 507/780 = 65%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   Seam.lean::seamComp_step_right  reproduces  Catalog.lean::f2_splitEmbed_run: 122/188 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 171/264 = 65%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Admin_apply: 171/264 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekStartTM: 162/251 = 65%
   Catalog.lean::clearTM  reproduces  Catalog.lean::transferMapTM: 344/533 = 65%
   Catalog.lean::f2_timed_read  reproduces  Catalog.lean::f2_control_heads: 109/169 = 64%
   Seam.lean::seamComp_step_left  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Catalog.lean::f2_splitEmbed_run: 121/188 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   Catalog.lean::f2_loopBody_run  reproduces  Universal.lean::timedFrame_run: 81/126 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  UniversalStartup.lean::universal_pair_separator: 133/207 = 64%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_pair_separator: 133/207 = 64%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::f2_catalogPoly_setup: 384/598 = 64%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::f2_counter_emit_run: 431/672 = 64%
   UniversalStartup.lean::universalCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   Universal.lean::timedCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 802/1254 = 64%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 644/1008 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   Seam.lean::seamCompTM_run  reproduces  Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   Catalog.lean::f2_extract_suffix  reproduces  Catalog.lean::f2_scanCopy_suffix: 553/868 = 64%
   Catalog.lean::f2_splitBody_rewind  reproduces  Catalog.lean::f2_splitBody_restore: 333/523 = 64%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalAdmin_apply: 168/264 = 64%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timedClockPrefix_length: 89/140 = 64%
   Universal.lean::timed_output_step  reproduces  Universal.lean::timedClock_step: 158/249 = 63%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 460/725 = 63%
   Catalog.lean::scanResult_map  reproduces  Catalog.lean::scanResult_fold: 92/145 = 63%
   UniversalStartup.lean::universalCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Universal.lean::timedCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopReplayTM: 82/130 = 63%
   UniversalStartup.lean::universalCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Universal.lean::timedCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   Catalog.lean::f2_read_heads  reproduces  Catalog.lean::f2_control_heads: 106/169 = 63%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_splitRewindTM: 116/185 = 63%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_pair_get: 173/276 = 63%
   Catalog.lean::incrementTM  reproduces  Catalog.lean::compareTM: 408/651 = 63%
   Catalog.lean::skipTM  reproduces  Catalog.lean::seekEndTM: 129/206 = 63%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_clock_get: 236/377 = 63%
   Catalog.lean::f2_pairDup_double  reproduces  Catalog.lean::f2_scanCopy_run: 311/497 = 63%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 453/725 = 62%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 257/412 = 62%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 191/307 = 62%
   Catalog.lean::f2_loopBody_stop  reproduces  Universal.lean::timedCapture_transfer: 77/124 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Catalog.lean::f2_counterInc_length  reproduces  Catalog.lean::f2_counterInc_potential: 106/171 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   Universal.lean::timedCut_skip_unary  reproduces  UniversalInterpreter.lean::universal_unary_copy: 611/987 = 62%
   Catalog.lean::f2_lenSuffix_run  reproduces  Catalog.lean::f2_anyTrue_run: 512/828 = 62%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_rawStripTM: 285/461 = 62%
   Catalog.lean::f2_loopCall_frame  reproduces  Catalog.lean::f2_loopCall_reframe: 500/809 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   NDCodeSimulator.lean::rc_replay_table  reproduces  StepBlock.lean::tableBitsK_groups: 87/141 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   Deterministic.lean::timed_input_bound  reproduces  Catalog.lean::f2_loop_input_run_le: 224/364 = 62%
   Catalog.lean::f2_loopFuel_init  reproduces  Universal.lean::timedCapture_init: 195/318 = 61%
   Catalog.lean::f2_loopReplay_step  reproduces  Catalog.lean::f2_loopBorrow_step: 258/421 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Catalog.lean::a2_mapVirtual: 123/201 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   Seam.lean::seamReleaseTM_step_inr  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Seam.lean::seamComp_step_right  reproduces  Seam.lean::seamComp_step_left: 132/216 = 61%
   Catalog.lean::f2_splitPrepare_scan  reproduces  Catalog.lean::f2_splitRestore_scan: 526/861 = 61%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_rawStrip_rewind: 442/725 = 61%
   Catalog.lean::clearTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 299/491 = 61%
   Catalog.lean::seekEndTM  reproduces  Catalog.lean::skipBackTM: 123/202 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   Catalog.lean::f2_loopFuel_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 195/322 = 61%
   UniversalK.lean::uk_encode_init_fields  reproduces  UniversalK.lean::uk_encode_halt: 66/109 = 61%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_extract_rewind: 464/767 = 60%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   Catalog.lean::f2_splitEmitCfg  reproduces  Catalog.lean::f2_splitPrepareScan: 62/103 = 60%
   Catalog.lean::f2_loopBody_stop  reproduces  UniversalStartup.lean::universalCapture_transfer: 77/128 = 60%
   Catalog.lean::f2_counter_emit_run  reproduces  Catalog.lean::f2_counter_emit: 378/630 = 60%
   Simulation.lean::bufferedCompTM  reproduces  UniversalStartup.lean::universalCaptureTM: 223/372 = 60%
   UniversalStartup.lean::universalCaptureTM  reproduces  Universal.lean::timedCaptureTM: 291/486 = 60%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 464/776 = 60%
   Catalog.lean::skipBackTM  reproduces  Catalog.lean::seekEndTM: 123/206 = 60%
   Catalog.lean::f2_pairDupTM  reproduces  Catalog.lean::f2_incFixedTM: 283/474 = 60%
   Catalog.lean::a2_loop_prepare  reproduces  Catalog.lean::f2_loopHost_input_rewind: 146/245 = 60%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_extract_run: 1137/1908 = 60%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 420/705 = 60%
   Catalog.lean::f2_splitBody_restore  reproduces  Catalog.lean::f2_splitBody_rewind: 333/559 = 60%
   Catalog.lean::catalog_redirect_loop  reproduces  Universal.lean::timedFrame_run: 75/126 = 60%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Catalog.lean::f2_scanCopy_finish: 160/269 = 59%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 258/434 = 59%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 454/764 = 59%
   Universal.lean::timedClock_step  reproduces  Universal.lean::timed_output_step: 158/266 = 59%
   Catalog.lean::a2_mapVirtual_step  reproduces  Catalog.lean::a2_map_move: 215/362 = 59%
   UniversalK.lean::uk_embed_suffix  reproduces  UniversalK.lean::uk_ruler_fields: 140/236 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 453/764 = 59%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 460/776 = 59%
   StepBlock.lean::roundTM_restore  reproduces  StepBlock.lean::roundData_shift: 115/194 = 59%
   StepBlock.lean::roundTM_prepare  reproduces  StepBlock.lean::roundData_shift: 115/194 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  UniversalStartup.lean::universalCaptureCfg: 109/184 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  Universal.lean::timedCaptureCfg: 109/184 = 59%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_rewind: 454/767 = 59%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitPrepare_scan: 394/666 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_rewind: 772/1306 = 59%
   StepBlock.lean::roundTM_restore  reproduces  StepBlock.lean::roundTM_prepare: 3079/5215 = 59%
   Catalog.lean::f2_catalogFirstEntry  reproduces  Catalog.lean::f2_splitCount_firstHalt: 198/337 = 59%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Catalog.lean::f2_loopHost_payload_rewind: 772/1314 = 59%
   Catalog.lean::f2_splitEmbed_cut  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Universal.lean::timedFrame_run: 74/126 = 59%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   Catalog.lean::f2_loopBorrow_correct  reproduces  Catalog.lean::f2_loopHost_borrow: 261/445 = 59%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitCount_over: 82/140 = 59%
   Catalog.lean::f2_splitPrepareScan  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   Catalog.lean::f2_splitPrepareReady  reproduces  Catalog.lean::f2_splitEmitCfg: 62/106 = 58%
   NDCodeSimulator.lean::rc_rounds  reproduces  NDCodeSimulator.lean::rc_skip: 131/224 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  UniversalStartup.lean::universal_pair_separator: 121/207 = 58%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timed_pair_separator: 121/207 = 58%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Universal.lean::timedCapture_step: 725/1241 = 58%
   Catalog.lean::f2_loopBody_capture  reproduces  Catalog.lean::a2_call_run: 184/315 = 58%
   Catalog.lean::f2_loopFuel_init  reproduces  UniversalStartup.lean::universalCapture_init: 195/334 = 58%
   Catalog.lean::f2_pairValid_run  reproduces  Catalog.lean::f2_anyTrue_run: 483/828 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  Universal.lean::timedCut_Interpreter_first: 168/288 = 58%
   Universal.lean::timed_apply_record  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 169/290 = 58%
   Seam.lean::seamReleaseTM  reproduces  Seam.lean::seamCompTM: 148/254 = 58%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_rawStrip_replay: 240/412 = 58%
   StepBlock.lean::roundTM_payload  reproduces  StepBlock.lean::roundData_shift: 113/194 = 58%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Catalog.lean::f2_extract_rewind: 446/767 = 58%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_borrow_rewind: 772/1329 = 58%
   Catalog.lean::f2_rawStrip_erase  reproduces  Universal.lean::timedCapture_transfer: 72/124 = 58%
   Catalog.lean::clearTM  reproduces  Catalog.lean::incrementTM: 305/526 = 58%
   Embed.lean::embedThroughHalt  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   Catalog.lean::a2_mapSetup_heads  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalInterpreter.lean::universalInterpreter_first: 168/290 = 58%
   Catalog.lean::computesFunInTime_pairLenCheck_spaceUsed  reproduces  Catalog.lean::computesFunInTime_stripLast_spaceUsed: 298/515 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   Simulation.lean::bufferedScanCfg_run  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  UniversalStartup.lean::universalCapture_init: 192/334 = 57%
   UniversalK.lean::uk_loop_pre_live  reproduces  UniversalK.lean::uk_loop_run: 75/131 = 57%
   Catalog.lean::f2_catalogPoly_unary_computes  reproduces  Catalog.lean::f2_splitPoly_loop_end: 423/739 = 57%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 874/1527 = 57%
   Universal.lean::timed_universal  reproduces  Universal.lean::timed_universal_concrete: 384/671 = 57%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_splitEmit_separator: 460/804 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::clearTM_run: 220/385 = 57%
   VirtualInput.lean::vhostEmitTM_runFrom  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::a2_mapVirtual_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Catalog.lean::f2_loopHost_fuel_copy: 872/1527 = 57%
   Catalog.lean::f2_loop_input_run_le  reproduces  Catalog.lean::f2_loop_output_length_le: 145/254 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::transferTM_run: 388/680 = 57%
   Catalog.lean::copyTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 280/491 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   UniversalK.lean::universalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%
   UniversalK.lean::exists_selfUniversalK  reproduces  UniversalK.lean::uk_encode_halt: 62/109 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_unary_copy: 558/985 = 57%
   Simulation.lean::bufferedFirstCfg_step  reproduces  UniversalStartup.lean::universalCapture_step: 725/1281 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_skip_unary: 709/1254 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   Catalog.lean::a2_map_suffix  reproduces  Catalog.lean::a2_map_block: 540/956 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_pairDup_spaceUsed: 61/108 = 56%
   Catalog.lean::Cfg.ofWords_copy_endpoint  reproduces  Catalog.lean::copyTM_run: 228/404 = 56%
   UniversalK.lean::ss_inputRewind_run  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   UniversalInterpreter.lean::universal_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock_end  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedCut_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Simulation.lean::timed_rewind: 245/435 = 56%
   Catalog.lean::f2_loop_rewind_bounded  reproduces  Catalog.lean::f2_catalogRewind: 245/435 = 56%
   Universal.lean::timedCanon_run  reproduces  UniversalStartup.lean::prefixCanon_run: 156/277 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_rawStrip_replay: 232/412 = 56%
   Finite.lean::step_output_prepend  reproduces  Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  Seam.lean::seamComp_step_right: 76/135 = 56%
   Catalog.lean::f2_counter_emit  reproduces  Catalog.lean::f2_counter_emit_run: 378/672 = 56%
   Catalog.lean::f2_rawStrip_erase  reproduces  UniversalStartup.lean::universalCapture_transfer: 72/128 = 56%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_bufferCleanup_run: 1396/2482 = 56%
   Catalog.lean::compareTM  reproduces  Catalog.lean::clearTM: 230/409 = 56%
   Catalog.lean::incrementTM_spaceUsedByTape  reproduces  Catalog.lean::clearTM_spaceUsedByTape: 244/434 = 56%
   Catalog.lean::a2_mapSetup_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 128/228 = 56%
   Catalog.lean::f2_splitRestore_first  reproduces  Catalog.lean::f2_splitPrepare_first: 151/269 = 56%
   UniversalInterpreter.lean::universalRecords  reproduces  StepBlock.lean::tableBitsK: 79/141 = 56%
   Catalog.lean::f2_splitEmbed_run  reproduces  Seam.lean::seamComp_step_left: 121/216 = 56%
   Catalog.lean::seekStartTM  reproduces  Rewind.lean::rewindTM: 98/175 = 56%
   Catalog.lean::a2_heads_join  reproduces  Catalog.lean::a2_heads_halted: 72/129 = 56%
   Catalog.lean::transferTM_run  reproduces  Catalog.lean::incrementTM_run_overflow: 274/491 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   UniversalK.lean::ss_capturedPrefix_fields  reproduces  UniversalK.lean::ss_capturedPrefix_run: 648/1163 = 56%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timedClockPrefix_length: 78/140 = 56%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::copyTM_run: 225/404 = 56%
   Catalog.lean::f2_extract_replay_finish  reproduces  Universal.lean::timedCapture_transfer: 69/124 = 56%
   UniversalStartup.lean::universalPrefix_start  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalStartup.lean::universalPrefix_bits  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Seam.lean::seamReleaseTM_runFrom_pos  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_splitEmit_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_double  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_pairDup_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::f2_incFixed_computes  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Catalog.lean::computesFunInTime_prepend_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_pairValid_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Catalog.lean::computesFunInTime_const_spaceUsed  reproduces  Catalog.lean::computesFunInTime_incFixed_spaceUsed: 61/110 = 55%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Seam.lean::seamCompTM_runFrom_left: 93/168 = 55%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_unary: 694/1254 = 55%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::f2_pairValid_run: 679/1231 = 55%
   UniversalK.lean::ss_inputRewind_run  reproduces  UniversalK.lean::ss_inputRewind_done: 177/321 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_write: 92/167 = 55%
   Catalog.lean::catalog_increment_trace  reproduces  Catalog.lean::step_of_tapeAction_move: 92/167 = 55%
   Rewind.lean::rewindTM  reproduces  Catalog.lean::skipTM: 71/129 = 55%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Universal.lean::timedCapture_init: 175/318 = 55%
   Catalog.lean::f2_scanCopy_run  reproduces  Catalog.lean::f2_scanCopy_finish: 148/269 = 55%
   UniversalStartup.lean::universal_pair_length  reproduces  Universal.lean::timedClockPrefix_length: 77/140 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   Simulation.lean::rewind_from_any  reproduces  Catalog.lean::f2_catalogRewind: 239/435 = 55%
   Catalog.lean::a2_call_run  reproduces  Catalog.lean::f2_loopHost_halt_return: 279/508 = 55%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_rawStrip_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_replay  reproduces  Universal.lean::timedCapture_transfer: 68/124 = 55%
   Catalog.lean::f2_extract_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 446/814 = 55%
   Universal.lean::timedCut_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   NDCodeSimulator.lean::rc_workReads_snoc  reproduces  StepBlock.lean::tableBitsK_groups: 77/141 = 55%
   UniversalK.lean::EffectiveMachineCode2.toK  reproduces  UniversalK.lean::EffectiveMachineCode.toK: 84/154 = 55%
   StepBlockForward.lean::fl_restore  reproduces  StepBlockForward.lean::fl_home: 78/143 = 55%
   Catalog.lean::f2_splitBody_prepare  reproduces  Catalog.lean::f2_splitBody_restore: 285/523 = 54%
   Catalog.lean::f2_extract_run  reproduces  Catalog.lean::a2_map_parse: 1035/1903 = 54%
   UniversalStartup.lean::universal_pair_get  reproduces  Universal.lean::timed_clock_get: 205/377 = 54%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_skip_fixed: 383/705 = 54%
   VirtualInput.lean::vhostCfg  reproduces  Simulation.lean::bufferedSecondCfg: 126/232 = 54%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Catalog.lean::f2_splitRestore_rewind: 442/814 = 54%
   Catalog.lean::f2_lenParse_run  reproduces  Catalog.lean::f2_pairValid_run: 668/1231 = 54%
   Catalog.lean::computesFunInTime_pairMapSnd_spaceUsed  reproduces  Catalog.lean::a2_heads_halted: 70/129 = 54%
   Catalog.lean::a2_map_parse  reproduces  Catalog.lean::f2_extract_run: 1035/1908 = 54%
   Simulation.lean::bufferTape_append  reproduces  Catalog.lean::f2_catalogBuffer_erase: 64/118 = 54%
   UniversalK.lean::EffectiveMachineCode.toK  reproduces  UniversalK.lean::EffectiveMachineCode2.toK: 84/155 = 54%
   Catalog.lean::f2_splitEmit_double  reproduces  Catalog.lean::f2_pairDup_double: 656/1212 = 54%
   StepBlockForward.lean::fl_round  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_scanCopy_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopHost_borrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_loopBorrow_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_extract_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_counter_carry  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_catalogPoly_loop  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_suffix  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backB  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::a2_map_backA  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Catalog.lean::f2_splitCount_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 123/228 = 54%
   StepBlock.lean::roundTM_effect  reproduces  StepBlock.lean::roundData_stateCell: 69/128 = 54%
   Catalog.lean::f2_extract_replay_finish  reproduces  UniversalStartup.lean::universalCapture_transfer: 69/128 = 54%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Catalog.lean::f2_loopHost_fuel_return: 736/1366 = 54%
   UniversalInterpreter.lean::universal_initialized  reproduces  UniversalStartup.lean::universalCanon_complete: 141/262 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   Finite.lean::output_prefix  reproduces  UniversalStartup.lean::universal_live_before: 65/121 = 54%
   Finite.lean::output_prefix  reproduces  Universal.lean::timedCut_live_before: 65/121 = 54%
   UniversalStartup.lean::universalCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timed_replay  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedFrame_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCapture_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Catalog.lean::a2_mapSetup_run  reproduces  Catalog.lean::catalog_redirect_loop: 75/140 = 54%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_skip_unary: 671/1254 = 54%
   Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   Catalog.lean::f2_loopCall_heads  reproduces  Catalog.lean::a2_fuel_heads: 329/615 = 53%
   Simulation.lean::ComputesInTime.spaceUsed_le  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_space_of_time  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::a2_segments  reproduces  Catalog.lean::a2_heads_halted: 69/129 = 53%
   Catalog.lean::f2_splitPrepare_extra  reproduces  Catalog.lean::f2_splitPrepare_scan: 356/666 = 53%
   Universal.lean::timedCut_count_run  reproduces  UniversalInterpreter.lean::universal_initial_skip: 518/970 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   Simulation.lean::bufferedScanCfg_run  reproduces  Catalog.lean::f2_splitPrepare_rewind: 414/776 = 53%
   Catalog.lean::f2_splitEmit_suffix  reproduces  Catalog.lean::f2_loopReplay_run: 187/351 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedCapture_transfer: 66/124 = 53%
   UniversalInterpreter.lean::universal_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   UniversalInterpreter.lean::universal_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitRestore_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_trim  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_reject  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_payload_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_fuel_return  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopHost_borrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_counter_increment  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_anyTrue_run  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Catalog.lean::f2_rawStrip_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_rawStrip_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::f2_extract_replay  reproduces  UniversalStartup.lean::universalCapture_transfer: 68/128 = 53%
   Catalog.lean::a2_mapVirtual  reproduces  Simulation.lean::bufferedSecondCfg: 123/232 = 53%
   Universal.lean::timedCut_prepare_next  reproduces  UniversalInterpreter.lean::universal_initial_skip: 513/970 = 53%
   Catalog.lean::f2_pairValid_computes  reproduces  Catalog.lean::f2_anyTrue_computes: 140/265 = 53%
   Catalog.lean::f2_splitCount_firstHalt  reproduces  Catalog.lean::f2_catalogFirstEntry: 198/375 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timed_clock_timeout: 513/975 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   Catalog.lean::a2_map_block  reproduces  Catalog.lean::f2_extract_block: 355/675 = 53%
   Catalog.lean::seekEndTM  reproduces  Rewind.lean::rewindTM: 92/175 = 53%
   Catalog.lean::f2_pairDup_computes  reproduces  Catalog.lean::f2_scanStep_right: 86/164 = 52%
   Simulation.lean::bufferedSecondCfg_step  reproduces  UniversalStartup.lean::universalCapture_init: 175/334 = 52%
   Catalog.lean::f2_loopReplay_run  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Catalog.lean::f2_counter_rewind  reproduces  Universal.lean::timedFrame_run: 66/126 = 52%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_fixed: 369/705 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::leftCfg: 68/130 = 52%
   StepBlock.lean::roundData  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   StepBlock.lean::seekTM_groups  reproduces  StepBlock.lean::seekTM_lookup: 1011/1938 = 52%
   Universal.lean::timed_input_layout  reproduces  Universal.lean::timedClockPrefix_length: 73/140 = 52%
   Catalog.lean::f2_splitCount_run  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_setup  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_catalogPoly_emit  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_stationary  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::a2_mapSetup_heads  reproduces  Catalog.lean::catalog_redirect_loop: 73/140 = 52%
   Catalog.lean::f2_timed_control_init  reproduces  Catalog.lean::f2_control_heads: 88/169 = 52%
   Catalog.lean::f2_loopReady_call  reproduces  Catalog.lean::f2_loopCall_reframe: 421/809 = 52%
   Catalog.lean::f2_rawStrip_copy  reproduces  Catalog.lean::f2_rawStrip_replay: 214/412 = 52%
   Simulation.lean::bufferedScanCfg  reproduces  Catalog.lean::a2_mapCfg: 69/133 = 52%
   Catalog.lean::f2_poly_step  reproduces  Catalog.lean::a2_mapSetup_step: 113/218 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_extract_replay_finish: 159/307 = 52%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::leftCfg_apply: 97/188 = 52%
   StepBlock.lean::roundTM_iterate  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   InputDevice.lean::rd_host_block  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_splitEmit_separator  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopHost_fuel_copy  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_lenSuffix_run  reproduces  Universal.lean::timedFrame_run: 65/126 = 52%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  UniversalStartup.lean::universalCapture_transfer: 66/128 = 52%
   Rewind.lean::rewindTM_run_ofCfg  reproduces  Catalog.lean::a2_mapSetup_run: 84/163 = 52%
   Catalog.lean::Cfg.ofWords_transfer_endpoint  reproduces  Catalog.lean::clearTM_run: 198/385 = 51%
   Catalog.lean::f2_loopFuelCaptured_frame  reproduces  Catalog.lean::f2_loopControl_payload: 128/249 = 51%
   UniversalInterpreter.lean::universal_count_run  reproduces  Universal.lean::timedCut_initial_skip: 518/1008 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::f2_catalogRewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   Catalog.lean::exists_loopTM_spaceUsed  reproduces  Catalog.lean::f2_exists_loopFind_space: 939/1831 = 51%
   StepBlock.lean::recordSkipTM_path  reproduces  StepBlock.lean::recordSkipTM_run: 555/1083 = 51%
   StepBlock.lean::succFieldTM_trace  reproduces  StepBlock.lean::succFieldTM_run: 127/248 = 51%
   Catalog.lean::a2_mapVirtual_step  reproduces  Simulation.lean::bufferedSecondCfg_step: 742/1449 = 51%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Catalog.lean::a2_mapVirtual_step: 742/1452 = 51%
   Catalog.lean::f2_loopHost_release  reproduces  Catalog.lean::f2_loopCall_frame: 269/527 = 51%
   Universal.lean::timedClockPrefix_length  reproduces  UniversalStartup.lean::universal_pair_length: 77/151 = 51%
   Catalog.lean::f2_splitRestore_scan  reproduces  Catalog.lean::f2_splitPrepare_extra: 240/472 = 51%
   Catalog.lean::f2_splitPrepare_rewind  reproduces  Catalog.lean::f2_loopBorrow_rewind: 388/764 = 51%
   Catalog.lean::f2_counter_rewind  reproduces  Catalog.lean::catalog_redirect_loop: 71/140 = 51%
   Catalog.lean::a2_map_setup  reproduces  Catalog.lean::f2_loopFuel_init: 214/422 = 51%
   UniversalK.lean::ss_bufferFinish_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   UniversalK.lean::ss_bufferCleanup_run  reproduces  UniversalK.lean::ss_live_map: 97/192 = 51%
   Catalog.lean::a2_map_move  reproduces  Simulation.lean::rightCfg_apply: 97/192 = 51%
   Catalog.lean::skipTM  reproduces  Catalog.lean::skipBackTM: 102/202 = 50%
   Catalog.lean::a2_map_reject  reproduces  Catalog.lean::a2_map_launch: 374/741 = 50%
   Catalog.lean::a2_mapCfg  reproduces  Simulation.lean::bufferedScanCfg: 69/137 = 50%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_fixed: 355/705 = 50%
   Universal.lean::timedCanon_complete  reproduces  UniversalStartup.lean::prefixCanon_complete: 161/320 = 50%
   UniversalStartup.lean::universalCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   Catalog.lean::compareTM_run_stop_ofCfg  reproduces  Catalog.lean::compareTM_run: 193/384 = 50%
   Universal.lean::timedCut_Actions  reproduces  UniversalInterpreter.lean::universalRecords: 105/209 = 50%
   Catalog.lean::f2_loopHost_frame_replay  reproduces  Catalog.lean::f2_loopControl_payload: 125/249 = 50%
   Catalog.lean::computesFunInTime_id_spaceUsed  reproduces  Catalog.lean::f2_idTM_run: 388/773 = 50%
   Catalog.lean::computesFunInTime_polyUnary_spaceUsed  reproduces  Catalog.lean::f2_unary_sharp: 176/351 = 50%
   UniversalK.lean::ss_bufferAdvance_run  reproduces  UniversalK.lean::ss_bufferClear_run: 1040/2075 = 50%
   Catalog.lean::a2_loop_round  reproduces  Catalog.lean::f2_loopHost_round: 1059/2114 = 50%
   Catalog.lean::transferTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::copyTM_spaceUsedByTape  reproduces  Catalog.lean::compareTM_spaceUsedByTape: 319/637 = 50%
   Catalog.lean::f2_loopBorrow_rewind  reproduces  Catalog.lean::f2_splitPrepare_rewind: 388/776 = 50%
   Catalog.lean::a2_fuel_heads  reproduces  Catalog.lean::f2_loopCall_heads: 329/658 = 50%
   Catalog.lean::f2_pairExtractTM  reproduces  Catalog.lean::f2_loopDebitTM: 219/438 = 50%
   Catalog.lean::f2_extract_replay_finish  reproduces  Catalog.lean::f2_rawStrip_replay: 206/412 = 50%
   Universal.lean::timedFrame_apply  reproduces  Simulation.lean::leftCfg_apply: 94/188 = 50%
   Catalog.lean::catalog_transferMap_trace  reproduces  Catalog.lean::catalog_write_take: 62/124 = 50%
   Universal.lean::timedClockCfg  reproduces  Universal.lean::timed_laneCfg: 60/120 = 50%
```

## Complete elaborated external citation list

```text
AddCancelCommMonoid.toAddCancelMonoid
AddCancelMonoid.toAddRightCancelMonoid
AddCommGroup.toAddGroup
AddCommGroup.toDivisionAddCommMonoid
AddCommMagma.toAdd
AddCommMonoid.toAddMonoid
AddCommMonoidWithOne.toAddMonoidWithOne
AddCommSemigroup.toAddCommMagma
AddGroup.toSubNegMonoid
AddGroupWithOne.toAddMonoidWithOne
AddMonoid.toAddSemigroup
AddMonoid.toAddZeroClass
AddMonoid.toNatSMul
AddMonoidWithOne.toAddMonoid
AddMonoidWithOne.toNatCast
AddMonoidWithOne.toOne
AddRightCancelMonoid.toAddRightCancelSemigroup
AddRightCancelSemigroup.toIsRightCancelAdd
AddSemigroup.toAdd
AddZero.toAdd
AddZero.toZero
AddZeroClass.toAddZero
And
And.casesOn
And.intro
And.left
And.right
Bool
Bool.casesOn
Bool.false
Bool.false_eq_true
Bool.true
Bool.true_eq_false
Classical.propDecidable
CommRing.toNonUnitalCommRing
CommSemiring.toSemiring
DFunLike.coe
Decidable
Decidable.byContradiction
Decidable.casesOn
Decidable.decide
DecidableEq
Distrib.toAdd
Distrib.toMul
Eq
Eq.mp
Eq.mpr
Eq.ndrec
Eq.rec
Eq.refl
Eq.symm
Eq.trans
Exists
Exists.casesOn
Exists.intro
False
Fin
Fin.addCases
Fin.addCases_left
Fin.addCases_right
Fin.castAdd
Fin.castLE
Fin.castLEEmb
Fin.castSucc
Fin.ext
Fin.fintype
Fin.instOfNat
Fin.isLt
Fin.last
Fin.lastCases
Fin.lastCases_castSucc
Fin.lastCases_last
Fin.mk
Fin.mk.congr_simp
Fin.natAdd
Fin.val
Fin.val_add_one_le_of_lt
Finset
Finset.Icc
Finset.card
Finset.card_le_card
Finset.card_range
Finset.card_union_le
Finset.card_univ
Finset.instHasSubset
Finset.instIsTransSubset
Finset.instMembership
Finset.instSingleton
Finset.instUnion
Finset.mem_range
Finset.mem_union
Finset.range
Finset.sum
Finset.sum_add_distrib
Finset.sum_const
Finset.sum_le_sum
Finset.univ
Fintype
Fintype.card
Fintype.card_fin
Fintype.decidableMemRangeFintype
Function.Embedding
Function.comp
Function.instFunLikeEmbedding
Function.update
Function.update.congr_simp
Function.update_eq_self
Function.update_of_ne
Function.update_self
GT.gt
GetElem.getElem
GetElem.getElem.congr_simp
GetElem?.getElem?
HAdd.hAdd
HAppend.hAppend
HMul.hMul
HPow.hPow
HSMul.hSMul
HSub.hSub
HasSubset.Subset
HasSubset.Subset.trans
Iff
Iff.mp
Iff.mpr
Iff.rfl
Int
Int.add_one_le_of_lt
Int.card_Icc
Int.decLe
Int.decLt
Int.instAdd
Int.instAddCommGroup
Int.instAddGroup
Int.instAddMonoid
Int.instAddSemigroup
Int.instCommRing
Int.instDecidableEq
Int.instLEInt
Int.instLTInt
Int.instLocallyFiniteOrder
Int.instMax
Int.instMul
Int.instNegInt
Int.instRing
Int.instSub
Int.lt_or_gt_of_ne
Int.max_def
Int.natCast_add
Int.ofNat_mul
Int.ofNat_nonneg
Int.sub_eq_zero_of_eq
Int.sub_nonneg_of_le
Int.toNat
Int.toNat_eq_max
IsOrderedAddMonoid.toAddLeftMono
IsRightCancelAdd.addRightStrictMono_of_addRightMono
IsStrictOrderedRing.toIsOrderedRing
LE.le
LE.le.trans
LT.lt
Lattice.toSemilatticeInf
Lean.Omega.Coeffs.get
Lean.Omega.Coeffs.isZero
Lean.Omega.Coeffs.ofList
Lean.Omega.Constraint.addEquality_sat
Lean.Omega.Constraint.addInequality_sat
Lean.Omega.Constraint.combine_sat'
Lean.Omega.Constraint.isImpossible
Lean.Omega.Constraint.mk
Lean.Omega.Constraint.not_sat'_of_isImpossible
Lean.Omega.Decidable.or_not_not_of_not_and
Lean.Omega.Fin.lt_or_gt_of_ne
Lean.Omega.Fin.ofNat_val_natCast
Lean.Omega.Int.add_congr
Lean.Omega.Int.le_of_not_lt
Lean.Omega.Int.lt_of_not_le
Lean.Omega.Int.mul_congr
Lean.Omega.Int.neg_congr
Lean.Omega.Int.ofNat_congr
Lean.Omega.Int.ofNat_le_of_le
Lean.Omega.Int.ofNat_lt_of_lt
Lean.Omega.Int.ofNat_mul_nonneg
Lean.Omega.Int.ofNat_sub_dichotomy
Lean.Omega.Int.sub_congr
Lean.Omega.LinearCombo
Lean.Omega.LinearCombo.add_eval
Lean.Omega.LinearCombo.coordinate
Lean.Omega.LinearCombo.coordinate_eval
Lean.Omega.LinearCombo.coordinate_eval_0
Lean.Omega.LinearCombo.coordinate_eval_1
Lean.Omega.LinearCombo.coordinate_eval_2
Lean.Omega.LinearCombo.coordinate_eval_3
Lean.Omega.LinearCombo.coordinate_eval_4
Lean.Omega.LinearCombo.coordinate_eval_5
Lean.Omega.LinearCombo.coordinate_eval_6
Lean.Omega.LinearCombo.coordinate_eval_7
Lean.Omega.LinearCombo.coordinate_eval_8
Lean.Omega.LinearCombo.coordinate_eval_9
Lean.Omega.LinearCombo.eval
Lean.Omega.LinearCombo.instAdd
Lean.Omega.LinearCombo.instNeg
Lean.Omega.LinearCombo.instSub
Lean.Omega.LinearCombo.mk
Lean.Omega.LinearCombo.mul
Lean.Omega.LinearCombo.mul_eval
Lean.Omega.LinearCombo.neg_eval
Lean.Omega.LinearCombo.sub_eval
Lean.Omega.and_not_not_of_not_or
Lean.Omega.combo_sat'
Lean.Omega.ite_disjunction
Lean.Omega.tidy_sat
List
List.IsPrefix
List.IsPrefix.eq_of_length_le
List.IsPrefix.length_le
List.append_assoc
List.cons
List.decidableBAll
List.drop
List.drop_drop
List.drop_zero
List.flatMap
List.flatMap_cons
List.flatMap_nil
List.getElem?_replicate
List.getElem_drop
List.getElem_drop._proof_1
List.instAppend
List.instGetElem?NatLtLength
List.instGetElemNatLtLength
List.length
List.length_drop
List.length_replicate
List.nil
List.nil_append
List.rec
List.replicate
Mathlib.Meta.NormNum.IsNat.of_raw
Mathlib.Meta.NormNum.IsNat.to_raw_eq
Mathlib.Meta.NormNum.isNat_add
Mathlib.Meta.NormNum.isNat_mul
Mathlib.Meta.NormNum.isNat_ofNat
Mathlib.Tactic.Ring.add_congr
Mathlib.Tactic.Ring.add_mul
Mathlib.Tactic.Ring.add_overlap_pf
Mathlib.Tactic.Ring.add_pf_add_gt
Mathlib.Tactic.Ring.add_pf_add_lt
Mathlib.Tactic.Ring.add_pf_add_overlap
Mathlib.Tactic.Ring.add_pf_add_zero
Mathlib.Tactic.Ring.add_pf_zero_add
Mathlib.Tactic.Ring.atom_pf
Mathlib.Tactic.Ring.cast_pos
Mathlib.Tactic.Ring.instCommSemiringNat
Mathlib.Tactic.Ring.mul_add
Mathlib.Tactic.Ring.mul_congr
Mathlib.Tactic.Ring.mul_one
Mathlib.Tactic.Ring.mul_pf_left
Mathlib.Tactic.Ring.mul_pf_right
Mathlib.Tactic.Ring.mul_zero
Mathlib.Tactic.Ring.of_eq
Mathlib.Tactic.Ring.one_mul
Mathlib.Tactic.Ring.zero_mul
Max.max
Membership.mem
Monoid.toNatPow
MonoidWithZero.toMonoid
MulZeroClass.toZero
Nat
Nat.add_le_add
Nat.add_le_add_left
Nat.add_le_add_right
Nat.add_sub_of_le
Nat.cast
Nat.cast_add
Nat.cast_one
Nat.cast_zero
Nat.decLe
Nat.decLt
Nat.exists_eq_add_of_le
Nat.find
Nat.find_min
Nat.find_min'
Nat.find_spec
Nat.instAddCancelCommMonoid
Nat.instAddCommMonoid
Nat.instAddCommSemigroup
Nat.instAddMonoid
Nat.instAddMonoidWithOne
Nat.instAtLeastTwoHAddOfNat
Nat.instCanonicallyOrderedAdd
Nat.instCommSemiring
Nat.instIsOrderedAddMonoid
Nat.instIsStrictOrderedRing
Nat.instLinearOrder
Nat.instMax
Nat.instNeZeroSucc
Nat.instNontrivial
Nat.instOne
Nat.instPartialOrder
Nat.instPreorder
Nat.instSemiring
Nat.instTransLe
Nat.instZeroLEOneClass
Nat.le_max_left
Nat.le_max_right
Nat.le_of_not_lt
Nat.lt_of_not_le
Nat.lt_or_gt_of_ne
Nat.mul_comm
Nat.mul_le_mul_left
Nat.mul_le_mul_right
Nat.mul_one
Nat.ofNat_pos._simp_1
Nat.rawCast
Nat.zero_add
Nat.zero_le
Ne
NeZero
Neg.neg
NegZeroClass.toZero
NonAssocSemiring.toAddCommMonoidWithOne
NonAssocSemiring.toNonUnitalNonAssocSemiring
NonUnitalCommRing.toNonUnitalNonAssocCommRing
NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring
NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring
NonUnitalNonAssocSemiring.toDistrib
NonUnitalNonAssocSemiring.toMulZeroClass
Not
OfNat.ofNat
One.toOfNat1
Option
Option.getD
Option.getD_some
Option.instDecidableEq
Option.map
Option.map_eq_none_iff
Option.map_none
Option.map_some
Option.none
Option.some
Option.some.injEq
Option.some_ne_none
Or
Or.casesOn
Or.elim
PartialOrder.toPreorder
Preorder.toLE
Preorder.toLT
Ring.toAddGroupWithOne
SemilatticeInf.toPartialOrder
Semiring.toMonoidWithZero
Semiring.toNonAssocSemiring
Set
Set.instMembership
Set.instSingletonSet
Set.mem_singleton_iff
Set.range
SignType
SignType.cast
SignType.instZero
SignType.pos
Singleton.singleton
SubNegMonoid.toAddMonoid
SubNegMonoid.toSub
SubNegZeroMonoid.toNegZeroClass
SubNegZeroMonoid.toSubNegMonoid
SubtractionCommMonoid.toSubtractionMonoid
SubtractionMonoid.toSubNegZeroMonoid
Sum
Sum.inl
Sum.inr
Trans.trans
True
Turing.Action
Turing.Cfg
Turing.Cfg.ext
Turing.Cfg.init
Turing.Cfg.init_inputPos
Turing.Cfg.init_output
Turing.Cfg.init_state
Turing.Cfg.init_workTapePos
Turing.Cfg.init_workTapes
Turing.Cfg.inputPos
Turing.Cfg.inputSymbol
Turing.Cfg.mapState
Turing.Cfg.mapState_inputPos
Turing.Cfg.mapState_mapState
Turing.Cfg.mapState_output
Turing.Cfg.mapState_state
Turing.Cfg.mapState_workTapePos
Turing.Cfg.mapState_workTapes
Turing.Cfg.mk
Turing.Cfg.output
Turing.Cfg.state
Turing.Cfg.workTapePos
Turing.Cfg.workTapeSymbols
Turing.Cfg.workTapes
Turing.FinTM
Turing.FinTM.ComputesFunInTime
Turing.FinTM.ComputesInTime
Turing.FinTM.ComputesInTime.mono
Turing.FinTM.State
Turing.FinTM.bufferTape
Turing.FinTM.bufferTape_of_neg
Turing.FinTM.computesInTime_iff
Turing.FinTM.k
Turing.FinTM.mk
Turing.FinTM.tm
Turing.Lockstep
Turing.Lockstep.cut
Turing.Lockstep.runFrom
Turing.MultiTapeTM
Turing.MultiTapeTM.initCfg
Turing.MultiTapeTM.initCfg_eq
Turing.MultiTapeTM.mem_visitedByTapeHead_iff
Turing.MultiTapeTM.mk
Turing.MultiTapeTM.output_prefix
Turing.MultiTapeTM.q₀
Turing.MultiTapeTM.runFrom
Turing.MultiTapeTM.runFrom_add
Turing.MultiTapeTM.runFrom_of_halt
Turing.MultiTapeTM.runFrom_output_eq_of_halt
Turing.MultiTapeTM.runFrom_state_ne_none_of_le
Turing.MultiTapeTM.runFrom_succ_eq_step
Turing.MultiTapeTM.runFrom_with_q₀
Turing.MultiTapeTM.runFrom_zero
Turing.MultiTapeTM.spaceUsed
Turing.MultiTapeTM.spaceUsedByTape
Turing.MultiTapeTM.spaceUsedByTape_eq_card
Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed
Turing.MultiTapeTM.spaceUsed_eq_sum
Turing.MultiTapeTM.step
Turing.MultiTapeTM.tr
Turing.MultiTapeTM.visitedByTapeHead
Turing.MultiTapeTM.visitedByTapeHead_add_subset
Turing.RewindPhase
Turing.RewindPhase.done
Turing.RewindPhase.start
Turing.StepBlock.exists_forwardLoopTM
Turing.StepBlock.forwardLoopCfg
Turing.StepBlock.forwardLoopCfg_inputPos
Turing.StepBlock.forwardLoopCfg_output
Turing.StepBlock.forwardLoopCfg_state
Turing.StepBlock.forwardLoopCfg_workTapePos
Turing.StepBlock.forwardLoopCfg_workTapes
Turing.StepBlock.summaryCells
Turing.StepBlock.summaryCells_eq
Turing.embedEmitCfg
Turing.embedEmitCfg_eq
Turing.embedEmitCfg_output
Turing.embedEmitCfg_state
Turing.embedEmitTM
Turing.embedEmitTM_runFrom
Turing.embedEmitTM_visitedByTapeHead
Turing.embedEmitTM_visitedByTapeHead_frame
Turing.exists_rulerHostTM
Turing.exists_selfStartupTMK
Turing.inputMoveAction
Turing.inputSymbolInner
Turing.instDecidableEqRewindPhase
Turing.instFintypeRewindPhase
Turing.instInhabitedCfg.default._proof_1
Turing.length_pairEncode
Turing.moveInputPos
Turing.moveInputPos_pos_of_ne_right
Turing.moveInputPos_pos_of_ne_right._proof_1
Turing.pairEncode
Turing.pairEncode_drop
Turing.rewindTM
Turing.rewindTM_run_ofCfg
Turing.rulerHostCfg
Turing.rulerHostCfg._proof_2
Turing.rulerHostCfg_inputPos
Turing.rulerHostCfg_output
Turing.rulerHostCfg_state
Turing.rulerHostCfg_workTapePos
Turing.rulerHostCfg_workTapes
Turing.seamCompTM
Turing.seamCompTM_firstReturn_ofCfg
Turing.seamCompTM_runFrom_left
Turing.seamCompTM_runFrom_right
Turing.seamCompTM_run_ofCfg
Turing.seamCompTM_visitedByTapeHead_ofCfg
Turing.serializeK
Turing.step_of_tapeAction_write
Turing.tableBitsK
Turing.tapeAction
Turing.unaryFin
Union.union
Zero.ofOfNat0
Zero.toOfNat0
add_assoc
add_sub_cancel
add_sub_cancel_right
add_zero
and_false
and_self
congr
congrArg
congrFun
contravariant_lt_of_covariant_le
contravariant_swap_add_of_contravariant_add
covariant_swap_add_of_covariant_add
dite
eq_false
eq_self
eq_true
false_and
forall_congr
funext
id
if_neg
if_pos
implies_congr
instAddNat
instDecidableAnd
instDecidableEqBool
instDecidableEqFin
instDecidableEqNat
instDecidableEqSum
instDecidableIff
instDecidableNot
instDecidableOr
instDecidableTrue
instFintypeSum
instHAdd
instHAppendOfAppend
instHMul
instHPow
instHSMul
instHSub
instLENat
instLTFin
instLTNat
instLatticeInt
instMulNat
instNatCastInt
instNeZeroNatHAdd_1
instOfNat
instOfNatAtLeastTwo
instOfNatNat
instSMulOfMul
instSubNat
instTransEq
instTransEq_1
ite
ite_cond_eq_false
ite_cond_eq_true
ite_congr
le_of_le_of_eq
le_refl
le_rfl
lt_mul_iff_one_lt_left'._simp_4
of_decide_eq_true
of_eq_true
one_lt_mul_iff._simp_4
or_true
propext
rfl
smul_eq_mul
sub_zero
zero_add
zero_lt_one._simp_1
```
