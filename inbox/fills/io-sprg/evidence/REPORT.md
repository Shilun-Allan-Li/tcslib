# io-sprg Phase A — checkpoint 4 (M4), READY for packaging

All sixteen frozen M4 original bodies and thirteen M4 theorem-only helpers have saved CHECKED_PASS records at `428c7eb117b51fe512348f226284df247e98c00c`. The supplied fresh local M4 artifacts have been cross-checked. **M4 packaging and publication remain pending.**

This is an intermediate Phase A checkpoint. M5–M6 and the full final proof gates
remain unfinished. T1–T6 remain the named, unproved Phase B efficiency hypotheses.
No end-to-end completion or Phase B implementation is claimed.

M3 source `04249b85e80a007dc5845077a18a365d5150e14b` was published at exchange
`2a9ccadc2772789ace445490f6df8d231ff1221b`. Its delivery record reports a successful
non-force push, an exact 6,349-file payload path set and zero committed SHA-256
mismatches. The retained M3 report below predates that push and therefore says
publication is pending; that wording is historical and is superseded by
`evidence/delivery/M3.json`, whose captured hash is bound outside this report.
An M4 package cannot contain its own future exchange push hash. M4 publication
status is stated separately below and must come from its later delivery record.

## Current source scope and milestone status

Current source-head context: `428c7eb117b51fe512348f226284df247e98c00c`. The supplied committed inventory and captured source hashes bind this source snapshot; Git ancestry/diff verification is a separate root-owned gate, not performed by this renderer.
The source branch remains `fill/io-sprg` on pinned base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, without rebasing. Delivery writes only
`inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

| Quantity | Current value | Authority and limitation |
| --- | --- | --- |
| Owned source files | 34 | Exact supplied committed inventory |
| Explicit source headers | 703 | Fresh freeze census |
| Cumulative helpers inserted | 33 | Inserted is not checked; the separate checked-helper row determines proof status |
| Source size/width | 10,656 lines; largest 801; width 100 | Current filesystem byte/line measurement; committed binding separately required |
| Saved proof records | 163 records; 163 CHECKED_PASS; pending [] | Saved step JSON records; inserted/unverified bodies are not passes |
| Completed originals | 130 | M3 historical 114 + M4 checked 16 |
| Checked theorem-only helpers | 33 | M3 historical 20 + M4 checked 13 |
| Remaining original direct holes | 16 | Fresh source inventory |
| Frozen headers/prose and moves | 670 unchanged; 93 exact moves | /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checks/M4-complete-worktree-freeze/summary.json |

| M4 source commit | Role | Exact subject/metadata status |
| --- | --- | --- |
| ed37984916cfb19a91732137e4e99e75e21fe995 | Modular reduction interfaces | io-sprg: M4 modular reduction interfaces and proof owners |
| 3a8f1b5e4fd568cf3273d97802abddbfd5ee7dd2 | Hybrid endpoints and statistical bounds | io-sprg: M4 hybrid endpoints and statistical coupling bounds |
| c44841d3ba8af56a407d3d30b7c4720617c0d845 | PRG hop and reduction encodings | io-sprg: M4 every-realiser PRG hop and reduction encoding bounds |
| 72b3b975e376a2d0ac72d787fe1ac4117b84bb54 | Canonical LPN transport and hop | io-sprg: M4 canonical LPN transport and every-realiser hop |
| 428c7eb117b51fe512348f226284df247e98c00c | Explicit security inequalities | io-sprg: M4 explicit security advantage inequalities |

The complete 34-commit source ledger, including exact author, committer, date and
signature metadata, is `evidence/checkpoints/M4/source-commits.json`. The table
above lists all five M4 source commits; exchange delivery has its own later record.

## M4 originals and proof status

The six hybrid originals, six reduction-encoding originals, two reduction hops,
`lemma42` and `prop41` are the sixteen frozen M4 originals. Source anchors in this
section belong to the current captured source; historical anchors below retain
their original checkpoint scope. Saved CHECKED_PASS records are proof checks,
not substitutes for a fresh complete owner build or final canonical seals.

| Frozen declaration (area prefix omitted) | Current source anchor | Saved step/status |
| --- | --- | --- |
| Params.hyb_real_eq_raw | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:156 | 135: CHECKED_PASS |
| Params.hyb_random_eq_raw | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:168 | 136: CHECKED_PASS |
| Params.hyb_prg_accept_eq_chain_zero | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:184 | 137: CHECKED_PASS |
| Params.hyb_uniform_accept_eq_chain_zero | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:199 | 138: CHECKED_PASS |
| Params.hyb_real_prg_le | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:213 | 140: CHECKED_PASS |
| Params.hyb_uniform_random_le | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:289 | 141: CHECKED_PASS |
| Params.lpnEnc_injective | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Encoding.lean:46 | 145: CHECKED_PASS |
| Params.encLPNAdvice_injective | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Encoding.lean:60 | 146: CHECKED_PASS |
| Params.encLPNAdvice_length_le | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Encoding.lean:107 | 147: CHECKED_PASS |
| Params.prgEnc_injective | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Encoding.lean:46 | 148: CHECKED_PASS |
| Params.encPRGAdvice_injective | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Encoding.lean:58 | 149: CHECKED_PASS |
| Params.encPRGAdvice_length_le | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Encoding.lean:89 | 155: CHECKED_PASS |
| Params.prg_hop | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Hop.lean:288 | 153: CHECKED_PASS |
| Params.lpn_hop | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Hop.lean:342 | 161: CHECKED_PASS |
| lemma42 | TCSlib/Cryptography/Obfuscation/StructuredSeed/Security.lean:62 | 162: CHECKED_PASS |
| prop41 | TCSlib/Cryptography/Obfuscation/StructuredSeed/Security.lean:124 | 163: CHECKED_PASS |

## Supporting theorem-only helpers

Four PRG helpers and nine LPN helpers are the completed M4 support scope. The table
binds each helper to its checked source and saved proof step.
A prepared body, installed statement, overlap suggestion or failed repair is not
counted as a proved helper. Additional helpers require explicit independent
admission and updated counts; they cannot be hidden in these thirteen rows.

| Helper (area prefix omitted) | Current source anchor or proposed owner | Saved step/status |
| --- | --- | --- |
| Params.sdCore_publicSeed | TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean:115 | 139: CHECKED_PASS |
| Params.prg_verdict_prob | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Hop.lean:49 | 142: CHECKED_PASS |
| Params.prg_nuisance_average | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Hop.lean:98 | 143: CHECKED_PASS |
| Params.prg_chain_accept_average | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG/Hop.lean:200 | 144: CHECKED_PASS |
| Internal.lpn_accept_realizes_eq | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Transport.lean:49 | 150: CHECKED_PASS |
| Internal.lpn_gap_realizes_eq | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Transport.lean:85 | 151: CHECKED_PASS |
| Internal.lpn_uniform_challenge_reindex | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Transport.lean:109 | 152: CHECKED_PASS |
| Internal.lpn_real_seed_reindex | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Transport.lean:145 | 154: CHECKED_PASS |
| Internal.lpn_pre_real_update | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Sections.lean:47 | 156: CHECKED_PASS |
| Internal.lpn_pre_uniform_update | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Sections.lean:84 | 157: CHECKED_PASS |
| Internal.lpn_real_section | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Sections.lean:122 | 158: CHECKED_PASS |
| Internal.lpn_uniform_section | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Sections.lean:192 | 159: CHECKED_PASS |
| Internal.lpn_fix_advice | TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Hop.lean:53 | 160: CHECKED_PASS |

## Hybrid and PRG proof route

The endpoint proofs read the actual raw index/seed laws through public readers.
SP-W2 is preserved: the chain-zero links assert semantic acceptance equalities,
not equal free-oracle programs with an extra unused query. The statistical hops
use the actual joint draw and shared finite probability transport; no uniformity
of the Boolean primitive's index distribution is assumed.

`Params.sdCore_publicSeed` is owned early in Hybrids, before its consumers, to
avoid a dependency cycle through PRG/Hop. The PRG verdict transport uses the
specific shared `RealizesOn.runAt_coinsEquivPoly_symm` reader after the generic
NUPPT verdict reader, then the existing prefix-coin marginalization. It does not
rederive a more specialized public realization identity inline.

The nuisance-law helper reindexes the actual finite draw and exact PRGAdvice law
through their explicit existing equivalences. The chain-average helper transports
advice through `PRGAdvice.prodEquiv`, consumes the reconstructed record via
`prgPre_eq`, and only then rewrites the inverse size. The public
`Equiv.coe_fn_symm_mk` reduces the inverse constructor. This avoids an invalid
rewrite motive caused by field types hiding `kappaOfN (n κ)` inside PRGAdvice.
Failed attempts and subsequent checked repairs stay archived; the checked source
and bound logs determine the proof claim. The PRG hop selects one advice family
before every realizing adversary and every κ, as frozen; it neither assumes nor
constructs a Phase B realizer.

## LPN proof route

The canonical LPN encoding remains exactly the assumption family's challenge
encoding. The construction modulus stays prime-first in its own challenge and
advice; this does not alter the preexisting assumption's canonical challenge.
The three LPN and three PRG encoding obligations reuse their canonical encoding
readers, shared fixed-width/list facts and explicit polynomial length bounds.

LPN helper01 transports the verdict through the required shared realization and
coin-prefix readers; helper02 expresses the canonical assumption gap. Helper03
reindexes the uniform matrix/output law. Helper04 reindexes the exact joint
matrix/secret/noise draw. A fresh-record calculation proves both matrix and noisy-value
coherence using public sample readers and explicit noise-seed cast cancellation.
A focused copy with `lpnNoise` irreducible passes with zero errors, warnings and sorrys;
this single-definition check is separate from the required final canonical matrix.
Its request and result are `evidence/checks/M4-lpn-transport-noise-opacity/`. Helper05 and helper06
identify actual real/uniform preprocessing updates. Helper07 and helper08 identify
the corresponding chain sections as acceptance probabilities. Helper09 performs
finite nuisance-law averaging and fixes advice. The frozen `lpn_hop` then composes
these facts. None changes an algorithm, encoding, parameter, assumption, or frozen
quantifier. All six helper04–09 bodies have bound CHECKED_PASS records.

## Search admission and reuse provenance

The required record is a per-declaration name/shape search and an isolated
exact?/apply? pair, with the mathematical goal and imported source hash recorded.
Public-only expanded cores exclude every StructuredSeed module. Actual algorithm
reader probes may use earlier owned definitions only when the target theorem is
absent from the bound imported source; these have a separate scope and cannot be
reported as public-only searches. Each future consumer must retain the most
specific required shared API rather than repeat its generic proof.

| Family | Required provenance and current status |
| --- | --- |
| Four PRG helpers | M4-PRG-name-shape, helper-specs-v3, fresh exact/apply core bindings; sdCore uses publicMap v2. Most-specific shared realization/coin-prefix reuse is explicit. |
| Six hybrid originals | M4-PRG name/shape and endpoint/statistical-hop core probes; semantic acceptance only, actual joint law, no uniform-index premise. |
| Six encoding originals | M4Advice 01–06 mathematical cores; shared canonical encoding and fixed-width APIs. Owned Basic reuse controls are separate, not public-only admission. |
| PRG hop | M4PRG prg_hop_fix_advice_core and four checked helper bodies; advice family before all realizing adversaries/all κ, finite averaging and existing prefix law. |
| LPN helper01–03 | Actual-definition probes import earlier LPN/Defs with target absent; canonical challenge and mandatory realization readers. V1/V2 repairs remain attributed. |
| LPN helper04–09 and hop | Checked bodies and fresh provenance bound above. 04 joint real draw; 05/06 preprocessing; 07/08 sections; 09 advice averaging. |
| lemma42/prop41 | Checked source/probe records bound above; finite hybrid triangle/telescope reuses public APIs and preserves every-realiser quantifiers. |
| Fresh exact admission ledger | /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/overlap-admission.json; exact 29-row scope, artifact hashes checked; outcomes are not proofs |

The old PRG sdCore template used reserved binder `public` and its original pair
was invalid. Root retained it and used a fresh `publicMap` v2 template; invalid
runs never satisfy admission. The first LPN01 runtime guard also used reserved binder `prefix`; its invalid V1
pair is retained and excluded. Fresh V2 uses `areaPrefix` and observes all ten target
names absent before searching. Probe repair history is preserved rather than
relabelled as a successful search. Finite inconclusive searches establish no
global absence claim and are not proof evidence.

## Fresh M4 local gates and later final gates

| Check | Fresh M4 result and bound evidence |
| --- | --- |
| committed_inventory | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/inventory/inventory.json |
| source_inventory | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/statements/source-inventory-binding.json |
| all_owner_build | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/build/M4/all-owners/results.jsonl |
| static_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/static/summary.json |
| freeze_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checks/M4-complete-worktree-freeze/summary.json |
| selected_axiom_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/axiom-summary.json |
| selected_names | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/selected-theorem-names.json |
| selected_owner_names | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/selected-owner-names.json |
| headline_names | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/headline-names.json |
| warning_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/warning-summary.json |
| slot_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/host/M4-final-v1/slot-summary.json |
| commits_ledger | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/source-commits.json |
| overlap_summary | Supplied/hash-checked: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence/checkpoints/M4/overlap-admission.json |
| Selected axiom scope | 422 exact selected names, standard-only; selected scope, not full stored-root census |
| Headline Params.G4_eval_eq | Classical.choice, Quot.sound, propext |
| Headline Params.claim42 | Classical.choice, Quot.sound, propext |
| Headline Params.realizable_of_targets | Classical.choice, Quot.sound, propext, sorryAx |
| Headline PrimeSchedule.nonempty | Classical.choice, Quot.sound, propext |
| Headline exists_sprg_of_targets | Classical.choice, Quot.sound, propext, sorryAx |
| Headline exists_sprg_of_targets_subexp | Classical.choice, Quot.sound, propext, sorryAx |
| Headline exists_sprg_raw | Classical.choice, Quot.sound, propext, sorryAx |
| Headline exists_sprg_raw_subexp | Classical.choice, Quot.sound, propext, sorryAx |
| Headline jlsSPRG | Classical.choice, Quot.sound, propext, sorryAx |
| Headline jls_hasComplexity | Classical.choice, Quot.sound, propext |
| Headline jls_hasPolyStretch | Classical.choice, Quot.sound, propext |
| Headline jls_secure | Classical.choice, Quot.sound, propext, sorryAx |
| Headline jls_subexpSecure | Classical.choice, Quot.sound, propext, sorryAx |
| Headline jls_subexpSmall | Classical.choice, Quot.sound, propext, sorryAx |
| Headline lpnNoise_law | Classical.choice, Quot.sound, propext |
| Headline prop41 | Classical.choice, Quot.sound, propext |
| Headline theorem41 | Classical.choice, Quot.sound, propext, sorryAx |
| Headline theorem41_of_targets | Classical.choice, Quot.sound, propext, sorryAx |
| Headline theorem41_subexp | Classical.choice, Quot.sound, propext, sorryAx |
| Tagged wrapper counts | 1460 acquisitions; historical max2/serial=false; post-correction 691 acquisitions serial=true; active0. Wrapper-snapshot qualification only. |

The M0 complete stored-constant graph, kernel-type dump and four-variant Rule10
matrix remain historical. Intermediate selected public theorem prints do not
establish a complete stored-root census or canonical opacity closure. M0 counts
(22 owners, 88 seals, 96 controls, 1,036 stored constants, 948 public kernel types,
511 theorem prints) are never reused as M4 scope. M1–M3 local gates retain their
published scopes in the complete historical report below.

The V2 final-audit adapters remain candidates unless their actual fresh runs are
supplied. Final inventory must discover every new committed owner, including
Basic, Claim42 splits, reduction splits and LPN/Sections. Every owner receives all
four required variants (strict diagnostics separately attributed; canonical coe-A/coe-B
passes required) and every eligible paired reader control, with complete
conservative closures, source/log/object/environment bindings, runtime masks,
chunks and EOF checks. New direct Mathlib roots require their exact narrowed
cache ledger. No count reduction or schema bypass is authorized by this report.

## Statement changes and modularity decisions

No post-M0 header or pre-sketch statement prose changed. The current exact source
inventory reports 703 headers: 670 frozen declarations plus 33 theorem-only helpers.
The 93 moves comprise the earlier 14 Claim42 moves and 79 M4 reduction moves.
LPN Transport owns canonical coordinate/realizer transport, Sections owns pointwise
and section identities, and Hop owns advice selection and the every-realizer conclusion.
PRG has corresponding definition, encoding and hop modules. Existing public names are
preserved. The early public-seed helper lives in Hybrids to keep the import graph acyclic.

The 10,656 lines exceed the dispatch's 8,450-line upper estimate. Explicit finite-law,
canonical sample-coherence and global advice-family proofs account for the increase.
The source is kept in coherent modules, each at most 801 lines and width at most 100;
the named Phase B obligations retain their hypothesis-only role.

Step154 was temporarily returned to its explicit ladder stub while independent section
proofs were checked. Those historical checks state that context. The completed helper,
fresh all-owner build and current standard-only prints supersede the temporary context.
For step160, root interrupted only recorded child75575 after a 312.77-second diagnostic
run, verified all recorded wrapper/time/script/Lean processes exited, and retained the
abort under `evidence/build/M4/step160/`. A bounded diagnostic isolated an omitted
function argument in `(hpairPost _).symm`; supplying both exact predicates removed the
sampling-enumeration unification work. The bounded v3 check and ordinary final owner
check pass. These diagnostic artifacts remain separate from proof-pass evidence.

The raw axiom-run substring counter records one occurrence of `error` in the legitimate
name `Params.packSeed_error`. Both actual diagnostic error forms are zero; the source/log
hashes and the unmodified raw counter remain in the current axiom summary.

## Frozen statements, efficiency boundary and process disclosures

The global frozen interface consists of all 670 M0 FQNs, kinds, normalized headers
and pre-sketch statement-prose prefixes. Moves require an explicit exact ledger;
per-file removals/additions are retained and reconciled globally. Header/prose
preservation is separate from a fresh generated full-kernel-type comparison.
Fresh source guard matches all current source hashes. Its WORKTREE_CANDIDATE label is retained; committed binding and full kernel types remain separate checks.

SP-W1 retains rational δ with real analytic coercions; SP-W2 retains only the two
acceptance equalities; SP-W3 retains growing seed size as part of polynomial
stretch. The public prime and schedule remain inputs. Primitive uniform
sampler/evaluator efficiency fields remain mandatory. T6 chooses ONE shared
sampler/machine witness before every prime schedule, not separately after π.
The frozen advice-family-before-all-realisers/all-κ reductions and fixed shared
subexponential exponent remain unchanged. T1–T6 truth is still Phase B.

Both recorded process breaches remain disclosed. An extra research descendant
exceeded the whole-job two-subagent limit; root interrupted it. The no-Lean/cache/
push/source-mutation account is based on task reports, not an independent process
audit. Separately, tagged wrappers 93883 and 93983 overlapped from
15:07:45–15:07:48UTC; the recorded child was terminated and the prior wrapper
released at15:08:34UTC. The records remain `evidence/host/team-limit-correction.json`
and `evidence/host/search-process-correction.json`. Fresh slot evidence must retain
all tagged lines and REAP provenance, fail any other overlap, report whole-history
seriality false and qualify any verified post-correction serial suffix separately.
It cannot establish a global host process cap or complete child-process history.

The paper SHA-256 remains
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF may be copied, committed or delivered. This report preparation makes no
new resource-measurement claim. All prior opacity repairs, warning cleanups,
StatementChanges and design deviations remain intact in the historical appendix.

## Remaining work and delivery

M4 local proof work is complete; the sixteen M5/M6 frozen original obligations remain (seven raw security/existence and nine target links/assemblies). Full fresh final canonical gates remain pending; Phase B targets remain hypotheses.

M4 delivery: PENDING packaging/publication; no M4 exchange hash is claimed.
The later packager must replay exact committed source at the pinned base,
including the M0 empty marker; verify the bundle; check every intermediate tree
for PDFs; and bind exact source/evidence manifest path sets and hashes. The report
contains no circular self-hash; the generator records it in an external binding.
This renderer is formatting and evidence cross-checking, not the final audit gate.

## Complete retained M3 report and earlier historical records

The following complete M3 report is retained byte-for-byte. All statements inside
this appendix, including its former publication-pending wording and source
anchors, have their original historical M3 scope. Its fidelity, Rule15, target
selection, non-vacuity, Phase B, StatementChanges, deviations, process disclosures
and M0–M3 gate records are preserved; the current M4 layer above supersedes only
current status, anchors and delivery observations.

<!-- BEGIN BYTE-EXACT HISTORICAL M3 REPORT -->
# io-sprg Phase A — checkpoint 3 (M3), repaired v2

M3 Claim 4.2 and all ten original M3 obligations are proved and locally checked at
`04249b85e80a007dc5845077a18a365d5150e14b`. All 26 owned modules pass the fresh
build, all 134 saved proof steps are CHECKED_PASS, and all 335 selected public
theorems in 17 completed owners print only standard axioms. Six of 19 current
headlines are standard-only, now including `Params.claim42`; thirteen later
headlines still retain sorryAx.

This is an intermediate proof checkpoint. **M3 packaging and publication remain
pending.** M4–M6 and the full final proof gates remain unfinished, with 32 original
direct proof holes. T1–T6 remain the named, unproved Phase B efficiency hypotheses.
The complete end-to-end goal is not yet finished.

M0 was frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7` and delivered at
exchange `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`. M1 source
`19dde91afc384656e7e47cb018057e088d4ded0a` was published at exchange
`10da7fdefd9a44023cc117a672f19e8a3617b81d`. M2 source
`4ecc40c04a001bc87349b7ec368ece309774c28a` was published at exchange
`c1d4f422f071f4a8e346d71a0f00ea3525941eee`. `evidence/delivery/M2.json`
records its successful non-force push, exact 5,270-file payload path set and zero
committed SHA-256 mismatches. These remain historical M2 delivery results.

The source branch is `fill/io-sprg` on base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, without rebasing. Delivery writes
only `inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

## Milestones

Cumulative source line counts refer to each named historical source checkpoint.

| Milestone | Status | Source commit | Cumulative source lines |
| --- | --- | --- | --- |
| M0 statements | Frozen and published | `d10a560b34d58919bc1a5206ce66a444613f94c7` | 5,911 (22 owners) |
| M1 algebraic correctness | Complete and published | `19dde91afc384656e7e47cb018057e088d4ded0a` | 7,244 (23 owners) |
| M2 stretch | Complete and published | `4ecc40c04a001bc87349b7ec368ece309774c28a` | 7,694 (23 owners) |
| M3 Claim 4.2 | Proofs/local gates complete; packaging/publication pending | `04249b85e80a007dc5845077a18a365d5150e14b` | 8,672 (26 owners) |
| M4 hybrids/reductions | Unfinished | No completion commit | Not measured as complete |
| M5 raw security/existence | Unfinished | No completion commit | Not measured as complete |
| M6 target links/assemblies | Unfinished; target truth stays Phase B | No completion commit | Not measured as complete |

## Source commits and confirmed proof scope

| M3 source checkpoint | Commit |
| --- | --- |
| First M3 source commit | `e966956e25caf9512050ddf5d480a5dec7f4d3de` |
| Second M3 source commit | `bc5d5227a52571ad5e1e9b86219cfcb4987b7771` |
| Third M3 source checkpoint (pre-opacity repair) | `c767ee867e76c0b1248cee46d4af5296ffa078d5` |
| Fourth M3 source commit, repaired v2 | `04249b85e80a007dc5845077a18a365d5150e14b` |

The final package's COMMITS.tsv must supply exact source-commit subjects and
metadata; no exchange delivery hash is inferred from these source hashes.

M3 fills all ten frozen original obligations (five Load and five Claim42 obligations) and adds fourteen
theorem-only helpers: six numerical bounds, six conditional probability bounds,
and two specialized semantic readers (joint-law transport and cast-indexed noise law).
The joint-law reader avoids duplicating the same sampler transport in the decomposition and Cond2 proof; Cond3 also reuses it.
It adds no algorithm or sampler. The decomposition consumer received a fresh root
check after this refactor. Cond2's repaired local index projection closes by rfl;
no projection equality or transport premise was added to a frozen statement.

| Confirmed source/proof quantity | Value | Evidence and limit |
| --- | --- | --- |
| Owned source modules, including both facades | 26 | Exact current inventory; fresh full build pass |
| Explicit source headers | 690 | Fresh base→HEAD decls2: 690 ADDED, zero CHANGED/REMOVED |
| Frozen M0 headers and statement-prose prefixes | 670 unchanged | Global freeze PASS, no approved prose change |
| Cumulative new theorem-only helpers | 20 (M1 3 + M2 3 + M3 14) | Global map; all twenty are standard-only in fresh selected prints |
| Existing declarations relocated | 14 | Exact move ledger and retained per-file decls2 rows |
| Saved checked proof steps | 134 CHECKED_PASS | Read all evidence/steps/001–134/step.json records |
| Completed original bodies | 114 (M1 100 + M2 4 + M3 10) | Root-confirmed original/helper classification |
| Remaining original direct holes | 32 | Root-confirmed; no transitive sorryAx-dependent count inferred |
| Source size and width | 26 files; 8,672 lines; largest 801; width ≤ 100 | Direct byte/line measurement, source hashes match freeze snapshot |

The global freeze remains explicitly a source-bound WORKTREE_CANDIDATE audit.
This preparation checked every captured source hash against the repaired current
files and fresh committed-source static inventory. Root supplied the source head;
this preparation invoked no Git. Source header/prose preservation is separate
from the later complete generated kernel-type audit.
Intermediate progress snapshots retain their earlier scope; the repaired source
inventory and fresh v2 evidence below determine this checkpoint status. Fresh source/build/static/selected-axiom/slot evidence is recorded below; the
complete stored-root/kernel-type/canonical seal suite remains a later final gate.

## Claim 4.2 proof route

The finite load bound counts `(t+1)`-element witnesses inside the overloaded
intersection. For each fixed witness subset, `Equiv.piEquivPiSubtypeProd` separates
selected from unused placement coordinates. Public `uprob_comp_equiv`, `uprob_fst`,
`OneWay.uprob_pi_forall` and `OneWay.uprob_eq_one_div_card` give the exact reciprocal
bucket probability. Public `uprob_exists_le` and `Finset.card_powersetCard` then give
`choose(|S|,t+1)/B^(t+1)`. Union over all B labels and specialize `S=univ` for the
remaining load bounds. This counts all labels and preserves the strict threshold
at every finite parameter, including zero thresholds.

The binomial estimate composes public natural-choice/factorial bounds and the
existing exponential-series estimate. The checked-root API correction to the
staged body supplies the explicit real argument to
`Real.pow_div_factorial_le_exp (k : ℝ) ... k`; discarded/failed attempts remain
archived. The source proof and root's final check are the authority, not the
untested preparation packet.

The locality estimate bounds the expected BAD cardinality by summing per-output
coordinate failures. The existing finite probability/expectation and Markov APIs
supply Cond1's single-repetition bound. The complete index is fixed **before**
independence over noise repetitions is used. Only afterwards is the bound averaged
under the actual index sampler. No uniform distribution on Boolean generator
indices is assumed.

Cond2 fixes all nuisance data while leaving the genuine placement draw uniform.
The small-set condition is handled inside the event; a BAD set larger than Γ is
not assumed away by an extra global premise. Cond3 uses the full-load estimate.
`Params.jointLaw_prob_eq_uprob` transports events through the actual deterministic
index/seed cores from one uniform raw product draw, once, and is reused by the
specialized decomposition and Cond2 proof. This is semantic probability equality;
no equality of free-oracle programs is asserted for unused queries.

The decomposition reuses `Correctness.firstGood_none_iff`. Polynomial bucket-count
bounds and the shared public polynomial/exponential growth APIs yield one eventual
cutoff. The final frozen statement is
`∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PrimeParam κ, errProb κ pp ≤ 2⁻κ`:
the cutoff precedes the public prime. Internal positive/large-κ helper hypotheses
do not change that statement or impose a new positive-κ premise on the raw family.
The rational δ convention remains SP-W1; no new analytic assumption on δ or the
noise width is introduced for Claim 4.2.

## Original M3 declarations

These current anchors and saved checked steps refer to the repaired M3 v2 source.
The fresh full-owner build and completed-owner axiom probes pass.

| Declaration (area prefix omitted) | M3 v2 source anchor | Saved step |
| --- | --- | --- |
| `Params.errProb_nonneg` | `Claim42/Defs.lean:135` | 116: CHECKED_PASS |
| `Params.badSet_expect_le` | `Claim42/Defs.lean:146` | 117: CHECKED_PASS |
| `Params.cond1_prob_le` | `Claim42/Defs.lean:274` | 118: CHECKED_PASS |
| `Params.errProb_le_decomposition` | `Claim42/Conditions.lean:268` | 119: CHECKED_PASS |
| `Params.claim42` | `Claim42.lean:58` | 133: CHECKED_PASS |
| `Internal.binomial_bound` | `Claim42/Load.lean:54` | 111: CHECKED_PASS |
| `Internal.bucket_tail` | `Claim42/Load.lean:91` | 112: CHECKED_PASS |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:177` | 113: CHECKED_PASS |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:194` | 114: CHECKED_PASS |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:206` | 115: CHECKED_PASS |

## New M3 theorem-only helpers

All fourteen helper bodies have saved CHECKED_PASS records and standard-only
axioms in the fresh selected probe. The fourteenth is the cast-indexed scalar
noise-law reader, step 134, owned beside lpnNoise in LPN.lean. It is not a new
algorithm or assumption. Per-helper public reuse and search scopes are recorded
below; search suggestions themselves are not proof evidence.

| Declaration (area prefix omitted) | M3 v2 source anchor | Saved step |
| --- | --- | --- |
| `Internal.bucket_count_upper` | `Claim42/Bounds.lean:41` | 120: CHECKED_PASS |
| `Internal.bucket_count_lower` | `Claim42/Bounds.lean:57` | 121: CHECKED_PASS |
| `Internal.prefactor_eventually_le_two_pow` | `Claim42/Bounds.lean:81` | 122: CHECKED_PASS |
| `Internal.binomial_ratio_quarter` | `Claim42/Bounds.lean:131` | 123: CHECKED_PASS |
| `Internal.smallset_bucket_tail_quarter` | `Claim42/Bounds.lean:159` | 124: CHECKED_PASS |
| `Internal.capacity_bucket_tail_quarter` | `Claim42/Bounds.lean:195` | 125: CHECKED_PASS |
| `Internal.cond1_single_le_quarter` | `Claim42/Conditions.lean:48` | 126: CHECKED_PASS |
| `Internal.cond1_repetitions_fixed_index` | `Claim42/Conditions.lean:83` | 127: CHECKED_PASS |
| `Internal.cond1_all_fixed_index` | `Claim42/Conditions.lean:114` | 128: CHECKED_PASS |
| `Internal.cond1_all_joint` | `Claim42/Conditions.lean:141` | 129: CHECKED_PASS |
| `Internal.cond3_joint_le_quarter_pow` | `Claim42/Conditions.lean:161` | 131: CHECKED_PASS |
| `Internal.cond2_sparse_joint_le_quarter_pow` | `Claim42/Conditions.lean:193` | 132: CHECKED_PASS |
| `Params.jointLaw_prob_eq_uprob` | `Claim42/Defs.lean:96` | 130: CHECKED_PASS |
| `Internal.lpnNoise_law_cast` | `LPN.lean:120` | 134: CHECKED_PASS |

## Module organization and frozen interface preservation

The approved split moves fourteen existing declarations out of Claim42.lean,
preserving their FQNs, statement headers and pre-sketch prose. Claim42.lean keeps
the frozen `Params.claim42` statement as the public facade. The fifteen-row move
ledger includes that stationary claim as well as the fourteen actual moves.

| Module | Role and dependencies |
| --- | --- |
| Claim42/Load | Existing finite binomial and placement bounds |
| Claim42/Defs | Cond1/Cond2/Cond3, joint law/error definitions and readers; locality/Markov bounds; shared joint-law probability reader |
| Claim42/Bounds | Rounded bucket and numerical tail bounds; imports Defs and Load |
| Claim42/Conditions | Fixed-index/repetition/placement bounds and decomposition; imports Bounds and the precise existing Correctness module |
| Claim42 | Public claim42 body and facade imports |

Correctness depends on Samplers, so the additional owned import is acyclic.
The split introduces no new external Mathlib import root. This is a source
organization decision authorized by root's best judgment while preserving frozen
mathematical interfaces. The five Claim42 files measure 102 facade, 307 Defs, 236 Bounds, 368 Conditions and
212 Load lines, respectively; every line has width ≤ 96. The full static refresh passes. No file exceeds 1,000 lines; the split adds only
owned imports and no new external Mathlib root.

The former per-file decls2 output legitimately contains paired REMOVED/ADDED rows
for the fourteen moves. Those rows are retained, not discarded. The new global
freeze guard rejects duplicate FQNs, compares every frozen kind/normalized header
and statement-prose prefix before `**Proof sketch.**`, and reconciles each move
against the explicit ledger with unchanged headers. New entries are separately
reported theorem/lemma helpers. Full frozen kernel-expression types are a separate
required final check, including generated public fields/constructors.

Root's proof-complete global guard PASS is archived in
`evidence/checks/m3-final-v2/global-freeze/`. All 26 captured source hashes
match the current proof-complete files; 670 frozen headers/prose prefixes are
preserved, fourteen moves are exact and twenty added helpers are separately
reported. The fresh static pass rebinds current source bytes to committed HEAD in
`evidence/checks/m3-final-v2/sizes-widths.json`. All twenty helper axioms are
standard-only in the fresh selected probe; full generated kernel types remain a
separate final gate.

## Current local checks and final-gate limits

| Check | Current M3 result and evidence |
| --- | --- |
| Exact-owner compilation | All 26 expected owners, including both facades, pass with rc0 and zero errors in both forms. Every current source/log/object SHA matches; every record identifies 04249b8. `evidence/build/M3/all-owners-v2/`. |
| Lean warnings | Exactly 32 expected warnings for the remaining frozen later-stage sorry bodies; zero other warnings. All twelve previous linter warnings were removed by eight proof-only edits in four prior owners. `evidence/checks/m3-final-v2/lean-warning-summary.json`. |
| Saved proof steps | All 134 `evidence/steps/001–134/step.json` records are CHECKED_PASS: 114 original bodies and 20 new helpers. Failed attempts/repairs remain archived; they are not counted as additional passes. |
| Selected theorem axioms | All 335 selected source public theorems in 17 completed owners use only propext, Classical.choice, Quot.sound (or subsets). This includes all ten M3 originals and all twenty cumulative helpers. Fresh `evidence/checkpoints/M3/axiom-summary-v2.json` binds both probe logs. |
| Headline axioms | Fresh 19 prints: six standard-only (`Params.claim42`, `Params.G4_eval_eq`, `jls_hasComplexity`, `jls_hasPolyStretch`, `lpnNoise_law`, `PrimeSchedule.nonempty`); thirteen later headlines retain sorryAx. Exact sets are listed below. |
| Source declarations and frozen interface | Base→HEAD 690 ADDED only, no CHANGED/REMOVED; 670 frozen global headers/prose prefixes unchanged, 14 exact ledgered moves, 20 added helpers. `evidence/checks/m3-final-v2/` retains per-file relocation rows and the global guard. |
| Style/campaign | Style, sk15 and widths pass; zero new individual campaign FAIL/WARN against the pinned base. Campaign rc1 is baseline-only. The unchanged 15-line hasComplexityEff_iff lexical sk15 false positive and prior triage remain retained. |
| Sizes/names | 26 files, 8,672 lines; largest 801, maximum width 100. Clash scan: 690 OK, zero CLASH/DUP-NEW/MODIFIED. |
| Phase A/PDF boundary | Current scan has no forbidden import, new realization/contract variant, forbidden enumeration or PDF path; only the designated sampler-contract imports. `evidence/checks/m3-final-v2/boundary.json`. Full all-intermediate-commit PDF verification remains a packaging check. |
| Overlap/reuse | 24 public-only full/core exact/apply pairs plus one separate actual-reader pair with target absent from the pre-search owner; all 50 source/log bindings retained. Closed normalization controls are public reuse, partial/inconclusive outputs are not proofs. |
| Focused noise opacity | V3 passes after the full repaired build with only lpnNoise locally opaque; zero errors/warnings. Old v1 failure is retained. This is a single-definition diagnostic, not a canonical seal. |
| Tagged wrapper history | Fresh 19:21:31UTC audit: 1,273 acquisitions, maximum two because the exact historical violation remains recorded; 504 post-correction acquisitions have maximum one, seriality true, zero active wrappers. `evidence/host/M3-final-v2/`. |

The current build, static, probe and slot records were read and hash-checked during
report preparation. Probe stdout's raw substring count is not a diagnostic count:
the completed probe has one occurrence in an identifier, but zero actual error
forms and rc0. No full-graph or canonical seal completion is inferred from these
selected source public-theorem probes.

M0's full stored-constant census, typed dump, dependency graph and four-variant
Rule10 matrix remain **historical M0 evidence until the final fresh gates**.
At M0 there were 22 owners, 88 seals plus 96 controls, 1036 stored constants,
948 public kernel types and 511 theorem prints. These are neither current M3
counts nor M3 proof passes. M1/M2 selected theorem prints likewise retain their
published limited scopes; no transitive sorryAx-dependent number is inferred by
subtracting filled source holes.

Root's final audit must discover all current owners, including Basic and the new
Claim42 modules (and any later LPN splits), before generating seals/census/controls.
The prepared V2 audit adapters derive exact owners from base→committed HEAD,
require owner×four complete seals and all paired reader controls, retain full
conservative closures/request/runtime/EOF guards, bind source/log/object/import
environments, and support an empty final obligations TSV. They are **untested
candidates**, not gate results. Only the unchanged-byte global freeze tool has a
root-reported execution result. Final source/helper overlap admission remains a
separate required record.

## Opacity repair and proof-only cleanup

The c767ee8 report and checks were held before publication after the focused
single-definition diagnostic failed: making the foreign `lpnNoise` opaque exposed
an implicit cast normalization in `Params.badSet_expect_le`. The old proof used
`cast_eq` on a stored coin-type equality whose reduction depended on that foreign
definition. The failure is retained in `evidence/meta/M3-focused-noise-opacity/`
and its old source/probe hashes. The pre-repair c767ee8 checkpoint artifacts remain
historical under `evidence/checkpoints/M3/pre-opacity-repair-c767ee8/`.

The fourth M3 commit adds only the theorem
`Internal.lpnNoise_law_cast` in LPN.lean. Its literal statement includes the cast
from the explicit selector/residue product into the noise's stored coin type.
The noise owner composes the already proved `lpnNoise_law` with public `cast_eq` from Lean core;
foreign consumers now use the published cast-indexed law rather than normalize
that foreign definition. No frozen theorem statement, encoding, algorithm,
parameter, import or assumption was changed. The updated consumer and affected
owners passed, then all 26 repaired owners were freshly rebuilt.

After that full build, the final focused probe
`evidence/probes/M3_FocusedNoiseOpacityV3.lean` copied the current Claim42/Defs
body under a **local irreducible lpnNoise only**. It passed rc0, zero errors and
warnings at the exact current consumer source hash. `focused-v3-binding.json` and
the third run in `evidence/meta/M3-final-v2/results.jsonl` bind its source/log.
This is a focused single-definition diagnostic, **not** a canonical full-closure
Rule10 seal. The historical v1 failure is not counted as a pass or erased.

The same commit applies eight proof-only warning cleanups in LPN, Degree,
Correctness and Stretch. The stored W01–W08 JSON records and before/after snapshots
under `evidence/warning-cleanup/` retain the exact hunks. Unused simp arguments and
a lambda binder were removed/renamed, redundant case equation labels removed,
two unnecessary focused-sequence operators replaced by ordinary sequencing, and
two dead ring suffixes deleted. Each proof-body edit was applied in a separate
tool invocation; combined final owner checks are recorded, not invented individual
compile claims. These four prior owners are therefore **changed from M2**.
Their frozen headers and pre-sketch prose remain byte-equivalent under the global
guard. No linter option or attribute was changed/disabled. The fresh v2 full build
has exactly 32 remaining-sorry warnings and zero other warnings.

## Overlap and public API reuse

The name/shape logs remain under `evidence/overlap/M3-Load-name-shape/`,
`M3-Claim42-name-shape/` and the joint-law/noise-reader search records. Twenty-four
public-only full/core goal pairs now have 48 exact?/apply? runs under
`evidence/overlap/probes/M3Load_*/`; their archived imports exclude StructuredSeed.
The added cast-normalization **control** closes by the existing `cast_eq` from Lean core.
This motivates composing that API in the noise owner; it is not evidence that
the actual opaque-noise reader statement was already available publicly.

A separate actual-reader exact/apply pair under
`evidence/overlap/probes/M3NoiseActual_lpnNoise_law_cast/` imports the preexisting
owned noise algorithm/law with lpnNoise opaque. The target reader was absent from
the bound source before both searches, so it cannot match itself. Both outcomes
are recorded INCONCLUSIVE_FINITE_SEARCH; they establish no global absence claim.
This is distinct from the public-only normalization control. In total 50 current
search source/log hashes were checked across those25 pairs.

The original errProb_nonneg core closes by public
`Games.ProbComp.prob_nonneg`; its frozen named wrapper composes that fact with the
published reader. Other partial/diagnostic outputs are not theorem proofs. The
original invalid prefactor harness attempt remains retained and superseded by its
fresh namespace-correct v2 pair. Specialized sampler/record goals are explicitly
mathematical cores, not claims that a complete source statement was searched under
all its own definitions. Actual saved source bodies, fresh 26-owner compilation
and 335 standard-only selected theorem prints supply the proof evidence.

The specialized helpers compose public finite expectation/product, Markov,
binomial/factorial, power-order and polynomial/exponential growth APIs. The two
new semantic readers centralize their concrete joint-law/cast transports; no
copied generic identity, local contract variant, machine, fair-coin sampler or
algorithm construction is introduced. Complete conservative Rule10 closures,
all controls and runtime masks/EOF coverage remain final fresh gates.

## Statement changes and deviations from the design note

### Frozen quantifiers, targets and earlier judgments

SP-W1 uses rational δ with real analytic coercions. SP-W2 asserts only the two
semantic acceptance equalities needed by the hybrid bridge, not equality of
free-oracle programs with an extra unused query. SP-W3 requires growing seed size
as well as the polynomial output bound; M2 proved both for the construction.
The public prime remains an input and all constructions accept every schedule.
Canonical LPN and Boolean assumption challenge encodings remain unchanged.

Rule15 primitive evaluator and exact-draw sampler efficiency fields remain
mandatory. Target witnesses are selected before every applicable size, schedule,
prime or input. In particular, T6 chooses one shared sampler witness before all
prime schedules; it is not a family of separately selected witnesses after π.
T1/T3/T5/T6 will fill the respective primitive fields only conditionally on the
unproved target propositions. No Phase B machine/sampler/efficiency construction
is introduced here. M4's advice-family-before-all-realisers/all-κ requirements and
M5's fixed shared subexponential exponent remain the frozen later obligations.

The four historical mathematical tables below retain the complete earlier
fidelity/deviation, Rule15 field, target-selection and nonvacuity detail. Their
historical line references are not altered to pretend they are current anchors.
The separate source-04249b8 appendix follows declaration identity and handles moved
Claim42 declarations explicitly.

## Frozen fidelity, Rule15 and non-vacuity tables

All four mathematical tables below are byte-exact M0 snapshots. Their line numbers
are **historical M0 anchors**; current committed-source anchors are indexed separately.

### Archived M0 fidelity table

| Paper item / page | Lean names and locations | Fidelity and deviations |
| --- | --- | --- |
| Multilinear representation, §2 p.8; efficient polynomial descriptions, Def.3.3 p.10 | `PolyTerms` (`PolyTerms.lean:45`); `PolyTerms.denote` (`PolyTerms.lean:56`); `PolyTerms.encTerms` (`PolyTerms.lean:85`) | Explicit finite term lists with repeated variable occurrences encode powers. Coefficients and finite coordinates have faithful sign/numeral encodings. `BoolCircuit.encodeList` and `pairEncode` delimit terms. This is a disclosed representation choice for T2, not a new polynomial semantics. |
| Scalar noise; Def.2.3, pp.9-10 | `lpnNoise` (`LPN.lean:49`); `lpnNoise_law` (`LPN.lean:67`) | One exact selector/residue draw gives `(1-1/W) delta_0 + (1/W) Uniform(ZMod p)`. Triggered noise may also be zero. Dv3 fixes the exact rounded rate. |
| LPN family and assumption; Def.2.3, pp.9-10 | `LPNFamily.Raw` (`LPN.lean:79`); `LPNFamily.Raw.toLWE` (`LPN.lean:136`); `LPNFamily.Raw.adv` (`LPN.lean:166`); `LPNFamily.Raw.Assumption` (`LPN.lean:175`) | Canonical `LWE.Parameters`, `LWE.Noise`, `LWE.Family`, `advantageAt`, and `DLWEAssumption` are reused. Dv3 assumes the construction's own l-indexed family, with transposed row/sample convention and canonical challenge encoding; no literal Def.2.3 bridge is claimed. |
| Honest LPN sampling; Def.2.3, pp.9-10 | `LPNFamily.Raw.Draw` (`LPN.lean:189`); `LPNFamily.Raw.sampleCore` (`LPN.lean:306`); `LPNFamily.Raw.sampleLaw` (`LPN.lean:317`); `LPNFamily` (`LPN.lean:400`) | One finite product draw includes the matrix, common secret, and all scalar noise seeds. `LPNFamily` adds mandatory shared `SamplesEfficiently`; Raw does not claim efficiency. Dv17/Dv18. Explicit draw coordinates are composition data, with no chosen enumeration. |
| Boolean PRG; Def.3.4, p.11 | `BoolPRG` (`BoolPRG.lean:50`); `BoolPRG.idSamp` (`BoolPRG.lean:124`); `BoolPRG.game` (`BoolPRG.lean:162`); `BoolPRG.Secure` (`BoolPRG.lean:191`); `BoolPRG.SubexpSecure` (`BoolPRG.lean:199`); `BoolPRG.HasStretch` (`BoolPRG.lean:207`) | Evaluation and exact index-core sampling both carry uniform efficiency fields. Every assumption quantifies NUPPT adversaries. Dv5 uses the settled pointwise stretch lower bound rather than an exact real-power output length; Dv13 uses the shared subexponential-advantage notion. |
| Multilinear degree and locality; Def.3.4, p.11 | `BoolPRG.MultilinearRep` (`BoolPRG.lean:217`); `BoolPRG.MultilinearRep.HasLocality` (`BoolPRG.lean:234`); `BoolPRG.MultilinearRep.TermsEfficient` (`BoolPRG.lean:245`) | Integer multilinear polynomials have degree <=d and equal output bits on Boolean inputs. Dv4 measures locality on the supplied representation at every index. Term-generation efficiency is a Phase B hypothesis, not proved here. Faithful input encoding and explicit finite-coordinate data are disclosed pre-M0 refinements. |
| sPRG syntax; Def.3.1, p.10 | `SPRG.Raw` (`Defs.lean:97`); `SPRG.Raw.idSamp` (`Defs.lean:179`); `SPRG.Raw.sdSamp` (`Defs.lean:188`); `SPRG` (`Defs.lean:397`) | Exact samplers are deterministic cores applied to one uniform complete draw. Raw stores the algorithms; the primitive adds evaluator and two shared sampler efficiency fields. Dv2 finite modular seed vectors; Dv9 modulus schedule; Dv15 explicit coordinates; Dv17/Dv18. |
| Security; Def.3.2, p.10 | `SPRG.Raw.challengeStr` (`Defs.lean:218`); `SPRG.Raw.game` (`Defs.lean:234`); `SPRG.Raw.adv` (`Defs.lean:251`); `SPRG.Raw.Secure` (`Defs.lean:260`); `SPRG.Raw.SubexpSecure` (`Defs.lean:267`) | Challenges publish prime, index, public seed, and real or uniform output. Dv9/Dv13/Dv18. Primitive property wrappers read the raw bundle through proved readers. |
| Complexity; Def.3.3, p.10 | `pubDegree` (`Degree.lean:45`); `privDegree` (`Degree.lean:56`); `SPRG.Raw.HasComplexity` (`Defs.lean:298`); `SPRG.Raw.HasComplexityEff` (`Defs.lean:352`) | Dv6 specializes to the composite output polynomial with separate public/private bounds. Efficient complexity uses one uniform map that outputs explicit term lists for actual polynomials. Dv10 takes public degree d from p.17, not the overview's d+1 wording on p.14. |
| Prime field / parameter convention; Def.2.3 pp.9-10 and §4 p.15 | `PrimeParam` (`Defs.lean:48`); `PrimeSchedule` (`Defs.lean:72`); `PrimeSchedule.nonempty` (`Defs.lean:82`) | Public p satisfies `2^kappa <= p <= 2^(kappa+1)` and primality. Params stores no prime. Dv9 accepts every schedule, with the prime supplied as input. Bertrand is used only for non-vacuity; no prime algorithm is defined. |
| Construction dimensions and rounding; §4 p.15 | `Params` (`Params.lean:50`); `Params.D` (`Params.lean:64`); `Params.ℓ` (`Params.lean:70`); `Params.n` (`Params.lean:76`); `Params.m` (`Params.lean:83`); `Params.noiseWidth` (`Params.lean:90`); `Params.W` (`Params.lean:111`); `Params.t` (`Params.lean:120`); `Params.rc` (`Params.lean:126`); `Params.cap` (`Params.lean:132`); `Params.B` (`Params.lean:138`); `Params.Γ` (`Params.lean:146`) | Dv1 one parameter and exact power schedules; Dv3 integer floors/ceilings with positive bucket/noise widths; Dv5 output stretch lower bound; Dv11 positive degree. SP-W1 stores rational delta and coerces it to real for analysis. Gamma uses integer base-two log and integer division. |
| Reindexing assumption dimensions; Remark2.1 p.9 | `Params.kappaOf` (`Params.lean:155`); `Params.kappaOfN` (`Params.lean:164`); `Params.kappaOf_pow` (`Params.lean:305`); `Params.kappaOfN_n` (`Params.lean:315`); `Params.lpnFamily_raw` (`Params.lean:339`) | Bounded greatest searches invert the fixed power schedules, with inverse <=identity and exact on-image equations. Dv1/Dv3 define the own l-indexed LPN family; arbitrary public prime schedule is read at the inverse parameter. |
| Public/private seed layout; SdSamp', pp.15-16 | `Params.Pub` (`Params.lean:247`); `Params.Priv` (`Params.lean:201`); `Params.SVar` (`Params.lean:180`); `Params.pubLen` (`Params.lean:173`); `Params.privLen` (`Params.lean:209`); `Params.pubEquiv` (`Params.lean:255`); `Params.privEquiv` (`Params.lean:232`) | Public seed contains kappa public vectors and error; private seed contains per-instance flag, data, and precomputed flag*data. Dv2 counts residue coordinates before fixed-width bits; Dv15 explicit Fin equivalences replace implicit enumeration. |
| Bucket placement; IdSamp', p.15 | `Buckets.bucket` (`Buckets.lean:52`); `Buckets.load` (`Buckets.lean:61`); `Buckets.rank` (`Buckets.lean:77`); `Buckets.indexMap` (`Buckets.lean:87`); `Buckets.bucketMatrix` (`Buckets.lean:147`) | Increasing ranks give deterministic injective positions. Pre-M0 refinement uses `Option (Fin rc x Fin rc)` and `none` on overfull/empty grids: at kappa=0 the required grid is empty, so a total default point cannot exist. All successful placements/capacity conventions are preserved. Matrix coordinates sum matching corrections without a choice. |
| Sparse correction factors; 1SdSamp, p.16 | `sparseEntries` (`SparseFactor.lean:48`); `sparseLeft` (`SparseFactor.lean:61`); `sparseRight` (`SparseFactor.lean:76`); `sparseFactor` (`SparseFactor.lean:91`); `sparseFactor_mul_of_card_le` (`SparseFactor.lean:146`) | Deterministic row-major nonzero listing fixes the paper's unspecified factor choice. One stored entry per factor slot reconstructs a matrix with <=t nonzeros. Total over semirings, zero padding, no rank theorem or classical enumeration. |
| Finite coordinates and encodings; §4 pp.15-17 | `Params.IdDraw` (`Encoding.lean:135`); `Params.Draw` (`Encoding.lean:147`); `Params.Seed` (`Encoding.lean:160`); `Params.idxEquiv` (`Encoding.lean:196`); `Params.idDrawEquiv` (`Encoding.lean:214`); `Params.drawEquiv` (`Encoding.lean:232`); `Params.encIdx'` (`Encoding.lean:263`); `Params.encIdDraw` (`Encoding.lean:275`); `Params.encDraw` (`Encoding.lean:308`); `Params.encSeed'` (`Encoding.lean:320`) | Dv15/Dv17 use supplied Boolean coordinates and canonical residue/function/product equivalences. Named injectivity obligations retain every field. Encoding is split into its own module, a disclosed modular refinement. No `Fintype.equivFin` or chosen enumeration. |
| Explicit polynomial size bounds; §4 p.15 and Claim4.1 p.18 | `Params.ellBound` (`Encoding.lean:331`); `Params.nBound` (`Encoding.lean:337`); `Params.mBound` (`Encoding.lean:343`); `Params.bucketBound` (`Encoding.lean:349`); `Params.rcBound` (`Encoding.lean:356`); `Params.sVarBound` (`Encoding.lean:371`); `Params.seedBound` (`Encoding.lean:382`); `Params.idxBound` (`Encoding.lean:392`) | Syntactic `PolyExpr` values bound every concrete size and code. Bucket numerals use numeric B bits (generous but polynomial); noise selectors use ell+1 bits; residues use kappa+1 bits. All bounds include kappa=0. |
| Equation(3), G(1), p.17 | `Params.linearCoeff` (`Polys.lean:146`); `Params.halfForm` (`Polys.lean:169`); `Params.prgPoly` (`Polys.lean:189`); `Params.G1` (`Polys.lean:229`); `Params.G1_eval` (`Polys.lean:371`) | Sorted monomial supports are padded with constants, split at D, and tensor-expanded. Dv3 transposes the public LPN matrix; Dv4 uses supplied multilinear representation; Dv15 uses explicit output-coordinate casts. |
| Equation(3), G(2), p.17 | `Params.correctionPoly` (`Polys.lean:208`); `Params.G2` (`Polys.lean:241`) | UV correction terms add the discrepancy between Boolean evaluation and noisy-input polynomial evaluation at the bucket position. Optional absent positions contribute zero, including the empty-grid boundary. |
| Equation(4), G(3), p.17 | `Params.G3` (`Polys.lean:253`); `Params.G3_eval_of_scaled` (`Polys.lean:389`) | One tensor half and U use the precomputed scaled copy; the other half and V are unscaled. This realizes flag*G2 while keeping private degree <=2. Dv6/Dv10/Dv15. |
| G(4), p.16; degree calculation p.17 | `Params.G4struct` (`Polys.lean:265`); `Params.G4` (`Polys.lean:277`); `Params.G4_degrees` (`Polys.lean:343`) | Sum G3 over repetitions and explicitly rename structured coordinates to Fin public/private coordinates. No public error multiplier is introduced. Dv10 gives degree d in public variables and two in private variables. |
| 1SdSamp, p.16 | `Params.noiseValue` (`Samplers.lean:45`); `Params.errSet` (`Samplers.lean:58`); `Params.badSet` (`Samplers.lean:69`); `Params.oneFlag` (`Samplers.lean:82`); `Params.corr` (`Samplers.lean:97`); `Params.lpnVector` (`Samplers.lean:116`); `Params.oneSd` (`Samplers.lean:140`) | Exact noise, representation-dependent BAD, all three success conditions, A*s+e+sigma, and deterministic sparse correction factors follow the algorithm. Dv3 rounded thresholds/transposed matrix; Dv4 locality; Dv15 finite layout. |
| SdSamp', pp.15-16 | `Params.firstGood` (`Samplers.lean:186`); `Params.packSeed` (`Samplers.lean:196`); `Params.sdCore` (`Samplers.lean:236`); `Params.sdSampFull` (`Samplers.lean:292`); `Params.sdSamp'` (`Samplers.lean:302`) | First successful repetition has selected flag one; others zero. Private seed stores flags and scaled/unscaled copies; error is true exactly if no repetition succeeds. All output data comes from one exact joint draw. Dv15/Dv17. Empty repetition families at kappa=0 are total. |
| IdSamp' and Eval', pp.15-17 | `Params.idCore` (`Samplers.lean:274`); `Params.idSamp'` (`Samplers.lean:283`); `Params.eval'` (`Samplers.lean:313`); `jlsSPRG_raw` (`Samplers.lean:353`) | Exact index draw contains underlying generator index draw, independent buckets, and public matrix. Eval' evaluates G4 and recognizes the field value one; correctness proves this is Boolean on sampled seeds. Raw publishes the fixed arbitrary modulus schedule. Dv8/Dv9/Dv17/Dv18. |
| Correctness, Equations(3)-(4), pp.16-17 | `Params.firstGood_none_iff` (`Correctness.lean:56`); `Params.oneSd_factors_mul` (`Correctness.lean:154`); `Params.G1_eval_of_good` (`Correctness.lean:171`); `Params.G2_eval_of_flag` (`Correctness.lean:201`); `Params.G4_eval_sdCore` (`Correctness.lean:219`); `Params.G4_eval_eq` (`Correctness.lean:232`); `Params.eval'_correct` (`Correctness.lean:244`); `jls_hasComplexity` (`Correctness.lean:259`) | Specialized reader glue proves good-output correction, sparse reconstruction, unique selected flags, packed coordinates, and exact sampled-seed correctness. All pp and all kappa, including zero. Dv3/Dv4/Dv6/Dv10/Dv15/Dv17/Dv18. |
| Claim4.1, p.18 | `E0` (`Stretch.lean:51`); `Params.seedBitsAt` (`Stretch.lean:64`); `Params.seedBitsAt_le` (`Stretch.lean:82`); `jls_seedBits_le` (`Stretch.lean:103`); `jls_hasPolyStretch` (`Stretch.lean:122`) | Explicit sufficient threshold `floor(max(10/delta,5/(tau-1)))+1`; uniform fifth-power payload estimate and eventual power stretch. Dv1/Dv3/Dv5/Dv18; SP-W1 rational delta. The estimate is uniform in all pp because lengths depend only on kappa. |
| Claim4.2, pp.19-21 | `Params.Cond1` (`Claim42.lean:45`); `Params.Cond2` (`Claim42.lean:58`); `Params.Cond3` (`Claim42.lean:73`); `Params.errProb` (`Claim42.lean:93`); `Params.badSet_expect_le` (`Claim42.lean:114`); `Params.cond1_prob_le` (`Claim42.lean:126`); `Params.errProb_le_decomposition` (`Claim42.lean:139`); `Params.claim42` (`Claim42.lean:155`) | Exact error probability at every pp/kappa, strict integer Markov denominator Gamma+1, shared capacity failure, conditional-noise independence, and common eventual threshold before forall pp. Dv3/Dv7. No false unconditional independence of index-dependent events is asserted. |
| Bucket tail estimates used in Claim4.2, p.20 | `Internal.binomial_bound` (`Claim42/Load.lean:54`); `Internal.bucket_tail` (`Claim42/Load.lean:67`); `Internal.some_bucket_tail` (`Claim42/Load.lean:78`); `Internal.full_bucket_tail` (`Claim42/Load.lean:88`); `Internal.some_full_bucket_tail` (`Claim42/Load.lean:98`) | Fixed bad set independent of uniform buckets. Load >t uses the exact stronger t+1 witness bound, handles t=0, assumes B nonzero. Existing public union-bound APIs and factorial/exponential facts are reused; no generic probability calculus is copied. |
| H0-H3 / Proposition4.1, pp.18-19 | `HybridStage` (`Hybrids.lean:43`); `Params.publicSeed` (`Hybrids.lean:53`); `Params.hyb` (`Hybrids.lean:112`); `Params.hyb_real_eq_raw` (`Hybrids.lean:142`); `Params.hyb_random_eq_raw` (`Hybrids.lean:148`); `Params.hyb_real_prg_le` (`Hybrids.lean:176`); `Params.hyb_uniform_random_le` (`Hybrids.lean:184`) | Same exact index/seed laws; H1/H2 clean the error flag, H1 uses G(sigma), H2/H3 use uniform tail. Each statistical step costs exact errProb. Dv7/Dv8/Dv18. |
| Semantic chain-start correspondence; Lemma4.2, p.19 | `Params.hyb_prg_accept_eq_chain_zero` (`Hybrids.lean:157`); `Params.hyb_uniform_accept_eq_chain_zero` (`Hybrids.lean:167`) | SP-W2 replaces the two false equalities of free oracle programs by equalities of acceptance probabilities. At chain index zero, an extra uniform public-vector query is unused; it changes the query tree while leaving acceptance unchanged. The probability-level statements suffice through advantage_eq. No algorithm or headline inequality changes. |
| Di chain / Lemma4.2, p.19 | `Params.chainPublic` (`Hybrids.lean:69`); `Params.chainGame` (`Hybrids.lean:86`); `lemma42` (`Security.lean:62`) | First i public LPN vectors become uniform; both real and uniform tails are represented. The direct endpoint lemma costs kappa LPN and one PRG advantage. Dv8 retains independent published buckets; Dv12 hardwires averages; Dv14 every-realiser typed statement. |
| LPN hops / Lemma4.2, p.19 | `Params.LPNChal` (`Reductions/LPN.lean:51`); `Params.lpnEnc` (`Reductions/LPN.lean:68`); `Params.LPNAdvice` (`Reductions/LPN.lean:135`); `Params.encLPNAdvice` (`Reductions/LPN.lean:243`); `Params.lpnPre` (`Reductions/LPN.lean:321`); `Params.lpnRed` (`Reductions/LPN.lean:353`); `Params.lpn_hop` (`Reductions/LPN.lean:398`) | Exact canonical LWE challenge remains unaltered. Advice fixes hop/index/buckets/draw/tail/uniforms, with inhabited sentinel at zero; matrix stays challenge-supplied. Deterministic guarded preprocessing calls A with required coin prefix. One advice family before every realiser/all kappa. Dv3/Dv8/Dv9/Dv12/Dv14/Dv15/Dv16. Coarse explicit advice-bound coefficient 4096 is disclosed. |
| PRG hop / Lemma4.2, p.19 | `Params.PRGChal` (`Reductions/PRG.lean:54`); `Params.prgEnc` (`Reductions/PRG.lean:83`); `Params.PRGAdvice` (`Reductions/PRG.lean:93`); `Params.encPRGAdvice` (`Reductions/PRG.lean:206`); `Params.prgPre` (`Reductions/PRG.lean:248`); `Params.prgRed` (`Reductions/PRG.lean:271`); `Params.prg_hop` (`Reductions/PRG.lean:338`) | Canonical G challenge; advice fixes buckets/matrix/uniform vectors, retaining challenged Boolean index/output. Guarded preprocessing neither samples nor calls G.eval. All-zero advice inhabits every parameter. Bound coefficient 100 is explicit. Dv8/Dv9/Dv12/Dv14/Dv15/Dv16. |
| Proposition4.1, pp.18-19 | `prop41` (`Security.lean:84`) | For each P/pi/A, exists advice families, then forall BL/BG realisers, then forall kappa: `adv <=2*kappa*ownLPNadv(ell)+Gadv(n)+2*errProb`. Dv12 selects a largest LPN gap among both chains; Dv16 shared layout-length predicate is weaker, so the universal-realiser bound is stronger. |
| Theorem4.1, p.11; security consequence p.18 | `jls_secure` (`Security.lean:102`); `jls_subexpSmall` (`Security.lean:115`); `jls_subexpSecure` (`Security.lean:129`); `theorem41` (`Security.lean:141`); `theorem41_subexp` (`Security.lean:153`) | Raw results assume realisability and own-family LPN. Fixed exponent is `min(E*cL,min(E*D*cG,1))/2`, with positive common assumption exponents before all NUPPT. Dv3/Dv13/Dv14/Dv18. Degree d/2 and stretch match the settled statement. |
| Theorem4.1 existence, p.11 | `exists_sprg_raw` (`Security.lean:167`); `exists_sprg_raw_subexp` (`Security.lean:184`) | Choose sufficiently large E from the supplied G/R/rational-delta data, for arbitrary supplied prime schedule. LPN and realisability range only over this E-indexed construction family. Dv1/Dv3/Dv13/Dv14/Dv18; SP-W1. Narrowing raw realisability to these Params is explicitly disclosed. |
| Phase B honest efficiency targets, Defs.3.1-3.3 p.10 / construction pp.15-17 | `Params.evalTarget` (`Targets.lean:72`); `Params.qGenTarget` (`Targets.lean:91`); `Params.coreTarget` (`Targets.lean:116`); `Params.drawSamplerTarget` (`Targets.lean:179`); `Params.lpnSamplerTarget` (`Targets.lean:197`); `Params.Targets` (`Targets.lean:216`) | T1/T2 each choose one map before all kappa/pp. T3 and T5 are shared halves on the same complete draw. T6 chooses one U/c/f before all dimensions and prime schedules. Dv17/Dv18. Targets are named Props with proved readers and the explicit unproved-Phase-B notice; no target truth is asserted. |
| Phase B reduction target / Lemma4.2 p.19 | `Params.lpnPreTarget` (`Targets.lean:139`); `Params.prgPreTarget` (`Targets.lean:154`); `Params.LPNRealizable` (`Reductions/LPN.lean:413`); `Params.PRGRealizable` (`Reductions/PRG.lean:288`); `Params.Realizable` (`Security.lean:45`); `Params.realizable_of_targets` (`Targets.lean:232`) | One preprocessing map precedes all schedules/advice/challenges. Shared RealizesOn is reused unchanged. Its public preTarget theorem supplies realisers conditionally on T4; no machine is constructed. Dv14/Dv16. |
| Primitive assembly / conditional Theorem4.1 | `Params.lpnFamily` (`Targets.lean:279`); `jlsSPRG` (`Targets.lean:301`); `Params.hasComplexityEff_of_target` (`Targets.lean:293`); `theorem41_of_targets` (`Targets.lean:319`); `exists_sprg_of_targets` (`Targets.lean:333`); `exists_sprg_of_targets_subexp` (`Targets.lean:349`) | T1, T3+T5, and T6 fill all mandatory fields; T2 supplies actual polynomial generation. Only these target assemblies construct new SPRG/LPNFamily values. Efficient existence keeps `forall P, P.Targets`; raw existence uses its own E-indexed realisability. Dv18. |

### Archived M0 rule15 table

| Primitive / algorithm layer | Exact uniform efficiency fields | Raw layer and actual sampler law | Construction from targets |
| --- | --- | --- | --- |
| `BoolPRG` (`BoolPRG.lean:50`) | `eval_eff` (`:94`) chooses one `PolyTimeComputable` string map before all `n`, indices, and Boolean seeds. `idSamp_eff` (`:99`) is the shared `CoinSampling.SamplesEfficiently` contract for its supplied `IdDraw`, `encIdDraw`, `encIdx`, and `idCore`. | The input primitive itself carries the algorithm data. `BoolPRG.idSamp` (`:124`) is exactly the pushforward of one uniform `IdDraw` through `idCore`, with proved reader `idSamp_eq` (`:128`). It is not a disconnected arbitrary sampler field. | This job assumes a `BoolPRG`; it constructs no new value of that type. Its evaluator and sampler witnesses are mandatory input data. |
| `LPNFamily` (`LPN.lean:400`) | `sample_eff` (`:402`) is shared `SamplesEfficiently` for the exact joint matrix/secret/noise draw, parameter word `sampleWord`, draw/output encodings, and `sampleCore`. | `LPNFamily.Raw` (`:79`) fixes samples, public modulus, exact noise denominator, polynomial bounds, canonical `toLWE` (`:136`), `adv` (`:166`), and `Assumption` (`:175`). Its complete draw is `Raw.Draw` (`:189`), its actual core is `sampleCore` (`:306`), and `sampleLaw` (`:317`) is the exact one-draw pushforward. | `Params.lpnFamily` (`Targets.lean:279`) extends `P.lpnFamily_raw pi` with the field furnished by `lpnSamplerEfficient_of_target` (`:269`), from T6. `lpnFamily_toRaw` (`:285`) is proved `rfl`. |
| `SPRG` (`Defs.lean:397`) | `eval_eff` (`:398`) is `toRaw.EvalEfficient`; `idSamp_eff` (`:399`) and `sdSamp_eff` (`:402`) are shared `SamplesEfficiently` contracts on the exact raw index and seed draws and their cores. | `SPRG.Raw` (`:97`) stores all honest algorithm data, explicit finite-coordinate equivalences, and encodings. `Raw.idSamp` (`:179`) and `Raw.sdSamp` (`:188`) are derived exact uniform-draw pushforwards. `Raw.EvalEfficient` (`:318`) chooses one map before all parameters, with the public modulus in its input. | `jlsSPRG` (`Targets.lean:301`) extends `jlsSPRG_raw P pi`; T1 supplies `eval_eff` via `evalEfficient_of_target` (`:238`), T3 and T5 supply both sampler fields via `idSampEfficient_of_targets` (`:245`) and `sdSampEfficient_of_targets` (`:257`). `jlsSPRG_toRaw` (`:308`) is proved `rfl`. |

### Archived M0 target-selection table

| Field / consequence | Target witness selected |
| --- | --- |
| sPRG `eval_eff` | `hT.1` (T1) |
| sPRG `idSamp_eff`, `sdSamp_eff` | `hT.2.2.1` (T3) and `hT.2.2.2.2.1` (T5) |
| LPN `sample_eff` | `hT.2.2.2.2.2` (T6) |
| `HasComplexityEff P.d 2` | T2, through `hasComplexityEff_of_target` (`Targets.lean:293`) |
| reduction realisers | T4, through `realizable_of_targets` (`Targets.lean:232`) |

### Archived M0 nonvacuity table

| Object | Source witness and finite-coordinate data | Zero/off-image behavior and scope |
| --- | --- | --- |
| `PrimeSchedule` (`Defs.lean:72`) | `PrimeSchedule.nonempty` (`:82`) is proved using existing `Nat.exists_prime_lt_and_le_two_mul`. | At `kappa=0`, `p=2` is admitted by the weak interval endpoints. This is an existence proof, not a prime algorithm. `Classical.choose` occurs only in this non-vacuity proof (`:86`), outside encodings, draw equivalences, preprocessing maps, and targets. |
| `P.LPNAdvice pi L` (`Reductions/LPN.lean:135`) | `instLPNAdviceNonempty` (`:235`) maps the component product through `lpnAdviceProductEquiv.symm`. `lpnAdviceEquiv` (`:197`) gives explicit `Fin (lpnAdviceCard pi L)` coordinates; `instLPNAdviceFintype` (`:226`) transports from them. | The hop component is `Fin (kappaOf L + 1)`, so the sentinel remains nonempty at zero and at independent dimensions off the schedule image. Boolean indices are nonempty by the input `BoolPRG`; bucket/noise widths are positive; function products with empty domains remain nonempty. The hop inequality is required only when its value is below `kappa`. `lpnPre` (`:321`) returns `[]` off image. |
| `P.PRGAdvice pi N` (`Reductions/PRG.lean:93`) | `instPRGAdviceInhabited` (`:187`) supplies all-zero buckets, matrix, and public vectors, using `P.B_pos`. `prgAdviceEquiv` (`:156`) is an explicit coordinate equivalence and `instPRGAdviceFintype` (`:178`) transports finiteness. | Valid for every `N`, including zero and off-image dimensions. No choice is used to obtain the explicit default. `prgPre` (`:248`) returns `[]` off image. |
| Input Boolean indices and index draws | `BoolPRG.idxNonempty` (`BoolPRG.lean:60`) and `idDrawNonempty` (`:70`) are mandatory supplied fields; their instances are at `:105`/`:108`. `idxEquiv` (`:56`) and `idDrawEquiv` (`:66`) are explicit data. | Honest Boolean index sampling never samples an empty type. These hypotheses describe the input primitive rather than an additional construction assumption. |
| Generic sPRG index/index draw/seed draw | `SPRG.Raw.idxNonempty`, `idDrawNonempty`, `sdDrawNonempty` (`Defs.lean:104`, `:109`, `:129`) are mandatory raw data; the public instances are at `:143`, `:145`, `:149`. | Every exact uniform law has a nonempty draw; every raw family includes explicit cardinal/equivalence data (`:105`/`:106`, `:110`/`:111`, `:130`/`:131`). |
| Construction's exact draws | `Params.IdDraw`, `Params.Draw` (`Encoding.lean:135`, `:147`) are concrete finite products; `idDrawEquiv`, `drawEquiv` (`:214`, `:232`) compose supplied Boolean and canonical modular/function/product equivalences. | Empty vector domains at zero do not make the function type empty. Positive bucket/noise widths and nonzero prime modulus provide nonempty codomains. |
| LPN exact joint draw | `LPNFamily.Raw.Draw` (`LPN.lean:189`) is the concrete matrix/secret/noise-seed product. `drawEquiv` (`:278`) gives explicit `Fin (drawCard ell)` coordinates; nonzero modulus and noise denominator instances are at `:101`/`:102`. | It remains nonempty when the secret dimension or sample count is zero. It is one product draw, not an illicit product fair-coin sampler construction. |
| Shared realiser predicate | Existing `Complexity.NUPPT.realizesOn_self` and `realizesOn_self_take` (`TCSlib/Cryptography/Asymptotic/Realization.lean:167`, `:179`) establish generic satisfiability, including the required coin-prefix shape. | These do **not** by themselves realize the actual LPN/PRG preprocessing. Actual reduction realisers are obtained conditionally from T4 by the existing `exists_realizesOn_of_preTarget` (`:220`) through the M0 `realizable_of_targets` obligation. |


## Current M3 v2 source declaration anchors

These locations refer to root-confirmed repaired source
`04249b85e80a007dc5845077a18a365d5150e14b`. Every source/log/object hash was
checked against the fresh 26-owner build and committed-source static inventory.
The complete TSV includes explicit structure fields; LPN field locations were
remapped through exact equal source lines after the new cast reader was inserted.
Generated constructors/recursors/inherited fields remain represented by their
owning structure. This lexical index is not a full typed kernel census.

| Declaration (area prefix omitted) | M3 v2 source anchor |
| --- | --- |
| `BoolPRG` | `BoolPRG.lean:50` |
| `BoolPRG.HasStretch` | `BoolPRG.lean:207` |
| `BoolPRG.IdDraw` | `BoolPRG.lean:62` |
| `BoolPRG.Idx` | `BoolPRG.lean:52` |
| `BoolPRG.MultilinearRep` | `BoolPRG.lean:217` |
| `BoolPRG.MultilinearRep.HasLocality` | `BoolPRG.lean:234` |
| `BoolPRG.MultilinearRep.TermsEfficient` | `BoolPRG.lean:245` |
| `BoolPRG.MultilinearRep.eval_poly` | `BoolPRG.lean:225` |
| `BoolPRG.MultilinearRep.poly` | `BoolPRG.lean:219` |
| `BoolPRG.MultilinearRep.poly_mem_restrictDegree` | `BoolPRG.lean:221` |
| `BoolPRG.MultilinearRep.totalDegree_poly_le` | `BoolPRG.lean:223` |
| `BoolPRG.Secure` | `BoolPRG.lean:191` |
| `BoolPRG.SubexpSecure` | `BoolPRG.lean:199` |
| `BoolPRG.encIdDraw` | `BoolPRG.lean:74` |
| `BoolPRG.encIdDraw_injective` | `BoolPRG.lean:76` |
| `BoolPRG.encIdx` | `BoolPRG.lean:78` |
| `BoolPRG.encIdx_injective` | `BoolPRG.lean:80` |
| `BoolPRG.encIdx_length_le` | `BoolPRG.lean:84` |
| `BoolPRG.eval` | `BoolPRG.lean:92` |
| `BoolPRG.eval_eff` | `BoolPRG.lean:94` |
| `BoolPRG.game` | `BoolPRG.lean:162` |
| `BoolPRG.idCore` | `BoolPRG.lean:72` |
| `BoolPRG.idDrawCard` | `BoolPRG.lean:64` |
| `BoolPRG.idDrawEquiv` | `BoolPRG.lean:66` |
| `BoolPRG.idDrawFintype` | `BoolPRG.lean:68` |
| `BoolPRG.idDrawNonempty` | `BoolPRG.lean:70` |
| `BoolPRG.idSamp` | `BoolPRG.lean:124` |
| `BoolPRG.idSamp_eff` | `BoolPRG.lean:99` |
| `BoolPRG.idxBits` | `BoolPRG.lean:82` |
| `BoolPRG.idxCard` | `BoolPRG.lean:54` |
| `BoolPRG.idxEquiv` | `BoolPRG.lean:56` |
| `BoolPRG.idxFintype` | `BoolPRG.lean:58` |
| `BoolPRG.idxNonempty` | `BoolPRG.lean:60` |
| `BoolPRG.outBound` | `BoolPRG.lean:88` |
| `BoolPRG.outLen` | `BoolPRG.lean:86` |
| `BoolPRG.outLen_le` | `BoolPRG.lean:90` |
| `Buckets.bucket` | `Buckets.lean:52` |
| `Buckets.bucketMatrix` | `Buckets.lean:192` |
| `Buckets.indexMap` | `Buckets.lean:87` |
| `Buckets.load` | `Buckets.lean:61` |
| `Buckets.rank` | `Buckets.lean:77` |
| `E0` | `Stretch.lean:51` |
| `HybridStage` | `Hybrids.lean:43` |
| `Internal.binomial_bound` | `Claim42/Load.lean:54` |
| `Internal.binomial_ratio_quarter` | `Claim42/Bounds.lean:131` |
| `Internal.bucket_count_lower` | `Claim42/Bounds.lean:57` |
| `Internal.bucket_count_upper` | `Claim42/Bounds.lean:41` |
| `Internal.bucket_tail` | `Claim42/Load.lean:91` |
| `Internal.capacity_bucket_tail_quarter` | `Claim42/Bounds.lean:195` |
| `Internal.cond1_all_fixed_index` | `Claim42/Conditions.lean:114` |
| `Internal.cond1_all_joint` | `Claim42/Conditions.lean:141` |
| `Internal.cond1_repetitions_fixed_index` | `Claim42/Conditions.lean:83` |
| `Internal.cond1_single_le_quarter` | `Claim42/Conditions.lean:48` |
| `Internal.cond2_sparse_joint_le_quarter_pow` | `Claim42/Conditions.lean:193` |
| `Internal.cond3_joint_le_quarter_pow` | `Claim42/Conditions.lean:161` |
| `Internal.encodeList_injective_of_fixedWidth` | `Basic.lean:49` |
| `Internal.encodeList_length_of_fixedWidth` | `Basic.lean:82` |
| `Internal.eventually_seed_relative_gap` | `Stretch.lean:256` |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:194` |
| `Internal.lpnNoise_law_cast` | `LPN.lean:120` |
| `Internal.prefactor_eventually_le_two_pow` | `Claim42/Bounds.lean:81` |
| `Internal.smallset_bucket_tail_quarter` | `Claim42/Bounds.lean:159` |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:177` |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:206` |
| `Internal.stretch_gaps` | `Stretch.lean:225` |
| `Internal.w_lower` | `Stretch.lean:206` |
| `LPNFamily` | `LPN.lean:525` |
| `LPNFamily.Raw` | `LPN.lean:133` |
| `LPNFamily.Raw.Assumption` | `LPN.lean:229` |
| `LPNFamily.Raw.Draw` | `LPN.lean:243` |
| `LPNFamily.Raw.adv` | `LPN.lean:220` |
| `LPNFamily.Raw.modulus` | `LPN.lean:137` |
| `LPNFamily.Raw.modulus_le_pow` | `LPN.lean:151` |
| `LPNFamily.Raw.modulus_prime` | `LPN.lean:141` |
| `LPNFamily.Raw.noiseDen` | `LPN.lean:139` |
| `LPNFamily.Raw.noiseDen_pos` | `LPN.lean:143` |
| `LPNFamily.Raw.residueBits` | `LPN.lean:147` |
| `LPNFamily.Raw.sampleCore` | `LPN.lean:360` |
| `LPNFamily.Raw.sampleLaw` | `LPN.lean:371` |
| `LPNFamily.Raw.samples` | `LPN.lean:135` |
| `LPNFamily.Raw.samplesBound` | `LPN.lean:145` |
| `LPNFamily.Raw.samples_le` | `LPN.lean:149` |
| `LPNFamily.Raw.toLWE` | `LPN.lean:190` |
| `LPNFamily.sample_eff` | `LPN.lean:527` |
| `Params` | `Params.lean:50` |
| `Params.B` | `Params.lean:138` |
| `Params.Cond1` | `Claim42/Defs.lean:43` |
| `Params.Cond2` | `Claim42/Defs.lean:56` |
| `Params.Cond3` | `Claim42/Defs.lean:71` |
| `Params.D` | `Params.lean:64` |
| `Params.Draw` | `Encoding.lean:148` |
| `Params.E` | `Params.lean:56` |
| `Params.G` | `Params.lean:58` |
| `Params.G1` | `Polys.lean:261` |
| `Params.G1_eval` | `Polys.lean:649` |
| `Params.G1_eval_of_good` | `Correctness.lean:253` |
| `Params.G2` | `Polys.lean:273` |
| `Params.G2_eval_of_flag` | `Correctness.lean:315` |
| `Params.G3` | `Polys.lean:285` |
| `Params.G3_eval_of_scaled` | `Polys.lean:753` |
| `Params.G4` | `Polys.lean:309` |
| `Params.G4_degrees` | `Polys.lean:541` |
| `Params.G4_eval_eq` | `Correctness.lean:413` |
| `Params.G4_eval_sdCore` | `Correctness.lean:351` |
| `Params.G4_seed_allOutputs` | `Correctness.lean:453` |
| `Params.G4struct` | `Polys.lean:297` |
| `Params.IdDraw` | `Encoding.lean:136` |
| `Params.LPNAdvice` | `Reductions/LPN.lean:135` |
| `Params.LPNAdvice.I` | `Reductions/LPN.lean:137` |
| `Params.LPNAdvice.buckets` | `Reductions/LPN.lean:138` |
| `Params.LPNAdvice.draw` | `Reductions/LPN.lean:139` |
| `Params.LPNAdvice.hop` | `Reductions/LPN.lean:136` |
| `Params.LPNAdvice.tail` | `Reductions/LPN.lean:140` |
| `Params.LPNAdvice.uniform` | `Reductions/LPN.lean:141` |
| `Params.LPNChal` | `Reductions/LPN.lean:51` |
| `Params.LPNRealizable` | `Reductions/LPN.lean:413` |
| `Params.OneSdOut.flag` | `Samplers.lean:133` |
| `Params.OneSdOut.priv` | `Samplers.lean:135` |
| `Params.OneSdOut.pub` | `Samplers.lean:134` |
| `Params.PRGAdvice` | `Reductions/PRG.lean:93` |
| `Params.PRGAdvice.buckets` | `Reductions/PRG.lean:95` |
| `Params.PRGAdvice.matrix` | `Reductions/PRG.lean:97` |
| `Params.PRGAdvice.uniform` | `Reductions/PRG.lean:100` |
| `Params.PRGChal` | `Reductions/PRG.lean:54` |
| `Params.PRGRealizable` | `Reductions/PRG.lean:288` |
| `Params.Priv` | `Params.lean:201` |
| `Params.Pub` | `Params.lean:247` |
| `Params.R` | `Params.lean:59` |
| `Params.Realizable` | `Security.lean:45` |
| `Params.SVar` | `Params.lean:180` |
| `Params.SdCoreOut.draw` | `Samplers.lean:228` |
| `Params.SdCoreOut.err` | `Samplers.lean:231` |
| `Params.SdCoreOut.first` | `Samplers.lean:230` |
| `Params.SdCoreOut.instances` | `Samplers.lean:229` |
| `Params.SdCoreOut.seed` | `Samplers.lean:232` |
| `Params.SdCoreOut.σ` | `Samplers.lean:227` |
| `Params.Seed` | `Encoding.lean:161` |
| `Params.Targets` | `Targets.lean:216` |
| `Params.W` | `Params.lean:111` |
| `Params.badSet` | `Samplers.lean:69` |
| `Params.badSet_expect_le` | `Claim42/Defs.lean:146` |
| `Params.bucketBound` | `Encoding.lean:350` |
| `Params.cap` | `Params.lean:132` |
| `Params.chainGame` | `Hybrids.lean:86` |
| `Params.chainPublic` | `Hybrids.lean:69` |
| `Params.claim42` | `Claim42.lean:58` |
| `Params.cond1_prob_le` | `Claim42/Defs.lean:274` |
| `Params.coreTarget` | `Targets.lean:116` |
| `Params.corr` | `Samplers.lean:97` |
| `Params.correctionPoly` | `Polys.lean:240` |
| `Params.d` | `Params.lean:51` |
| `Params.drawEquiv` | `Encoding.lean:233` |
| `Params.drawSamplerTarget` | `Targets.lean:179` |
| `Params.ellBound` | `Encoding.lean:332` |
| `Params.encDraw` | `Encoding.lean:309` |
| `Params.encIdDraw` | `Encoding.lean:276` |
| `Params.encIdx'` | `Encoding.lean:264` |
| `Params.encLPNAdvice` | `Reductions/LPN.lean:243` |
| `Params.encPRGAdvice` | `Reductions/PRG.lean:206` |
| `Params.encSeed'` | `Encoding.lean:321` |
| `Params.errProb` | `Claim42/Defs.lean:123` |
| `Params.errProb_le_decomposition` | `Claim42/Conditions.lean:268` |
| `Params.errProb_nonneg` | `Claim42/Defs.lean:135` |
| `Params.errSet` | `Samplers.lean:58` |
| `Params.eval'` | `Samplers.lean:313` |
| `Params.eval'_correct` | `Correctness.lean:431` |
| `Params.evalTarget` | `Targets.lean:72` |
| `Params.firstGood` | `Samplers.lean:186` |
| `Params.firstGood_none_iff` | `Correctness.lean:56` |
| `Params.halfForm` | `Polys.lean:201` |
| `Params.hasComplexityEff_of_target` | `Targets.lean:293` |
| `Params.hyb` | `Hybrids.lean:112` |
| `Params.hyb_prg_accept_eq_chain_zero` | `Hybrids.lean:157` |
| `Params.hyb_random_eq_raw` | `Hybrids.lean:148` |
| `Params.hyb_real_eq_raw` | `Hybrids.lean:142` |
| `Params.hyb_real_prg_le` | `Hybrids.lean:176` |
| `Params.hyb_uniform_accept_eq_chain_zero` | `Hybrids.lean:167` |
| `Params.hyb_uniform_random_le` | `Hybrids.lean:184` |
| `Params.idCore` | `Samplers.lean:274` |
| `Params.idDrawEquiv` | `Encoding.lean:215` |
| `Params.idSamp'` | `Samplers.lean:283` |
| `Params.idxBound` | `Encoding.lean:393` |
| `Params.idxEquiv` | `Encoding.lean:197` |
| `Params.jointLaw_prob_eq_uprob` | `Claim42/Defs.lean:96` |
| `Params.kappaOf` | `Params.lean:155` |
| `Params.kappaOfN` | `Params.lean:164` |
| `Params.kappaOfN_n` | `Params.lean:332` |
| `Params.kappaOf_pow` | `Params.lean:316` |
| `Params.linearCoeff` | `Polys.lean:178` |
| `Params.lpnEnc` | `Reductions/LPN.lean:68` |
| `Params.lpnFamily` | `Targets.lean:279` |
| `Params.lpnFamily_raw` | `Params.lean:367` |
| `Params.lpnPre` | `Reductions/LPN.lean:321` |
| `Params.lpnPreTarget` | `Targets.lean:139` |
| `Params.lpnRed` | `Reductions/LPN.lean:353` |
| `Params.lpnSamplerTarget` | `Targets.lean:197` |
| `Params.lpnVector` | `Samplers.lean:116` |
| `Params.lpn_hop` | `Reductions/LPN.lean:398` |
| `Params.m` | `Params.lean:83` |
| `Params.mBound` | `Encoding.lean:344` |
| `Params.n` | `Params.lean:76` |
| `Params.nBound` | `Encoding.lean:338` |
| `Params.noiseValue` | `Samplers.lean:45` |
| `Params.noiseWidth` | `Params.lean:90` |
| `Params.oneFlag` | `Samplers.lean:82` |
| `Params.oneSd` | `Samplers.lean:140` |
| `Params.oneSd_factors_mul` | `Correctness.lean:206` |
| `Params.one_le_E` | `Params.lean:57` |
| `Params.one_le_d` | `Params.lean:52` |
| `Params.packSeed` | `Samplers.lean:196` |
| `Params.prgEnc` | `Reductions/PRG.lean:83` |
| `Params.prgPoly` | `Polys.lean:221` |
| `Params.prgPre` | `Reductions/PRG.lean:248` |
| `Params.prgPreTarget` | `Targets.lean:154` |
| `Params.prgRed` | `Reductions/PRG.lean:271` |
| `Params.prg_hop` | `Reductions/PRG.lean:338` |
| `Params.primeWidthBound` | `Samplers.lean:343` |
| `Params.privEquiv` | `Params.lean:232` |
| `Params.privLen` | `Params.lean:209` |
| `Params.pubEquiv` | `Params.lean:255` |
| `Params.pubLen` | `Params.lean:173` |
| `Params.publicSeed` | `Hybrids.lean:53` |
| `Params.qGenTarget` | `Targets.lean:91` |
| `Params.rc` | `Params.lean:126` |
| `Params.rcBound` | `Encoding.lean:357` |
| `Params.realizable_of_targets` | `Targets.lean:232` |
| `Params.sVarBound` | `Encoding.lean:372` |
| `Params.sdCore` | `Samplers.lean:236` |
| `Params.sdSamp'` | `Samplers.lean:302` |
| `Params.sdSampFull` | `Samplers.lean:292` |
| `Params.seedBitsAt` | `Stretch.lean:64` |
| `Params.seedBitsAt_le` | `Stretch.lean:82` |
| `Params.seedBound` | `Encoding.lean:383` |
| `Params.t` | `Params.lean:120` |
| `Params.Γ` | `Params.lean:146` |
| `Params.δ` | `Params.lean:53` |
| `Params.δ_lt_one` | `Params.lean:55` |
| `Params.δ_pos` | `Params.lean:54` |
| `Params.ℓ` | `Params.lean:70` |
| `PolyTerms` | `PolyTerms.lean:45` |
| `PolyTerms.denote` | `PolyTerms.lean:56` |
| `PolyTerms.encTerms` | `PolyTerms.lean:85` |
| `PrimeParam` | `Defs.lean:48` |
| `PrimeParam.le_two_pow` | `Defs.lean:52` |
| `PrimeParam.p` | `Defs.lean:49` |
| `PrimeParam.prime` | `Defs.lean:50` |
| `PrimeParam.two_pow_le` | `Defs.lean:51` |
| `PrimeSchedule` | `Defs.lean:72` |
| `PrimeSchedule.nonempty` | `Defs.lean:82` |
| `SPRG` | `Defs.lean:402` |
| `SPRG.Raw` | `Defs.lean:97` |
| `SPRG.Raw.HasComplexity` | `Defs.lean:298` |
| `SPRG.Raw.HasComplexityEff` | `Defs.lean:352` |
| `SPRG.Raw.HasComplexityEff.hasComplexity` | `Defs.lean:388` |
| `SPRG.Raw.IdDraw` | `Defs.lean:107` |
| `SPRG.Raw.Idx` | `Defs.lean:102` |
| `SPRG.Raw.SdDraw` | `Defs.lean:127` |
| `SPRG.Raw.Secure` | `Defs.lean:260` |
| `SPRG.Raw.SubexpSecure` | `Defs.lean:267` |
| `SPRG.Raw.adv` | `Defs.lean:251` |
| `SPRG.Raw.challengeStr` | `Defs.lean:218` |
| `SPRG.Raw.encIdDraw` | `Defs.lean:113` |
| `SPRG.Raw.encIdDraw_injective` | `Defs.lean:114` |
| `SPRG.Raw.encIdx` | `Defs.lean:115` |
| `SPRG.Raw.encIdx_injective` | `Defs.lean:116` |
| `SPRG.Raw.encIdx_length_le` | `Defs.lean:118` |
| `SPRG.Raw.encSdDraw` | `Defs.lean:134` |
| `SPRG.Raw.encSdDraw_injective` | `Defs.lean:135` |
| `SPRG.Raw.eval` | `Defs.lean:136` |
| `SPRG.Raw.game` | `Defs.lean:234` |
| `SPRG.Raw.idCore` | `Defs.lean:112` |
| `SPRG.Raw.idDrawCard` | `Defs.lean:110` |
| `SPRG.Raw.idDrawEquiv` | `Defs.lean:111` |
| `SPRG.Raw.idDrawFintype` | `Defs.lean:108` |
| `SPRG.Raw.idDrawNonempty` | `Defs.lean:109` |
| `SPRG.Raw.idSamp` | `Defs.lean:179` |
| `SPRG.Raw.idxBits` | `Defs.lean:117` |
| `SPRG.Raw.idxCard` | `Defs.lean:105` |
| `SPRG.Raw.idxEquiv` | `Defs.lean:106` |
| `SPRG.Raw.idxFintype` | `Defs.lean:103` |
| `SPRG.Raw.idxNonempty` | `Defs.lean:104` |
| `SPRG.Raw.modulus` | `Defs.lean:98` |
| `SPRG.Raw.modulus_le_pow` | `Defs.lean:101` |
| `SPRG.Raw.modulus_prime` | `Defs.lean:99` |
| `SPRG.Raw.outBound` | `Defs.lean:123` |
| `SPRG.Raw.outLen` | `Defs.lean:121` |
| `SPRG.Raw.outLen_le` | `Defs.lean:126` |
| `SPRG.Raw.privLen` | `Defs.lean:120` |
| `SPRG.Raw.privLen_le` | `Defs.lean:125` |
| `SPRG.Raw.pubLen` | `Defs.lean:119` |
| `SPRG.Raw.pubLen_le` | `Defs.lean:124` |
| `SPRG.Raw.residueBits` | `Defs.lean:100` |
| `SPRG.Raw.sdCore` | `Defs.lean:132` |
| `SPRG.Raw.sdDrawCard` | `Defs.lean:130` |
| `SPRG.Raw.sdDrawEquiv` | `Defs.lean:131` |
| `SPRG.Raw.sdDrawFintype` | `Defs.lean:128` |
| `SPRG.Raw.sdDrawNonempty` | `Defs.lean:129` |
| `SPRG.Raw.sdSamp` | `Defs.lean:188` |
| `SPRG.Raw.seedBound` | `Defs.lean:122` |
| `SPRG.eval_eff` | `Defs.lean:403` |
| `SPRG.idSamp_eff` | `Defs.lean:404` |
| `SPRG.sdSamp_eff` | `Defs.lean:407` |
| `exists_sprg_of_targets` | `Targets.lean:333` |
| `exists_sprg_of_targets_subexp` | `Targets.lean:349` |
| `exists_sprg_raw` | `Security.lean:167` |
| `exists_sprg_raw_subexp` | `Security.lean:184` |
| `jlsSPRG` | `Targets.lean:301` |
| `jlsSPRG_raw` | `Samplers.lean:355` |
| `jlsSPRG_toRaw` | `Targets.lean:308` |
| `jls_hasComplexity` | `Correctness.lean:489` |
| `jls_hasPolyStretch` | `Stretch.lean:430` |
| `jls_secure` | `Security.lean:102` |
| `jls_seedBits_le` | `Stretch.lean:406` |
| `jls_subexpSecure` | `Security.lean:129` |
| `jls_subexpSmall` | `Security.lean:115` |
| `lemma42` | `Security.lean:62` |
| `lpnNoise` | `LPN.lean:49` |
| `lpnNoise_law` | `LPN.lean:67` |
| `privDegree` | `Degree.lean:56` |
| `prop41` | `Security.lean:84` |
| `pubDegree` | `Degree.lean:45` |
| `sparseEntries` | `SparseFactor.lean:48` |
| `sparseFactor` | `SparseFactor.lean:91` |
| `sparseFactor_mul_of_card_le` | `SparseFactor.lean:202` |
| `sparseLeft` | `SparseFactor.lean:61` |
| `sparseRight` | `SparseFactor.lean:76` |
| `theorem41` | `Security.lean:141` |
| `theorem41_of_targets` | `Targets.lean:319` |
| `theorem41_subexp` | `Security.lean:153` |

## Source and host disclosures

The paper was verified in place at SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF is copied, committed or delivered. The initial memory/disk observations
and the preflight retry remain historical measurements in the M0/M1/M2 reports;
this report makes no new resource measurement claim.

Both historical instruction breaches remain disclosed. An extra research
descendant exceeded the whole-job two-subagent limit and root interrupted it.
No Lean/cache/push/source mutation was reported for that descendant, based on
task reports rather than an independent process audit; no further agents were
spawned. Separately, tagged wrappers93883 and93983 overlapped at
15:07:45–15:07:48UTC; the recorded search child was terminated and the prior
wrapper released at15:08:34UTC. The records are
`evidence/host/team-limit-correction.json` and
`evidence/host/search-process-correction.json`.

The fresh exact-exception slot audit at 19:21:31UTC preserves every tagged line
and REAP provenance. It records 1,273 acquisitions, whole-history seriality false,
and maximum two tagged wrappers because the known three-second violation is not
erased. Its 504 post-correction acquisitions have maximum one wrapper, seriality
true and no active wrappers. Every other overlap would fail the checker. These
are snapshot-qualified tagged wrapper facts, not a global host process cap,
actual simultaneous Lean-process census or complete child-process history proof.
`evidence/host/M3-final-v2/slot-summary.json` gives the exact qualification and hashes.

## Current M3 v2 headline axiom prints

Fresh 19-headline probe at source 04249b8. Names have the prefix
`TCSlib.Cryptography.Obfuscation.StructuredSeed.`. Exact logs and hashes are in
`evidence/checkpoints/M3/axiom-summary-v2.json`.

| Headline | Current printed axioms |
| --- | --- |
| `prop41` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `Params.claim42` | `Classical.choice, Quot.sound, propext` |
| `Params.G4_eval_eq` | `Classical.choice, Quot.sound, propext` |
| `jls_hasComplexity` | `Classical.choice, Quot.sound, propext` |
| `jls_hasPolyStretch` | `Classical.choice, Quot.sound, propext` |
| `lpnNoise_law` | `Classical.choice, Quot.sound, propext` |
| `jls_secure` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `jls_subexpSmall` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `jls_subexpSecure` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `theorem41` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `theorem41_subexp` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `exists_sprg_raw` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `exists_sprg_raw_subexp` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `PrimeSchedule.nonempty` | `Classical.choice, Quot.sound, propext` |
| `Params.realizable_of_targets` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `jlsSPRG` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `theorem41_of_targets` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `exists_sprg_of_targets` | `Classical.choice, Quot.sound, propext, sorryAx` |
| `exists_sprg_of_targets_subexp` | `Classical.choice, Quot.sound, propext, sorryAx` |

## Size re-estimate

Current source is 8,672 lines, 222 above the original expected upper estimate of
8,450, while every file remains below the hard 1,000-line limit. M3 adds 978 lines
to M2's 7,694: the five load proofs, the fourteen specialized theorem-only helpers,
the five original Claim42 proofs and the three new module headers. This reflects
proof size and modular organization within the requested scope.

A provisional final estimate is 9,500–12,500 lines while the remaining 32 reduction,
security and target-link proofs are completed. This is a planning range, not a
completion claim or permission to add scope; M4's explicit realiser/averaging
transports dominate its uncertainty. Additional splits must preserve FQNs/frozen
headers/prose, exact move ledgers and complete final owner coverage. The final
measured source inventory will supersede this estimate.

## Remaining original obligations and continuation

The 32 remaining direct original bodies comprise M4's eight hybrid/security
statements, eight shared M4/M6 reduction/encoding obligations, M5's seven raw
security/existence statements, and M6's nine target links/assemblies. Supporting
encoding proofs completed in M1 do not by themselves complete M6. No transitive
sorryAx-dependent count is inferred from this direct-hole count.

| Frozen milestone | Remaining declaration (area prefix omitted) | M3 v2 source anchor |
| --- | --- | --- |
| M4 | `Params.hyb_real_eq_raw` | `Hybrids.lean:142` |
| M4 | `Params.hyb_random_eq_raw` | `Hybrids.lean:148` |
| M4 | `Params.hyb_prg_accept_eq_chain_zero` | `Hybrids.lean:157` |
| M4 | `Params.hyb_uniform_accept_eq_chain_zero` | `Hybrids.lean:167` |
| M4 | `Params.hyb_real_prg_le` | `Hybrids.lean:176` |
| M4 | `Params.hyb_uniform_random_le` | `Hybrids.lean:184` |
| M4 / M6 | `Params.lpnEnc_injective` | `Reductions/LPN.lean:368` |
| M4 / M6 | `Params.encLPNAdvice_injective` | `Reductions/LPN.lean:376` |
| M4 / M6 | `Params.encLPNAdvice_length_le` | `Reductions/LPN.lean:385` |
| M4 / M6 | `Params.lpn_hop` | `Reductions/LPN.lean:398` |
| M4 / M6 | `Params.prgEnc_injective` | `Reductions/PRG.lean:304` |
| M4 / M6 | `Params.encPRGAdvice_injective` | `Reductions/PRG.lean:311` |
| M4 / M6 | `Params.encPRGAdvice_length_le` | `Reductions/PRG.lean:322` |
| M4 / M6 | `Params.prg_hop` | `Reductions/PRG.lean:338` |
| M4 | `lemma42` | `Security.lean:62` |
| M4 | `prop41` | `Security.lean:84` |
| M5 | `jls_secure` | `Security.lean:102` |
| M5 | `jls_subexpSmall` | `Security.lean:115` |
| M5 | `jls_subexpSecure` | `Security.lean:129` |
| M5 | `theorem41` | `Security.lean:141` |
| M5 | `theorem41_subexp` | `Security.lean:153` |
| M5 | `exists_sprg_raw` | `Security.lean:167` |
| M5 | `exists_sprg_raw_subexp` | `Security.lean:184` |
| M6 | `Params.realizable_of_targets` | `Targets.lean:232` |
| M6 | `Params.evalEfficient_of_target` | `Targets.lean:238` |
| M6 | `Params.idSampEfficient_of_targets` | `Targets.lean:245` |
| M6 | `Params.sdSampEfficient_of_targets` | `Targets.lean:257` |
| M6 | `Params.lpnSamplerEfficient_of_target` | `Targets.lean:269` |
| M6 | `Params.hasComplexityEff_of_target` | `Targets.lean:293` |
| M6 | `theorem41_of_targets` | `Targets.lean:319` |
| M6 | `exists_sprg_of_targets` | `Targets.lean:333` |
| M6 | `exists_sprg_of_targets_subexp` | `Targets.lean:349` |

## Delivery verification

M3 source proofs and local milestone gates are complete at
`04249b85e80a007dc5845077a18a365d5150e14b`. **M3 packaging and publication
remain pending.** This READY report is ready for root's packager, not a claim that
an M3 payload has already been replayed, bundled, committed or pushed.

The packager must copy committed source; replay every patch at the pinned base
with exact commit hashes, including M0's empty marker; verify the bundle; check
every intermediate commit tree for PDFs; and verify exact source/evidence manifest
path sets and hashes. The future M3 `evidence/replay.json`, `bundle-verify.txt`,
`pdf-commit-trees.json`, `payload-source-binding.json`, COMMITS.tsv and exchange
publication record will be the delivery authority. No M3 delivery hash, successful
push or final ZIP is invented. Report SHA-256 is recorded externally in this
preparation's provenance, so no circular self-hash is embedded in REPORT.md.

Continue M4–M6 and then the full fresh stored-constant/kernel-type/canonical
four-variant seal/control gates. The candidate V2 tools remain unrun adaptations;
AST syntax checks are not gate passes. The four M0 mathematical tables are retained
byte-for-byte and their historical counts/anchors stay explicitly attributed.

No user question is pending. SP-W1 is resolved; SP-W2/SP-W3 and the disclosed
organization/process judgments remain available for downstream review. The agent's temporary report
preparation performed static reads and temporary writes only. It did not invoke
Lean, Lake, Git, cache tooling, source edits, final gates or agents. The pure temp
producer was executed only to verify existing root-produced records and render
this report/anchor/provenance packet; active evidence/REPORT.md is untouched.

## Complete source commit ledger

Every source commit since the pinned base is listed below. Exact author/committer
metadata and signing status are supplied by patches/COMMITS.tsv. Root appended this
ledger from Git when staging the active report.

| Commit | Subject |
| --- | --- |
| `03b157e974aed1021f920d3a954cc2dc43e7a5b4` | io-sprg: prepare Phase A module imports |
| `8679f7161261fb8294ffabdeee620ce859472cca` | io-sprg: draft raw syntax and construction cores |
| `83dda868993a846d278ffc0df7a1185f36f81490` | io-sprg: prepare complete M0 statement candidate |
| `b3712d241bf30130e9424b85c60c8223701be4cd` | io-sprg: complete public instance readers and lint names |
| `2af7d5111f63dcb24a498dbddcf76b1d26c591ef` | io-sprg: publish Boolean finiteness instance readers |
| `23f22a93d8ea100132baedeb04014d291e287be6` | io-sprg: prove derived sampler correspondence readers |
| `b80bfb9011f7bf39ec1548467c27dda102e2d0e9` | io-sprg: complete M0 reference and facade headers |
| `bb3455c5015031a9b03a4013fbe8d372fc09791d` | io-sprg: import shared floor bound for rounded stretch proofs |
| `4efedfad01b049abd1a393e1c449c6e49552119a` | io-sprg: repair sampler readers under canonical seals |
| `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0` | io-sprg: pre-M0 SP-W2 compare hybrid acceptance probabilities |
| `cd916ad868f1b921d1716d618f2fa1f9f8bbfdcf` | io-sprg: reuse existing bounded power inverse API |
| `55cb1147ff84f750a6b94f48103f6cc72d4fa036` | io-sprg: order parameter bounds for direct reuse |
| `18bfd824aa27796148a76a211ba7e75f65d225b4` | io-sprg: make raw bound transports robust to eval seals |
| `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3` | io-sprg: require growing seeds in polynomial stretch |
| `d10a560b34d58919bc1a5206ce66a444613f94c7` | io-sprg: M0 statements (all proofs sorry) |
| `68469690bf021684214da60615a7c1aec282a876` | io-sprg: M1 degree bounds |
| `5f3ea1c5e6c28f34fa0493cd49528d2489a7ad3e` | io-sprg: M1 parameter bounds and inverse schedules |
| `778397fd929839cc82f6cd70d400770b52796b4a` | io-sprg: M1 shared fixed-width encoding lemmas |
| `19627198f8f279fe6fdf3f67d7d658a1b39e79f0` | io-sprg: M1 faithful encodings and polynomial bounds |
| `cd837aee4db19fa47362316e8b3ac8a5dda09e7b` | io-sprg: M1 exact LPN law and faithful encodings |
| `f2095b7625171b1b1a7a1877a9b9eb5d3a23bb9f` | io-sprg: M1 deterministic bucket placement and correction matrices |
| `8854cf709238defb459377fea0a1e2ff54db88b7` | io-sprg: M1 explicit sparse-factor reconstruction |
| `6477edc198ec33eec8c682bd62ff344be896d07c` | io-sprg: M1 polynomial bidegrees and tensor evaluation |
| `19dde91afc384656e7e47cb018057e088d4ded0a` | io-sprg: M1 algebraic correctness and complexity links |
| `4ecc40c04a001bc87349b7ec368ece309774c28a` | io-sprg: M2 polynomial stretch with explicit rounded seed bounds |
| `e966956e25caf9512050ddf5d480a5dec7f4d3de` | io-sprg: M3 finite load bounds and modular probability analysis |
| `bc5d5227a52571ad5e1e9b86219cfcb4987b7771` | io-sprg: M3 error decomposition and explicit exponential load bounds |
| `c767ee867e76c0b1248cee46d4af5296ffa078d5` | io-sprg: M3 Claim 4.2 uniform in the public prime |
| `04249b85e80a007dc5845077a18a365d5150e14b` | io-sprg: M3 opacity-safe scalar law reader and proof cleanup |
<!-- END BYTE-EXACT HISTORICAL M3 REPORT -->
