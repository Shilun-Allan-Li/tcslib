# Lamport fill — checkpoint 2

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
Checkpoint 1: `09ac6b6c8c7f5997928ee5dfb4f18984ba2709b5`.
Frozen checkpoint-2 proof head: `77ec7bb1255852eb6288c6c38577a540a5e1a266` on
local `fill/lamport`; the proof branch is not pushed.

**Status:** the averaging bound and best-position choice are proved for the actual
Lamport forgery game. Checkpoint 1's planted experiment and algorithm readers are
retained. `Authentication.lamport_oneTimeSecure` still has its original `sorry`.
The efficient machine, advice and negligibility conclusion remain for the final
delivery. This payload is an intermediate checkpoint, not a completed proof of
Theorem 137.2.

## Delivered mathematics

For a forger `A`, let `ε_A(n)` be the acceptance probability of the actual one-query
`SignatureScheme.forgeGame`. The new owned theorem
`lamport_forgeGame_accept_eq_honestProbability` identifies this probability exactly
with the typed honest-table experiment. This equality does not assume the
algorithms' intended behavior: it uses the checked generator, signer and verifier
readers from checkpoint 1, the key-tape/table equivalence, and the forger codec's
published move/entry/timeout readers.

The actual signing oracle contains a sampling node even though Lamport signing
ignores its coins. `lamport_signImpl_expect` proves equality of its call law with
the deterministic typed signer, for every function of answer and state.
`lamport_loggedSignImpl_expect` preserves that equality with the query log.
The existing `ProbComp.expect_simulate_congr` then transports it through the
forger's logged simulation. No syntactic equality between a sampling computation
and a pure computation is asserted.

For each fixed position-bit pair `(i,c)`, `RedSuccess` means that the planted
simulation ends with a false abort bit and its extracted signature block maps to
the challenge image. `redProbability (i,c)` averages that predicate over an
independent uniform challenge preimage, a uniform complete secret table, and the
forger's coins. Thus the counted successes explicitly exclude aborted runs.

For every successful honest run with a signing query `m` and fresh forged message
`m'`, the favorable fraction is
`#{i : m_i ≠ m'_i} / (2n) ≥ 1/(2n)`. With no query, it is exactly `1/2`.
The favorable event simultaneously requires a safe query and `m'_i = c`.
`diagonal_red_of_success_favourable` turns each such run into a nonaborting
inversion when challenged with the image of its selected honest table entry.
The planted public key and aborting implementation ignore the original preimage
at that entry. `coordinate_reduction_bound` therefore applies the published
coordinate-resampling law to make the challenge independent of the table, while
preserving its average. It does not assume independence after conditioning on
nonabort.

The resulting bound is

```text
ε_A(n) / (2n) ≤ E_(i,c)[redProbability(i,c)]        (n > 0).
```

Finite maximum averaging chooses a position at least as good as this average.
`lamport_exists_best_position` proves the corresponding statement for the actual
game: for every `n > 0`, some `i : Fin n` satisfies

```text
ε_A(n) / (2n) ≤ E_c[redProbability(i,c)].
```

The planted bit remains fair. This step does not require an exactly uniform
`Fin n` sampler implemented with a fixed finite Boolean coin tape. Supplying the
chosen position as non-uniform advice and realizing this experiment as a T1
machine remain the final checkpoint's work.

## Files and declarations

The cumulative payload contains nine source files. Relative to checkpoint 1,
checkpoint 2 changes six files:

| File | Checkpoint-2 change |
| --- | --- |
| `Authentication/Signatures/Lamport.lean` | Coin/table readers, canonical string-function readers, forger-codec equality, signing-law bridge, exact actual-game probability equality, and best-position theorem. |
| `Lamport/Averaging.lean` | Favorable-pair counting, no-query fraction, finite maximum and expectation bounds. |
| `Lamport/AveragingExtra.lean` | Optional-query bound and best-position selection with a fair bit. |
| `Lamport/Statistics.lean` | Coordinate-invariant reduction averaging via independent resampling. |
| `Lamport/Experiment.lean` | Typed honest/reduction predicates, their probabilities, averaging bound and best position. |
| `Authentication.lean` | Four import-only registrations for the new helpers. |

The checkpoint-1 `Lamport/Encoding.lean`, `Lamport/Planted.lean` and
`Lamport/TableCoins.lean` are unchanged. The owned module imports its helpers
precisely and extends its Contents list. Every delivered file is below 1000
lines; the owned module has 905 lines at the frozen head.

The user authorized the required facade imports with “Allow the required facade
imports”; the request and authorization are retained under `evidence/requests/`.
No other frozen file is edited. The target statement, earlier declarations,
statement prose and global simp attributes are preserved. The target sketch and
statement-phase title remain pending their final-proof update. The local
irreducibility installation on the probability interpreter and bind forces the
probability proofs to use their published laws; it adds no global simp rule. It
checks the current reducibility status before installing an attribute, so it is
idempotent when whole-file probes have already sealed those definitions.

`evidence/new-declarations-checkpoint2-r2.json` compares immutable issue, checkpoint-1
and checkpoint-2 sources. There are 40 new public explicit declarations and one
new private explicit declaration in checkpoint 2. The cumulative counts since
issue are 109 public and one private. No explicit declaration was removed.
The private addition is the generic structure-extensionality theorem
`lamport_codec_ext`. The JSON categorizes private names separately and records
their lexical names rather than claiming Lean's mangled stored names.
Generated constants are covered by the separate runtime census. The original
checkpoint-1 declaration JSON is preserved unchanged and its hash is recorded in
the new inventory.

## Promotion, readers and duplication

The existing promotion requests remain: cryptographic tuple-encoding injectivity,
the generic cost-zero computation lemma, and the tape/table serialization facts.
Additional promotion candidates are the generic finite favorable-pair counting
and maximum-average lemmas, optional-query/fair-bit position averaging,
`coordinate_reduction_bound`, and the private generic codec-extensionality fact.
The actual Lamport signing laws, forgery-game equality and planted experiment are
construction-specific.

No missing foreign reader or failure of the issued mathematical route has been
found. All uses of foreign definitions in the new proofs go through their
published readers. The codec-extensionality proof eliminates variables of the
public `MachineCodec` structure; it does not unfold another file's constructed
codec.

**overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.
This is the unchanged checkpoint-1 overlap: the private two-block identity was
re-derived inside the general serialization proof from public
`FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`; its private proof was
not copied. No additional copied private proof is introduced in checkpoint 2.

Provider searches are retained in `evidence/logs/duplication-searches-checkpoint2.json`
with their commands and raw output. Searches for probability/sample-product and
simulation laws identified `Bridge.expect_sample_pair`,
`ProbComp.expect_sample_comm`, `ProbComp.expect_sample_coord` and
`ProbComp.expect_simulate_congr`; the delivered proofs import and consume them.
A draft product-average lemma was removed after identifying that public provider.
The source search for codec extensionality found the public structure but no
existing extensionality theorem. Searches for tuple-encoding injectivity outside
the owned helpers found no public provider. Cost-zero and two-block reader
searches are retained as well. No public provider was copied into the payload.

## Edge cases

- `n = 0`: the actual-game equality is valid at every parameter. The averaging
  and best-position lower bounds explicitly require `n > 0`; negligibility at
  zero is reserved for the final finite-exception argument.
- No query: the first-query log is empty, all pairs are query-safe, and exactly
  half select the forged message bit.
- `m' = m`: after a query, freshness excludes this case. Distinct messages give
  a differing coordinate and hence at least one favorable position-bit pair.
- Wrong-length or malformed forger words: the canonical bit codec determines
  the same fixed-width/default values in both games; the codec equality is
  proved from its move, entry and timeout readers. This includes budget timeout.
- Malformed signatures and verifier lengths: the existing guarded verifier and
  its checked coordinatewise reader are used unchanged.
- An unsafe planted query may occur in a successful honest forgery, but it does
  not contribute to the jointly favorable event. `RedSuccess` requires an
  explicitly nonaborting planted run; the averaging argument does not treat a
  successful aborting branch as extraction success.

## Environment and checks

The seven issued pack hashes and issue source hashes verified before editing.
The toolchain is Lean 4.25.0 with Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
Only the 82 issued Mathlib roots were fetched. The helper-import audit reports
no root outside those 82. T1's nine extra TCSlib prerequisites,
`Games.Bridges.Experiments`, and the required `Games.Hopping` were checked
sequentially using the same worker-owned olean tree.

The original macOS preflight remains in evidence: 12 CPUs;
19,327,352,832 physical-memory bytes; native available-memory estimate
8,697,308,774 bytes (45%); initial APFS free space 276,725,379,072 bytes and then
273,175,490,560 bytes. These exceed the 4 GiB memory-headroom and 12 GiB initial
disk floors. Linux cgroups, `/proc/meminfo`, `nproc`, and GNU `df -B1`/`df -T`
were unavailable; raw failures and native measurements are retained, without
claiming a Linux `MemAvailable` measurement.
The preexisting host cache held 32,667 files / 1,595,387,830 bytes of unknown
earlier origin. The narrowed fetch downloaded zero files and unpacked 2,339
existing archives. Present packages matched the manifest; the documentation
packages doc-gen4, UnicodeBasic, BibtexQuery and MD4Lean were ABSENT. The
Mathlib-import probe passed and no empty olean was found.

The complete issued 150-module baseline bootstrap passed one module per
`scripts/lean_check_tree.sh` call. No `lake build`, unfiltered cache fetch,
copied dependency tree, joined `LEAN_PATH`, or memory-backed scratch tree was
used. Python commands use `python3 -I`; the separate exchange checkout is
transport-only.

The addendum's initial host-wide one-Lean rule was superseded by the user's
explicit three-process Mac override, followed by a temporary slot reservation for
dl-crh's bootstrap. Read-only verification later confirmed that its exact-base
98-module bootstrap had completed with zero errors and its final sweep was active.
The bootstrap-only extra reservation was then released; new guard invocations use
the shared limit of three actual Lean processes across this Mac.
The authorization and chronology are in
`evidence/requests/host-serialization-override.md`. Lamport still checks only one
module at a time; its guard waits for capacity and interrupts only
its own check if the shared cap is exceeded. No other worker's process or cache
is modified. Process-state and executable-path checks confirmed that the bare
`lean` entries were running compilers. The reservation-release observation and
process diagnosis are retained in the raw evidence. After repeated interruptions,
the user explicitly authorized a coordination note to the other active worker chats;
the exact message and receipts are retained in
`evidence/requests/worker-coordination-note-authorized.json`. Guard waits and interrupted checks are preserved and are not
counted as mathematical failures or successful checks.

The source-hash-matching successful checks for this frozen payload include:

- `Averaging-03` and `AveragingExtra-02`;
- fresh `Idempotent-01` checks of `Statistics`, `Experiment`, the owned `Lamport`,
  unchanged `HashAndSign`, and registered `Authentication`; the only admissions
  reported are the unchanged Lamport and HashAndSign targets.

Earlier `Statistics-08`, `Experiment-02`, `Lamport-07`, and `Authentication-02`
checked the original candidate. The final checkpoint retains the same proof
bodies with the idempotent local-attribute command.

Checkpoint-1 `Encoding-03`, `Planted-04` and `TableCoins-01` remain applicable to
their unchanged sources. All failed attempts, guard interruptions, source
snapshots, resource measurements and `results.jsonl` entries are retained.
The isolated frozen-tree style comparison reports 216 inherited FAIL at both
issue and checkpoint 2, with zero new FAIL and zero removed FAIL.

The four-patch series from the issue base reproduces all nine delivered source
files byte-for-byte. `evidence/logs/source-payload-checkpoint2-r2.json` records
successful sequential application and exact reproduction; it explicitly does
not claim a compiler run in the reproduction checkout. `evidence/logs/checkpoint2-checked-source-hashes-r2.json` identifies successful
canonical module checks matching all nine frozen source hashes. Later uncommitted final
machine work is excluded from the frozen checkpoint-2 patches and source payload.
The exact source-only inputs of its preparatory installation audit are separately
retained under `evidence/preparatory/final-machine-installation/`, clearly labeled
as unverified preparation rather than delivered proof source.

## Seal, axiom and delivery evidence

The baseline and checkpoint-2 main-file A/B evidence, paired controls,
source/closure manifests, request records, tools and raw logs are retained.
The other helper and final-facade seals remain explicitly pending for final delivery;
the prepared all-nine queue does not imply that those checks have been executed.
Mode A excludes `PolyExpr.eval` as notation; mode B seals it. The exact seal and
axiom results must be reported per failing declaration, rather than replacing a
sealed check with an unsealed one.

### Rule 10, controls and axioms at checkpoint 2

Mode A excludes `Complexity.PolyExpr.eval` as notation; mode B seals it too.
All results below are actual whole-file probes over the complete recorded TCSlib import
closure. No failed B run is replaced by an unsealed check or omitted from the payload.

**Pinned base, owned Lamport module.** At `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`,
A passed with zero errors and 1,445 requested definitions. B had 15 diagnostics in these
11 declarations, with 1,446 requested definitions:

- `TCSlib.Cryptography.Authentication.lamport`
- `TCSlib.Cryptography.Authentication.lamportOWF`
- `TCSlib.Cryptography.Authentication.lamportOWF_f`
- `TCSlib.Cryptography.Authentication.lamportOWF_inLen`
- `TCSlib.Cryptography.Authentication.lamportOWF_outLen`
- `TCSlib.Cryptography.Authentication.lamport_gen`
- `TCSlib.Cryptography.Authentication.lamport_msgLen`
- `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`
- `TCSlib.Cryptography.Authentication.lamport_sigLen`
- `TCSlib.Cryptography.Authentication.lamport_sign`
- `TCSlib.Cryptography.Authentication.lamport_ver`

The first B obstruction is the unchanged definition-level equality between
`PolyExpr.var.eval n` and `n` in `lamportOWF`/`lamport`; later dependent declarations
cascade from it. All six original base controls passed. Each sealed negative failed
exactly once at its designated line. Raw requests, complete INSTALL/EOF coverage and
every diagnostic are in `evidence/logs/seals/base-r1/`.

**Pinned base, authorized Authentication facade.** Its base snapshot has zero local
stored constants and exactly 149 canonical TCSlib dependency modules. Both A and B pass,
with 1,944 and 1,945 requested definitions respectively; all six paired controls pass,
and each negative fails exactly once. This base environment was obtained by checking
canonical pinned-base Lamport and HashAndSign in this worker's existing olean tree.
All 147 other provider oleans were unchanged. The census rejects unexpected TCSlib module
homes, so final helper imports cannot silently enter this baseline.

The first facade queue completed both source seals and five controls; its B-reader
control was interrupted by the host cap before INSTALL/EOF. The filtered retry reused
the identical request record only after checking that both freshly built canonical base
oleans were byte-identical to the census environment and all 147 provider hashes matched.
The B-reader finally passed in `baseauth-cp2-r2-seals-host5`. Failed host attempts remain
in the payload. The exact final source bytes were restored and final Lamport,
HashAndSign and Authentication were rechecked successfully. The rollup and all original
results are retained under `evidence/logs/base-auth/base-auth-cp2-completion.json`,
`evidence/logs/base-auth/baseauth-cp2-r1/`, `evidence/logs/base-auth/baseauth-cp2-r2/`
and `evidence/logs/seals/baseauth-cp2-*/`. No olean tree was copied or joined.

**First checkpoint-2 candidate, `11cc4e54fb63bb1c6310e90e6fbaa07e7031fb07`.** A produced
three command diagnostics at source line 765: the unconditional local attributes tried
to mark `ProbComp.expect`, `ProbComp.sample` and `OracleComp.bind` irreducible when the
seal had already done so. The source mapper attaches them to the preceding
`TCSlib.Cryptography.Authentication.lamport_forgerCodec` declaration; they are attribute
installation errors, not three failures of that theorem's proof. B produced 25 errors.
All six controls passed. All raw results and failing sources are preserved in
`evidence/logs/seals/cp2-rule10-r1-Main-r1/`.

**Revised candidate, `77ec7bb1255852eb6288c6c38577a540a5e1a266`.** The native source fix makes
the same local attribute installation idempotent in main, Statistics and Experiment,
without unsafe reducibility, unsealing, a new public metaprogram API, or a statement change.
Statistics, Experiment, Lamport, HashAndSign and Authentication all pass their fresh
native checks. Revised main A passes with zero errors; B has 22 errors. Both candidates'
B errors map to the same following 16 declarations, all listed here:

- `TCSlib.Cryptography.Authentication.lamport`
- `TCSlib.Cryptography.Authentication.lamportOWF`
- `TCSlib.Cryptography.Authentication.lamportOWF_f`
- `TCSlib.Cryptography.Authentication.lamportOWF_inLen`
- `TCSlib.Cryptography.Authentication.lamportOWF_outLen`
- `TCSlib.Cryptography.Authentication.lamport_exists_best_position`
- `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`
- `TCSlib.Cryptography.Authentication.lamport_forgerCodec`
- `TCSlib.Cryptography.Authentication.lamport_gen`
- `TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect`
- `TCSlib.Cryptography.Authentication.lamport_msgLen`
- `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`
- `TCSlib.Cryptography.Authentication.lamport_sigLen`
- `TCSlib.Cryptography.Authentication.lamport_sign`
- `TCSlib.Cryptography.Authentication.lamport_signImpl_expect`
- `TCSlib.Cryptography.Authentication.lamport_ver`

This is the inherited 11-declaration list plus:

- `TCSlib.Cryptography.Authentication.lamport_exists_best_position`
- `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`
- `TCSlib.Cryptography.Authentication.lamport_forgerCodec`
- `TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect`
- `TCSlib.Cryptography.Authentication.lamport_signImpl_expect`

The additional B diagnostics are retained as dependent application/type cascades after
the unchanged constructor-level B obstruction; they are not claimed to pass. For example,
the codec diagnostic reports `f` being supplied to the errored `lamport` application
where the remaining elaborated argument expects `List Bool → List Bool`. The repaired
local installation command contributes no new A or B error.

Revised main A/B INSTALL and EOF coverage validate all 1,492/1,493 requested definitions.
All six revised controls pass: both unsealed and reader controls compile, and each sealed
negative has exactly one error at its designated line. The full lists, line mappings,
source snapshots and raw diagnostics are in `evidence/logs/seals/cp2-rule10-r2-Main-r1/`.

**Stored constants and explicit scan.** The revised main census prints the axioms of all
91 stored constants. Ninety use only subsets of `propext`, `Classical.choice` and
`Quot.sound`. The still-admitted `lamport_oneTimeSecure` alone additionally uses `sorryAx`;
its exact set is `[Classical.choice, Quot.sound, propext, sorryAx]`. No other nonstandard
axiom occurs. This is checkpoint evidence, not a claim that the target is proved.
The complete census is in `evidence/logs/helper-checks/Inventory-cp2-rule10-r2-Main-inventory1.log`.

The explicit-unfold scan recorded 376 token readings and 15 review candidates. All 15
are benign: 12 are local-name/parameter-label suffix matches; two are arguments to
published reader lemmas; one is an unchanged outer function in a representation equality.
There is no forbidden explicit foreign unfold. The raw scan and row-by-row review,
bound to the revised source and inventory hashes, are
`evidence/seals/Cp2R2Main/explicit-unfold-scan.json` and
`evidence/seals/Cp2R2Main/explicit-unfold-review.json`.

**Remaining final-delivery checks.** Whole-file final seals for the helpers and final
Authentication facade are still pending. When the target proof and final machine imports
land, main must be sealed again too. This intermediate checkpoint does not claim those
omitted final checks complete.

No new helper contains `sorry` or an axiom declaration. The issue census contains
22 admitted declarations; the target is deliberately still admitted at this
checkpoint. The final stored-constant axiom census, supplied-order sweep, sorry
comparison showing only removal of the target, final seals and final style
comparison remain requirements of the final proof delivery.

Before publication, regenerate `evidence/SHA256SUMS` over every delivered raw
artifact and check exact manifest/path-set equality. The final delivery must
also return the complete ZIP with `lamport/` at its root in chat, as required by
the issued brief. Neither evidence size nor the exchange push substitutes for
that completeness check.
