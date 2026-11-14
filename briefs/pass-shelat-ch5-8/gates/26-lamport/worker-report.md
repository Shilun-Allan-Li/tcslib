# Lamport fill — final

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
Final local proof head: `47ced271090f45918645c842cd358c5079092754` on `fill/lamport`.
The proof branch is kept local and is not pushed.

**Proved:** `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`, with its original
statement unchanged. Lean 4.25.0 and pinned Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` are retained.
The final 177-module sweep passes with zero errors. Admissions are exactly 22→21,
removing only this target. Its direct axiom probe prints exactly
`[propext, Classical.choice, Quot.sound]`.

All eighteen ordinary-definition seals A pass. Strict B additionally seals
`PolyExpr.eval` and reports 32 diagnostics across seventeen declarations in two files;
those results and their type-width causes are reported below, not called passes.
All 102 paired controls pass, all 321 stored constants have only standard axioms,
and all 50 explicit-unfold candidates were reviewed without a forbidden foreign unfold.

## Proof route and checkpoints

For each one-query forger `A`, write `ε_A(n)` for acceptance in the actual
`SignatureScheme.forgeGame`. The proof follows the issued planted-experiment route:

1. At fixed `(i,c)`, plant the challenge image in one public-key cell. Couple safe signing
   queries with the honest table, and extract the corresponding preimage block from an
   accepted forgery whose message bit is `c`.
2. A successful honest run with query `m` and fresh forgery message `m'` has favorable
   fraction `#{i : m_i ≠ m'_i}/(2n) ≥ 1/(2n)`. Without a query the fraction is exactly `1/2`.
   Coordinate resampling makes the challenge preimage independent while preserving the
   average. No independence after conditioning on nonabort is assumed.
3. The actual-game equality and averaging theorem choose a best fixed position for every
   positive length. T1 realizes the planted simulation as one machine before this sequence
   of positions is supplied as advice. Only nonaborting reduction successes are transported
   to actual inversion witnesses.
4. The chosen index is encoded in exactly `Nat.size n` binary bits. The existing bounded
   binary-to-unary decoder, parameter-aware preprocessing and `NUPPT.exists_withAdvice`
   recover its unary form internally. The constructor's polynomial bound is
   `Nat.size n ≤ n`; no uniform best-index search or exact uniform `Fin n` sampler is needed.
5. The result is one inverter `C` satisfying
   `ε_A(n)/(2n) ≤ (lamportOWF L f).invProbAt C n` for `n ≥ 1`.
   Strong one-wayness and the published `Negligible.mul_pow`, `const_mul` and `mono`
   lemmas make `ε_A` negligible. The eventual comparison begins at one, so `n=0` is a
   finite exception without changing any probability or theorem statement.


Checkpoint 1 (planted coupling and algorithm readers) was pushed as
`70023e3c331fcf7861ff230dd9ff5ef525d0f08d`. Checkpoint 2 (actual-game averaging and best
position), proof head `77ec7bb1255852eb6288c6c38577a540a5e1a266`, was pushed as
`12e086f037ba0b6bc5d78d83790252387c0de60f`. Its exact transport verification is
[evidence/logs/checkpoint2-delivery-verification.json](evidence/logs/checkpoint2-delivery-verification.json).
Both intermediate checkpoints retained the target admission; this final source removes it.

The first proved candidate `252ec646b9a5605c11aa245629a4ce8f404f74e8` was corrected for
public-API reuse before finalization. Its complete successful sweep and earlier source
preparations remain historical evidence; final verification uses `47ced271…`.

## Files, declarations and scope

The payload changes eighteen library source files: the owned
`TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`, sixteen helpers in its
`Lamport/` directory, and authorized import-only registrations in `Authentication.lean`.

| Helpers | Purpose |
| --- | --- |
| Encoding | Tuple-encoding injectivity and equality readers. |
| Planted | Tables, planting, one-query coupling, nonabort and extraction. |
| TableCoins, Seed | Tape/table and fair-bit/table equivalences. |
| Averaging, AveragingExtra | Favorable-pair counts and fixed-position averaging. |
| Statistics, Experiment | Independent resampling and typed probability bounds. |
| Blocks | Fixed-width tuple replacement under serialization. |
| Machine, MachineSpec | Polynomial-time handler and its functional contracts. |
| Nonabort, Realization | Nonabort-to-safety and T1 machine realization. |
| Advice | Binary index advice and bounded unary expansion. |
| InversionProbability | Transport to the actual machine inversion probability. |
| Closing | Linear-loss negligibility and one-time-security closure. |

The title drops “(statement phase)”, Main results marks the theorem proved, Contents lists
all sixteen helpers, and sketch step 5 describes the actual machine, advice and closure.
The explicit source inventory is
[evidence/new-declarations-final-r2.json](evidence/new-declarations-final-r2.json):
268 declarations across the eighteen files, consisting of all 47 original names and
220 new public plus one new private declaration. No original name is removed. Its lexical
parser limits are explicit; generated/private stored constants are covered by the separate
321-constant native census. Every new public definition has its readers and docstring.

The immutable final source commit `47ced271090f45918645c842cd358c5079092754` changes exactly the owned Lamport module, its sixteen new helper modules, and the authorized import-only `Authentication.lean` facade. All six intermediate source commits stay within that path scope, and every intermediate facade retains all non-import bytes and original imports. All eighteen files are plain Lean source files and contain fewer than 1,000 lines; the main module has 973 and `Machine.lean` has 340.

The target theorem header is byte-for-byte equal to the issued base. The source audit finds all forty-six other original declaration bodies and directly attached docstrings unchanged, with no removed line outside the allowed module title, target Main-results status, and target doc/proof regions. The added Contents section lists the sixteen delivered helpers. Manual review confirms that all four added `include ... in` occurrences affect only new lemmas and that the idempotent command after all original non-target declarations installs only local irreducibility for `ProbComp.expect`, `ProbComp.sample`, and `OracleComp.bind`. That command intentionally tightens the later target proof's transparency context while preserving its statement. No new `sorry`, `admit`, axiom, unsafe declaration, global simp directive, or bare `Mathlib` import was detected. This is an exact-text and lexical audit, not a claim to have parsed Lean semantically; compiled target types, axioms, effective imported environments, and Rule-10 results are reported separately.

Compared with the historical `252ec646…` candidate, only `Machine.lean` changes: it removes the duplicate `LamportMachine.take_poly` and `LamportMachine.drop_poly` wrappers, imports `Asymptotic.ReductionSupport`, and uses the already-published `TCSlib.Cryptography.takeLen_poly` and `dropLen_poly` at every former use site. The provider source is unchanged from the pinned base; the public API reuse resolves this duplication and requires no promotion request. The main module, facade and other fifteen helper files are byte-identical to the preceding candidate.

The frozen-commit campaign lint has the same 216 findings as the pinned baseline, with zero added or removed findings. Its exit status remains 1 because the inherited findings remain. Fresh raw Git diff, source blobs/hashes, removed-line records, manual review, mode records, provider source and candidate delta are under `evidence/logs/final-source-integrity-r2/`; lint comparison and raw output are `evidence/logs/lint-final-source-integrity-r2-comparison.json` and `evidence/logs/style-final-source-integrity-r2-delivered-tree.log`. The historical candidate's r1 audit is retained.


The facade exception was explicitly authorized by the user (“Allow the required facade
imports”); see [the authorization](evidence/requests/facade-authorization.md).

## Reuse, promotion and overlap

Final Machine imports `Asymptotic.ReductionSupport` and consumes its public
`TCSlib.Cryptography.takeLen_poly` and `dropLen_poly`. The two duplicate local wrappers
were removed. The provider is unchanged from the issue base and was already in the issued
order; this adds no module or Mathlib root and creates no promotion request for those facts.
The exact disposition is in
[evidence/preparation/final18-r2/public-prefix-reuse-resolution.json](evidence/preparation/final18-r2/public-prefix-reuse-resolution.json).

- **overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.
  The general serialization proof rederives the private two-block identity through public
  `FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`; no private proof is copied.
- **overlap: TCSlib/Cryptography/Authentication/Signatures/Lamport.lean lamportVerFun_sign.hflat**.
  `MachineSpec.publicWord_flatten` rederives the serialization identity through the public
  encoding/list equations. The additional owned verifier now consumes this public helper.
- **overlap: TCSlib/Complexity/ClassNP/TMSAT.lean tmsat_pt_take**.
  Historical local prefix wrapper removed; public `takeLen_poly` is used instead.
- **overlap: TCSlib/Complexity/CookLevin/Hardness.lean clA5Drop_native**.
  Historical local suffix wrapper removed; public `dropLen_poly` is used instead.
- **overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_take_poly** and
  **overlap: TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean dlb_drop_poly**.
  These additional exact private overlaps were found in the final search; removal of the
  local wrappers resolves them too. Their private proofs were not copied.

Promotion requests: shared encoding injectivity/equality; the cost-zero OracleComp return
characterization; codec extensionality; list-window and fixed-width tuple-update readers;
favorable-pair/optional-query averaging; coordinate-invariant reduction; bounded binary
index/advice support; polynomial-loss negligibility and signature-reduction closure.
The current nonabort reader may be generalized for another consumer. Table/seed layouts,
realization and inversion comparison retain Lamport contracts. Existing probability
product, coordinate-resampling and simulation laws are imported, not reimplemented.
Search commands, raw matches and dispositions are retained in the preparation and checkpoint
search evidence. No missing frozen foreign reader or mathematical route failure was found.

## Edge cases

- At zero, the machines/advice remain total; the eventual negligible comparison starts at
  one and permits that finite exception without changing any probability.
- With no query, the log is empty, query safety holds, and the favorable fraction is 1/2.
- Freshness excludes reusing the signed message; distinct messages provide a differing bit.
- Malformed/wrong-length forger words use the existing fixed-width codec/defaults and guarded
  verifier through their readers in both actual and typed games.
- The lower bound counts only nonaborting reduction runs. A false final abort flag yields
  safe-query agreement and the actual extracted inverse; no successful abort is assumed.

## Environment and bootstrap

The seven issued pack hashes and all issue source hashes verified before editing.
Only the 82 issued Mathlib roots were fetched; the final 177-module root census is exactly
that same set. The preexisting host cache held 32,667 files / 1,595,387,830 bytes of unknown
earlier origin. The narrowed fetch downloaded zero files and unpacked 2,339 existing
archives. All present packages match the manifest; doc-gen4, UnicodeBasic, BibtexQuery and
MD4Lean are ABSENT documentation packages. The Mathlib import probe passed; no empty olean
was found.

The native macOS preflight records 12 CPUs, 19,327,352,832 physical-memory bytes,
available-memory estimate 8,697,308,774 bytes (45%), and APFS free space initially
276,725,379,072 bytes, then 273,175,490,560 bytes. These exceed the initial 4 GiB memory and
12 GiB disk floors. Linux-only commands were unavailable; raw failures and native
measurements are in [preflight.log](evidence/logs/preflight.log). Native timing permissions
were corrected after the initial sysctl instrumentation failure; it was not cache corruption.

The supplied 150-module baseline, nine extra T1 prerequisites, `Games.Bridges.Experiments`
and `Games.Hopping` were checked one module at a time in this worker's own olean tree.
The final order has all 150 issued modules in the same order plus sixteen helpers and
eleven prerequisites. No project `lake build`, unfiltered cache fetch, copied dependency
tree, joined `LEAN_PATH` or memory-backed scratch was used. Python is `python3 -I`.
The separate exchange checkout is transport-only.

The user's shared-Mac limit of three actual Lean processes supersedes the initial single
process rule. Lamport still checks one module at a time. The temporary dl-crh bootstrap
reservation, its release after that bootstrap completed, and the explicitly authorized
coordination message are retained under `evidence/requests/`. Only our own native child was
interrupted when needed. Resource waits/interrupted attempts remain distinct from proof
failures and successful checks. Retirement of the stopped Python coordinator was intentional;
no Lean was killed by that retirement and it is not a Lean resource-shortage exit.

## Final checks

The final canonical source checks and direct target axiom probe pass on the exact frozen
source bytes. The required final 177-module sweep passes with every module checked once,
zero errors, and exactly 21 admission warnings. The baseline set of 22 loses only
`lamport_oneTimeSecure`; no new admission appears. Exact order/source hashes, raw module
logs and the independent comparison are at
[evidence/logs/final-sweep-comparison-r2/report.json](evidence/logs/final-sweep-comparison-r2/report.json).
The direct axiom output is
[evidence/logs/helper-checks/FinalTargetAxioms-Reuse01.log](evidence/logs/helper-checks/FinalTargetAxioms-Reuse01.log).
Lint remains 216 inherited findings with zero new findings. The six cumulative patches
reproduce all eighteen final source files byte for byte from the issue base; see
[evidence/logs/source-payload-final-r2.json](evidence/logs/source-payload-final-r2.json).

## Whole-file seals, axioms and explicit unfolding

A excludes `PolyExpr.eval` as notation; B also seals it. The base Lamport A passed;
base B reported 15 diagnostics in eleven declarations:
`lamport`, `lamportOWF`, `lamportOWF_f`, `lamportOWF_inLen`, `lamportOWF_outLen`,
`lamport_gen`, `lamport_msgLen`, `lamport_oneTimeSecure`, `lamport_sigLen`, `lamport_sign`,
`lamport_ver` (all in `TCSlib.Cryptography.Authentication`). Its first obstruction is
`PolyExpr.var.eval n` versus `n` in the unchanged family/scheme definitions. All six base
controls pass. Base Auth has zero own constants and exact closure149; both A/B and six
controls pass. Its base Lamport/HashSign products and all147 other provider hashes were
checked, and original final sources restored/rechecked. The interrupted B-reader retries
and exact provenance remain at
[evidence/logs/base-auth/base-auth-cp2-completion.json](evidence/logs/base-auth/base-auth-cp2-completion.json).
All sixteen new helper paths are ABSENT at base, with raw Git errors/exits retained;
no empty base compilation is substituted.

All eighteen final whole-file Rule 10 reviews are complete for `47ced271090f45918645c842cd358c5079092754`.

| File | Own constants | Closure | A/B definitions | A/B errors | Controls | Scan readings/candidates |
|---|---:|---:|---:|---:|---:|---:|
| Planted | 67 | 100 | 1438/1439 | 0/0 | 6 | 150/3 |
| Encoding | 3 | 53 | 813/814 | 0/0 | 6 | 6/0 |
| TableCoins | 6 | 101 | 1455/1456 | 0/0 | 6 | 8/0 |
| Averaging | 7 | 3 | 38/38 | 0/0 | 6 | 30/0 |
| AveragingExtra | 3 | 9 | 50/50 | 0/0 | 6 | 7/0 |
| Statistics | 2 | 102 | 1455/1456 | 0/0 | 6 | 18/0 |
| Experiment | 23 | 107 | 1462/1463 | 0/0 | 6 | 38/2 |
| Advice | 12 | 67 | 911/912 | 0/0 | 6 | 34/0 |
| Blocks | 2 | 0 | 0/0 | 0/0 | 0 | 31/0 |
| Closing | 4 | 78 | 1057/1058 | 0/0 | 6 | 12/0 |
| InversionProbability | 2 | 108 | 1468/1469 | 0/0 | 6 | 17/0 |
| Machine | 73 | 138 | 1930/1931 | 0/0 | 6 | 46/0 |
| Seed | 6 | 102 | 1456/1457 | 0/0 | 6 | 6/0 |
| MachineSpec | 13 | 148 | 2003/2004 | 0/0 | 6 | 175/5 |
| Nonabort | 1 | 101 | 1455/1456 | 0/0 | 6 | 11/0 |
| Realization | 6 | 156 | 2014/2015 | 0/6 | 6 | 77/8 |
| Lamport | 91 | 163 | 2025/2026 | 0/26 | 6 | 386/32 |
| Auth | 0 | 176 | 2149/2150 | 0/0 | 6 | 0/0 |

All eighteen A seals pass. All 102 controls pass, including 34 sealed negatives with exactly one error each. The 321 stored constants have only subsets of `{propext, Classical.choice, Quot.sound}` as axioms. All 50 scanner candidates were reviewed in their source contexts; none is a forbidden explicit foreign unfold. Blocks has no TCSlib import closure and therefore zero requested definitions and no closure-local control; the other seventeen phases supply the paired controls.

B failures (with `PolyExpr.eval` sealed):

- `TCSlib.Cryptography.Authentication.Signatures.Lamport.Realization`: 6 errors in 1 declarations: `TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine`.
- `TCSlib.Cryptography.Authentication.Signatures.Lamport`: 26 errors in 16 declarations: `TCSlib.Cryptography.Authentication.lamport`, `TCSlib.Cryptography.Authentication.lamportOWF`, `TCSlib.Cryptography.Authentication.lamportOWF_f`, `TCSlib.Cryptography.Authentication.lamportOWF_inLen`, `TCSlib.Cryptography.Authentication.lamportOWF_outLen`, `TCSlib.Cryptography.Authentication.lamport_exists_best_position`, `TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability`, `TCSlib.Cryptography.Authentication.lamport_forgerCodec`, `TCSlib.Cryptography.Authentication.lamport_gen`, `TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_msgLen`, `TCSlib.Cryptography.Authentication.lamport_oneTimeSecure`, `TCSlib.Cryptography.Authentication.lamport_sigLen`, `TCSlib.Cryptography.Authentication.lamport_sign`, `TCSlib.Cryptography.Authentication.lamport_signImpl_expect`, `TCSlib.Cryptography.Authentication.lamport_ver`.

Per-name INSTALL and EOF multisets, actual Name/home identity, original-source maps and hashes, full eligible-set selection (including private definitions and generated matchers), exact runtime import closure, every own axiom row, and control locations were checked against the retained raw evidence. The versioned module-name cache changes only pure reads of a captured immutable environment. Earlier Core-loop/sparse proposals were not adopted; historical attempts and the actual generator bindings are preserved.


Strict B adds PolyExpr.eval to the same sealed request sets. In Realization, the first type conversion failures occur at source146 in the new exists_realization_machine proof: Fin n / Fin(n*n) arguments do not convert to bitSpecAt(var,var.mul var)n domain/range when eval is opaque. The other failures concern the same oracle specification or output-vector widths. These new helper diagnostics are not classified as inherited baseline failures.

In the main file, the first failure is at source499 in lamportOWF: its f accepts Fin n, while the declared FunFamily input expects Fin(PolyExpr.var.eval n). A second width conversion appears at598 in lamport correctness. Later declarations report type/notation/context cascades from the failed declarations, including the target theorem. This strict-B result is not a passing proof of those declarations under opaque eval. The standard A source seal and ordinary native proof remain passing.

Every strict-B failing declaration and all its mapped source error lines:

| File | Declaration | Original source lines |
| --- | --- | --- |
| TCSlib/Cryptography/Authentication/Signatures/Lamport/Realization.lean | TCSlib.Cryptography.Authentication.LamportFill.exists_realization_machine | 146, 153, 174, 177, 179 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport | 598 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF | 499 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_f | 508 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_inLen | 502 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamportOWF_outLen | 505 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_exists_best_position | 876, 881 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgeGame_accept_eq_honestProbability | 826 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_forgerCodec | 766 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_gen | 607 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_loggedSignImpl_expect | 807, 810 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_msgLen | 601 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_oneTimeSecure | 917, 918, 921 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sigLen | 604 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_sign | 610 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_signImpl_expect | 791 |
| TCSlib/Cryptography/Authentication/Signatures/Lamport.lean | TCSlib.Cryptography.Authentication.lamport_ver | 613 |


Full 32 mapped diagnostics with raw result/log links are
[evidence/logs/final18-native-r3/strict-b-failures.json](evidence/logs/final18-native-r3/strict-b-failures.json).
The independent aggregate and scan dispositions are
[evidence/audits/final18-peer-completion-r1/summary.json](evidence/audits/final18-peer-completion-r1/summary.json)
and [explicit-unfold-review-summary.json](evidence/audits/final18-peer-completion-r1/explicit-unfold-review-summary.json).
There are 1,052 scan token readings, 50 reviewed candidates, and zero forbidden explicit
foreign unfolds. Full selection covers private definitions, generated matchers/projections,
actual names/homes and exact runtime import closure. All 138 source/control probe byte
strings were independently regenerated; 703 referenced raw artifacts were checked present
and hashed.

The first four final phases retain their original successful probes/tool bindings. The
remaining fourteen use a versioned, qualified pure cache of the imported module-name array
from the same captured immutable environment. Attribute commands, local scope, validations,
request sets, controls and EOF checks are unchanged. Qualification reran full Planted A/B
and all six controls; cached census output was byte-identical for all9,103 catalog rows,
67 axiom rows and closure/END markers. Queue version maps and actual-generator provenance
separate adopted and cached attempts. The Core-loop and sparse alternatives were not adopted.

Historical failed native attempts, the checkpoint-2 local-attribute idempotency failure,
its repair and all strict-B diagnostics remain preserved. The original checkpoint-2 A
had three attribute-command errors, not a codec proof failure; B had25 then22 diagnostics
across the same sixteen main declarations listed above. Earlier 252ec inventory preparations
were never run and are labeled historical. No failed sealed check is replaced by an
unsealed pass and no raw evidence is omitted for size.

## Payload and delivery

This payload contains `REPORT.md`, all six issue-base-to-final format patches, all eighteen
changed/new source files, and complete raw evidence with `evidence/SHA256SUMS`. The root
`SHA256SUMS` covers the complete payload. The freezing tool checks exact path-set equality
and every hash, verifies an identical frozen snapshot and ZIP, and verifies every ZIP entry.
The fallback ZIP has `lamport/` at its root.

Delivery is only under `inbox/fills/lamport/` on `exchange/pass-shelat-ch5-8`, with pull/rebase
before pushing and no force push. The final exchange commit and verified fallback ZIP are
returned in chat. The proof branch remains local. Campaign integration is for maintainer
review and a PR Seyoon approves; this worker does not merge the campaign branch.
