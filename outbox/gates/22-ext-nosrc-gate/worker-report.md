# ext-nosrc · final delivery

The frozen `TCSlib.Cryptography.Randomness.not_isExtractor_effSources` is proved. The complete
owned module and all required checks pass. The only admission removed is the target.

## Provenance and scope

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` on `cryptography/pass-shelat-ch2-4`.
Local proof branch: `fill/ext-nosrc`, head `7aa5cf513f964ddfe32c1282673329f2187b42fc`. It has never been pushed.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`; all seven pack checksums and
all 201 issued source hashes passed. Lean pin: 4.25.0. Mathlib pin:
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

Only the owned Extraction module and its two permitted helper modules were initially edited.
The required lint exposed two direct-import findings in frozen `Randomness.lean`. Seyoon
explicitly approved exactly those two imports in this chat. The approval, exact two-line patch,
original findings and successful overlay are preserved under `evidence/scope-request/`.
No other frozen source file is changed. All original non-target declarations and their prose,
the target signature/statement prose and global simp attributes are preserved.

| Changed or new source | Lines |
|---|---:|
| `TCSlib/Cryptography/Randomness.lean` | 40 |
| `TCSlib/Cryptography/Randomness/Extraction.lean` | 322 |
| `TCSlib/Cryptography/Randomness/Extraction/Rejection.lean` | 481 |
| `TCSlib/Cryptography/Randomness/Extraction/Sampler.lean` | 216 |

## Proof and sketch changes

At the fixed parameter n, the uniform PPT outputs its n coin bits. Its law is U_n, an n-source
and hence an (n−2)-source. Assuming extraction yields q≥1/4 for the first output bit on U_n.
The uniform rejection machine uses exactly 11n coins: ten independent n-bit trial blocks and
an eleventh fallback. Ten applications of the published polynomial-time conditional combinator
prove efficiency. Its constant coin polynomial is legitimate because the witness is chosen
after fixing n; it has empty advice at every activation parameter.

A generic finite-law calculation identifies its distribution with
`(1−q)^10 U_n + (1−(1−q)^10) flat(S)`. Uniform is an (n−2)-source. Each flat-source point has
mass at most `1/(2^n q) ≤ 4/2^n = 2^(-(n−2))`, so the flat component is one too. Convex mixtures
preserve that bound. The exact acceptance probability is `1−(1−q)^11`, which is at least
`1−(3/4)^11 > 3/4`, contradicting the assumed quarter-closeness to a fair bit.

The formulas work unchanged for n=0,1,2 and q=1; division is only by positive q, never by 1−q.
An empty extractor output reads false through padFin and is already contradicted by q≥1/4.
The canonical coin/block equivalence proves the exact 11n split, including n=0.

The owned module drops the statement-phase title, updates Main results, adds Contents and
updates sketch step 3 to describe the checked finite conditional construction. The frozen
statement and its mathematical meaning are unchanged.

## Declarations, reuse and promotion requests

The final three proof modules contain 108 stored constants,
versus 10 at base: 98
new stored constants, including compiler-generated definitions. Full names, module ownership
and every axiom set are in `evidence/logs/declaration-inventory.json` and the raw census logs.
The approved facade contains zero stored constants, verified by its separate censuses.

`evidence/rejection-review.md` lists the public probability/expectation, pushforward/product,
tuple, rejection-law and convex-mixture declarations for promotion to the InformationTheory
and sampling layers. `evidence/sampler-review.md` lists the machine/list promotion requests;
in particular `take_poly` belongs in ClassNP/PolyTimePrefix and the bounded sampler interface
can be promoted to a shared sampler layer. `uniform_one_probTrue` is a probability-layer
promotion request, and `uniform_card_div_quarter` is a bit-source entropy arithmetic request.
The target-specific membership and machine-law bridges stay with Extraction. The complete
uniform-machine family and an existing block-reader relocation request are also listed in
`evidence/promotion-requests.md`, which consolidates all promotion requests.

Searches are recorded in those reviews and `evidence/logs/rejection-duplication-search.log`.
Public lemmas/readers were imported and used. **Overlap: none.** No private foreign proof was
copied or re-derived from its implementation. No missing-reader request remains.

## Environment and bootstrap

Preflight raw evidence is `evidence/logs/preflight.log`: Darwin/macOS, 12 logical CPUs,
19,327,352,832 physical bytes (18 GiB), native memory-pressure headroom estimate 8,890,582,302
bytes and APFS available space 273,209,647,104 bytes. The 4 GiB memory and 12 GiB disk floors
passed. Linux nproc/proc/cgroups and GNU df flags are unavailable on this host; their failed
queries and native sysctl/vm_stat/memory_pressure/statvfs/mount alternatives are explicit.
All clone, scratch and olean directories are disk-backed. No dependency tree or another
session's object store was copied, merged, moved or reused.

All present packages match the manifest. The package verifier's final line is
`PACKAGES MATCH: all present packages match manifest`. doc-gen4, UnicodeBasic, BibtexQuery and
MD4Lean are ABSENT and are not imported by the issued order. Only the 80 supplied Mathlib roots
were requested. The narrowed cache command exited 0 without failed downloads: no files needed
downloading and 2,125 files decompressed. The shared archive store already contained 32,667
files totaling 1,595,387,830 bytes, of unverified prior origin; these were not downloaded by
this session. The zero-size olean scan was empty and the root-import probe passed.

Bootstrap first checked the owned module's 32 initial prerequisites, then the additional 43
prerequisites for the sampler and the new helpers, always in dependency order. A full 203-module
pass then completed the remaining bootstrap (its historical logs are named sweep). A separate
203-module final sweep follows that completed bootstrap; its logs are named final-sweep. Development
errors and corrected successful rechecks are preserved. No project lake build or unfiltered cache get
was run. The cache tool's expected internal package build is allowed by the addendum. Every module/probe uses scripts/lean_check_tree.sh, one module per invocation, with
start/end time and native maximum-memory output. All Python commands use python3 -I.

Seyoon temporarily overrode host concurrency and then clarified a cap of three Lean jobs
across the whole Mac. The scheduler counts actual Lean executables before launching its one
job. It also honored the authorized reservation for dl-crh's bootstrap, releasing that reservation
after a read-only status confirmed the requesting chat had reached checkpoint packaging. External jobs sometimes
occupied or exceeded the cap, so this fill waited. The scheduler was deliberately restarted at
a completed module boundary to honor the reservation; only its Python controller was signaled,
no Lean check was interrupted. The verified completed prefix and all raw logs were preserved.
See concurrency-override.txt, resource-reservation.json and sweep-scheduler-reservation.log.

## Completed checks

The owned theorem module passed before the final sweep. The completed first full pass was
used as bootstrap, and a separate final sweep ran after all prerequisites existed, satisfying
the addendum sequencing requirement. Both passes have zero errors. The supplied 201-module order plus
two helpers gives 203 successful per-module checks, zero errors. The stable topological order
places Samples before Rejection, then Sampler before Extraction, preserving all supplied
modules and satisfying the new import edges. `admissions-comparison.json` records 21 base
admissions and 20 final admissions: exactly not_isExtractor_effSources removed, none added.
The current facade, including the approved imports, is checked in that sweep.

The target's axioms are exactly `Classical.choice`, `Quot.sound`, `propext`. Every stored
constant in all changed/new files has only a subset of these axioms. The facade's stored set
is empty. The raw censuses, probes, manifests and summaries are included.

Both whole-file seal variants pass for every changed/new file at base where present and at
final. Variant A exempts PolyExpr.eval as notation; variant B seals it. Full foreign TCSlib
import closures include definitions, instances, matchers, splitters and projections. Only
validated actually reducible abbreviation notation is exempted in both variants; semireducible
compiler-generated definitions remain sealed. Every requested name/home and active seal is
verified at installation and EOF. Rejection does not import PolyExpr.eval, so its A/B sets are
both 18 definitions; the other files and the eval controls test the eval distinction. No source
declaration fails any completed whole-file seal.

| Survey | Whole-file seal | Requested definitions | Errors |
|---|---|---:|---:|
| base-r2 | `SealA_Extraction` | 608 | 0 |
| base-r2 | `SealB_Extraction` | 609 | 0 |
| final | `SealA_Extraction` | 1046 | 0 |
| final | `SealB_Extraction` | 1047 | 0 |
| final | `SealA_Rejection` | 18 | 0 |
| final | `SealB_Rejection` | 18 | 0 |
| final | `SealA_Sampler` | 1034 | 0 |
| final | `SealB_Sampler` | 1035 | 0 |
| facade-base | `FacadeSealA` | 3365 | 0 |
| facade-base | `FacadeSealB` | 3366 | 0 |
| facade-final | `FacadeSealA` | 3382 | 0 |
| facade-final | `FacadeSealB` | 3383 | 0 |

The base facade uses the original Extraction snapshot, not its final olean; every other
foreign source is byte-identical to the pinned base. Both facade censuses explicitly verify
zero stored constants. Its controls reuse hash-verified matching sources/logs/results from
the completed control surveys. Every paired negative control passes unsealed and fails
exactly once sealed. The eval control passes in A and fails exactly once in B; reader controls
pass under both variants. Invalid early collector/preparation attempts are retained separately, including the quoted
snapshot-header parser repair used for the facade;
no dependent Lean seal was run against a failed census.

The census-backed explicit scan finds zero foreign-definition tactic rule heads across 92
argument lists. Its five nested lexical matches are ordinary theorem parameters or local
name shadowing, reviewed explicitly. Source scans and whole-file seals provide independent
evidence; lexical limitations are documented. The facade has imports only, no tactic bodies.

Required command: `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`.
Base and approved final each have 216 existing FAIL findings and 102 WARN: **zero new FAIL**.
The raw initial two-finding regression and the approved repair are both preserved.

The complete three-patch series replays at the issue base and reproduces all four src files
byte-for-byte (`patch-reproduction.log`). Full-library landing checks under TCSlib and
audits/pass-shelat/Checks remain the maintainer's landing step, as specified by the brief.

## Delivery and evidence completeness

Checkpoint 1: a0c36ef90. Checkpoint 2: dfec1f17d. Checkpoint 3: a2c2e1b2c. The final delivery
changes only inbox/fills/ext-nosrc on the exchange; every push is preceded by pull --rebase and
no force push is used. A checkpoint push race was resolved by rebasing and retrying.
The campaign proof branch stays local; maintainer landing is through a PR for Seyoon's approval.

patches contains the entire format-patch series from the pinned base; src contains its exact
final files. evidence contains every tool, probe/control/seal source, request/import manifest,
raw log and results.jsonl named by its SHA256SUMS. All development failures and successful
repairs are retained. The payload verifier checks that manifest paths are exactly delivered
paths and every digest matches. The chat ZIP has ext-nosrc/ at its root and the same payload.
