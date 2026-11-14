# ext-nosrc · checkpoint 3

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`. Local branch: `fill/ext-nosrc` (never pushed).
Local proof head: `7aa5cf513f964ddfe32c1282673329f2187b42fc`. Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.

## Status

The frozen theorem is now proved, with no statement change. The complete owned module passed
Lean. Its axioms are exactly Classical.choice, Quot.sound and propext; the same holds for all
108 stored constants in the three proof modules. Checkpoints 1 and 2 are complete. The exact
acceptance law `1−(1−q)^11` and `q≥1/4` yield the final contradiction.

This checkpoint is not the final validated delivery. Both base Extraction whole-file seals
passed. All eleven final controls passed their expected outcomes. Six final proof-file seals,
the 203-module sweep/admission comparison and additional facade seals remain queued, because
the user explicitly confirmed a limit of three Lean jobs across the whole Mac and other chats
have continuously occupied at least three slots. The worker is not exceeding that limit.

The required lint initially reported two missing direct helper imports in the frozen facade.
The user explicitly approved exactly those two imports. They are applied and committed in
this checkpoint, with approval and the exact patch recorded under evidence/scope-request/.
The approved lint run has 216 pre-existing FAIL findings, identical to base: zero new FAIL.

The three-patch series was replayed at the pinned base and reproduced all four delivered
source files byte-for-byte. The independent frozen-surface review and census-backed explicit
unfold scan pass; the latter has zero foreign definition rule heads across92 argument lists.

## Files and declarations

Changed: `TCSlib/Cryptography/Randomness/Extraction.lean`, plus exactly two user-approved direct imports in `TCSlib/Cryptography/Randomness.lean`.
New: `TCSlib/Cryptography/Randomness/Extraction/Rejection.lean` and `Extraction/Sampler.lean`.
The patch and `src/` carry their exact committed bytes. The target statement is unchanged.
New declarations are visible in those sources; probability helper promotions and searches are
listed in `evidence/rejection-review.md`. No private foreign proof was copied or re-derived.
`uniform_one_probTrue` is a promotion request to the finite-probability layer.
No foreign reader request is currently needed. The module title/status and target proof sketch describe the delivered proof; Contents lists both helpers. Every other original declaration and statement prose is unchanged.

## Environment and checks

Preflight is in `evidence/logs/preflight.log`: Darwin/macOS, 12 logical CPUs, 18 GiB physical
memory, native memory-pressure estimate 8,890,582,302 available bytes, APFS with
273,209,647,104 available bytes. Linux nproc, cgroups/proc and GNU df flags do not exist here;
the log records the failed Linux queries and native sysctl/vm_stat/memory_pressure/statvfs/mount
measurements. No memory-backed scratch or dependency-tree reuse was used.

The user overrode the one-host concurrency rule: unlimited initially, then at most three Lean
jobs after 20 minutes (06:02 UTC). This fill keeps its own olean tree sequential.
All 201 source hashes and all seven pack hashes passed. All present packages match the pinned
manifest; doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean are ABSENT and are not imported by the
issued order. The narrowed 80-root fetch exited 0, with no download failures: no files needed
downloading; 2,125 files decompressed. The shared cache store already held 32,667 files,
1,595,387,830 bytes, of unverified earlier origin. These were not downloaded by this session.
Zero-length olean scan was empty; a probe importing the first issued Mathlib root passed.

The initial bootstrap checked 32 prerequisites successfully, then caught draft helper errors.
The corrected helper check and owned-module checkpoint-one check exited 0. A further 43 prerequisites and the rejection machine were checked; its draft errors were corrected. The machine and complete checkpoint-two assembly then exited 0. The first base census attempt exposed a collector keyword error, preserved verbatim for repair; no dependent seal was run from that failed census. Raw failed
attempts and successful rechecks are included. Every module invocation uses
`scripts/lean_check_tree.sh`, one module at a time, with timestamps and maximum resident memory.
No lake build or unfiltered cache fetch was run.

The all-stored-constant axioms, controls, explicit scan and no-new-FAIL lint comparison are complete. Final whole-file seals, full203-module sweep, admission comparison and additional facade coverage remain pending. No success is claimed for those pending checks.

## Evidence

`evidence/SHA256SUMS` covers exactly all evidence files except itself. The root SHA256SUMS
covers the complete checkpoint payload except itself. Logs were copied as a completed
checkpoint snapshot as a snapshot while the final driver waits for a host-wide concurrency slot. All named paths are delivered.
