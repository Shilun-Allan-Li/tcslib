# ext-nosrc · checkpoint 1

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`. Local branch: `fill/ext-nosrc` (never pushed).
Local proof head: `e0b0d2265434219da031e81deb30f8ae18a4c1ad`. Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.

## Status

Checkpoint 1 is proved and module-checked. The target remains admitted, with the extractor
assumption introduced and the proved `uniform_acceptance_lower` bound available.
This is an intermediate delivery, not a completed proof.

The uniform PPT returns its `n` coins, its law is `U_n`, and `U_n` is an `(n−2)`-source.
Its extractor closeness implies `q ≥ 1/4`. A separate checked probability helper proves the
finite rejection law, its acceptance probability, explicit uniform/flat mixture, and preservation
of source bounds. The machine implementation and final assembly remain to be checked.

## Files and declarations

Changed: `TCSlib/Cryptography/Randomness/Extraction.lean`.
New: `TCSlib/Cryptography/Randomness/Extraction/Rejection.lean`.
The patch and `src/` carry their exact committed bytes. The target statement is unchanged.
New declarations are visible in those sources; probability helper promotions and searches are
listed in `evidence/rejection-review.md`. No private foreign proof was copied or re-derived.
`uniform_one_probTrue` is a promotion request to the finite-probability layer.
No foreign reader request is currently needed. The original target sketch is unchanged so far.

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
The corrected helper check and the owned-module checkpoint check both exited 0. Raw failed
attempts and successful rechecks are included. Every module invocation uses
`scripts/lean_check_tree.sh`, one module at a time, with timestamps and maximum resident memory.
No lake build or unfiltered cache fetch was run.

The final 201-module sweep, admission comparison, all-stored-constant axioms, both whole-file
seal variants at base/final, paired controls, explicit scan and style-lint comparison remain
pending. No success is claimed for those final requirements at this checkpoint.

## Evidence

`evidence/SHA256SUMS` covers exactly all evidence files except itself. The root SHA256SUMS
covers the complete checkpoint payload except itself. Logs were copied as a completed
checkpoint snapshot before further bootstrap work. All named paths are delivered.
