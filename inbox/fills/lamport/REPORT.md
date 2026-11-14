# Lamport fill — checkpoint 1

Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
Issued exchange pack: `b436d19a0310265b214447ea6710deba32df6dd8`.
Local proof head: `09ac6b6c8c7f5997928ee5dfb4f18984ba2709b5` on `fill/lamport`; that branch is not pushed.

**Status:** the planted experiment and its pointwise honest-run coupling are proved.
The generator, signer, and verifier are connected to the typed table model by checked
equations. `Authentication.lamport_oneTimeSecure` itself is still admitted. This is an
intermediate checkpoint, not a final proof delivery.

## Delivered mathematics

The table has an independent `n`-bit preimage at each `(i,c)`. The reduction plants a
challenge image in one public cell, answers safe queries from its sampled table, remembers
unsafe queries with an abort bit, and extracts the forged signature's selected block.
`planted_coupling` proves exact simulation agreement on safe cost-at-most-one trees.
`favorable_extraction` proves inversion on an accepting run selecting the planted bit.
The complete planted experiment is invariant under changing its unused secret cell.

`honest_transcript` also exposes the empty or singleton honest query log and proves that
freshness is equivalent to the first query differing from the forged message. The actual
signing oracle's sampling node must still be bridged at the expectation level; that bridge,
the averaged bound and best-position choice, and the T1 machine/negligibility conclusion
remain for checkpoints 2 and final.

The owned module now proves `runAt_lamportGen_table`, `runAt_lamportSign_table`, and
`lamportVerFun_publicWord_iff`. Thus the typed table model is linked to the actual algorithms,
rather than assuming their intended behavior. The existing security statement, proof sketch,
other declarations and global simp attributes have been preserved.

## Files and declarations

The proof patch changes the owned `TCSlib/Cryptography/Authentication/Signatures/Lamport.lean`
and adds `Lamport/Encoding.lean`, `Lamport/Planted.lean`, and `Lamport/TableCoins.lean`.
The user additionally authorized import-only registrations in the otherwise frozen
`TCSlib/Cryptography/Authentication.lean`: “Allow the required facade imports”.
That second patch adds exactly three imports, resolving the lint scope conflict; the
request, proposed patch, and authorization are in evidence/requests/.
The owned module imports these helpers precisely and lists them in its Contents section. Every file is below 1000 lines.
`evidence/new-declarations-checkpoint1.json` lists the new public declarations.

The module title and final main-result status will be updated when the target is proved.
No statement was weakened, no axiom was added, and no new helper contains `sorry`.

## Promotion, readers, duplication

Promotion requests: tuple-encoding injectivity and its finite-tuple form; the generic
cost-zero computation lemma; the tape/table serialization equivalence. The planting,
one-query transcript and extraction facts are Lamport-specific.
No missing foreign reader or mathematical route failure has been found.

**overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.
The private two-block word identity is re-derived inside the general table serialization
proof from the published `FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`.
Its private proof was not copied. Searches for cryptographic `encodeList` injectivity
found no public provider; the new proof uses `encodeList_nil`, `encodeList_cons`,
`pairEncode_ne_nil` and `pairEncode_injective`. New probability work consumes the existing
coordinate-resampling and product-sampling lemmas; no copy of those lemmas is delivered.

## Environment and bootstrap

The pack's seven manifest entries verify, and all issued source hashes matched before
editing. This is Lean 4.25.0 with the issue manifest's Mathlib revision
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

This host runs macOS. `nproc`, Linux cgroups, `/proc/meminfo`, GNU `df -B1` and `df -T`
are unavailable. The raw failures and native equivalents are retained in preflight.log.
Native measurements report 12 CPUs, 19,327,352,832 physical-memory bytes, and a
memory_pressure available estimate of 8,697,308,774 bytes (45%), above the 4 GiB floor.
The initial APFS free-space measurements were 276,725,379,072 bytes and then
273,175,490,560 bytes, above the 12 GiB floor. This is a native available-memory estimate,
not a claim to have read Linux MemAvailable.

Only the 82 issued Mathlib roots were fetched. The regenerated root list is identical.
The preexisting host cache held 32,667 files / 1,595,387,830 bytes; its origin beyond
being preexisting on this host is unknown. The cache tool downloaded no files and
unpacked 2,339 existing archives. Every present package matches the manifest; doc-gen4,
UnicodeBasic, BibtexQuery and MD4Lean are ABSENT documentation packages. No empty olean
was found. The Mathlib-import cache probe passed.

The first timing attempts were blocked by macOS sysctl sandbox permissions; the Lean
cache probe produced a fresh olean, and the checks were rerun successfully with native
resource timing permitted. These were instrumentation failures, not cache corruption.

The supplied 150-module baseline was bootstrapped one module per lean_check_tree.sh
invocation, with one Lean process at a time. T1 needs nine additional modules not listed
in the issued order; these and Bridges.Experiments were then bootstrapped, with no new
Mathlib roots. A premature QueryTree check exposed one missing supplied downstream
prerequisite; that raw attempt is retained and is not reported as a library finding.
No lake build, unfiltered cache fetch, copied dependency tree, or memory-backed scratch
filesystem was used. Python commands use python3 -I. The separate exchange checkout
is transport-only and contains no dependency cache.

## Checks and evidence status

Encoding-03, Planted-04, TableCoins-01 and Lamport-03 pass. The only diagnostic in the
owned module is the unchanged target's sorry warning. All failed attempts and their
source snapshots are retained. A subsequent docstring-only amendment added the Contents
list; the checked proof text is unchanged. The patch series reproduces all five delivered source
files byte-for-byte from the issue base.

The baseline stored-constant/axiom inventory and whole-file A/B seals, request records,
paired controls and tools are delivered under evidence. A excludes PolyExpr.eval as
notation; B includes it. Seal results are recorded in the raw results/summary files;
the checkpoint does not substitute an unsealed check for a sealed one. Final-file seals,
the final axiom census, the final supplied-order sweep, the final sorry comparison and
whole-Cryptography lint comparison remain required before final delivery.

The generic finite counting helper was separately checked during preparation; its raw
attempt sources are retained as evidence, but it is not yet in this checkpoint's proof
patch. Every file named by evidence/SHA256SUMS is included, and the manifest's path set
is checked before publishing.


Baseline seal A passed with zero errors. Baseline seal B had 15 diagnostics in the
following 11 declarations, beginning with the definition-level `PolyExpr.var.eval n`
versus `n` mismatch in `lamportOWF` and `lamport`, followed by dependent cascades:

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


All six paired base controls pass: both unsealed controls and both reader controls
compile; each sealed negative fails exactly once at its designated source line.
All eight base probes completed with valid INSTALL/EOF coverage. The authorized-facade
lint comparison has 0 new FAIL (216 inherited FAIL at both base and checkpoint).
The earlier lint logs retain the initial draft-only registration failures and the three
real frozen-facade failures; they are superseded by lint-authorized-comparison.json.

The authorized authentication facade also checks successfully (Authentication-01).
The baseline admission census found exactly 22 sorry declarations, matching the issued total.
