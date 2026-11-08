# Construction-core statement phase

Frozen Lean/root: `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`.
Audited dependency: `0769cba3e44c56700349f954190fc99d9e622270` (PR #236).
Draft branch: `cryptography/lwe-sis-phase1-statements`.
PR target: **`cryptography/lwe-sis-constructions`**, the user's central integration branch.

## Scope and status

Eight mathematical modules state the next construction slice:

| Modules under `TCSlib/Cryptography/` | Trusted surface to review |
|---|---|
| `LWE/SampleSchedules` | Replace only the sample count; preserve fixed-sample `DLWEAssumption`; expose the multi-message row count |
| `Encoding/ModularDecode` | Canonical vector/matrix parsers, rejection rules and two-way round-trip statements |
| `LWE/BitEncoding` | Codepoints, Mathlib-based circular distance, nearest-codepoint decoding and strict bounded-error correctness |
| `Encryption/Symmetric/Regev/{Basic,Experiments}` | Direct batched Regev encryption, perfect mathematical correctness and the two-DLWE concrete bound |
| `Hashing/SIS/{Basic,Experiments,Profiles}` | Binary matrix hashing, integer collision reduction, concrete probability bound, compression and a dyadic profile |

This is a statement phase: **31 named theorem bodies are admitted**. No nontrivial
proof fill has started. The existing `PrivateKeyScheme`, adaptive CPA and prospective
CRH-owner bridges are not implemented, and no efficient sampler or construction-security
endpoint is claimed. All five headline constructions remain the campaign's scope.

The sample wrapper supplies no amplification theorem. A future all-polynomial
multi-message result needs an explicit outer hardness quantifier over the required
sample schedules. The scalar error law remains the actual finite-seed law.
The SIS profile supplies arithmetic conditions and existence statements, with no
hardness conclusion or LWE–SIS bridge. No lattice-basis trapdoor is introduced.

## Interface and verification accounting

* New source: 62 public declarations, comprising 17 definitions and 45 theorems.
  Of those theorems, 31 are explicit admissions and 14 are defining/rejection/readout equations.
* New elaborated constants: 90 = 62 source declarations + 23 generated non-simp
  reading lemmas + 5 compiler proof auxiliaries. No private or unexplained constant
  and no axiom-kind declaration is introduced.
* Forty-six new constants depend on `sorryAx`: the 31 admitted statements, the two
  profile constructors, their nine readers and four generated constructor proofs.
  All other axiom dependencies are standard. This is not a zero-sorry theorem claim.
* All 166 foundation constants and their axiom sets agree with the earlier proof
  record and still use only standard axioms. Sixty of the earlier 63 frozen files
  are byte-identical; the exceptions are the root and two facade export files.
* Fresh serial dependency sweep: 68 modules, 176.591 seconds, zero errors,
  31 new admission warnings and the same 17 inherited warnings. All final source
  hashes match the frozen source, including after the private-history adjustment.
* Final probe: exit zero, all 62 source axiom prints and all 256 owned-module
  constants reconciled. Only standard axioms and the inventoried `sorryAx` occur.
* Style: 0 FAIL, 2 WARN over 18 mathematical files. The warnings are the unchanged
  assumption-acronym heuristic cases accepted by both foundation audits.

The five scoped facade roots and all their TCSlib imports were checked. The full
`TCSlib.lean` root was not elaborated. Native execution and physical package isolation
are maintainer attestations with logs; an external static audit is not a native rerun.

The initial parser namespace and bit-codepoint coercion errors were corrected before
the source freeze. An initial inventory probe failed because its temporary census
omitted inner namespaces; the final census reuses the existing comment-aware invariant
checker and prints the correct 62 distinct names. Development logs are retained and
are not the passing sweep/probe evidence.

## Reuse and resources

The parsers reuse the audited encoders and numeral API, with the matrix parser built
through the vector parser and public finite-product equivalence. Bit distance uses
`ZMod.valMinAbs` and its public lemmas. No private machine host, copied proved
infrastructure, new generic cryptographic interface, shared linter change or unsafe
proof mechanism was added. Two authorized internal agents performed read-only design
and source reviews; root alone wrote and checked this slice. Their feedback is internal
review data, not an external gate.

The new worktree has an isolated APFS clone of this chat's own pinned package setup.
No TCSlib olean was copied; the final tree started fresh. The 56 precise Mathlib roots
were already among that setup's selected official archives. No new archive was fetched,
no package pin changed, and no other chat's packages/scratch objects were touched.
Native jobs were serial and their owned PIDs recorded. No `lake build` or unfiltered
cache command was run; Python commands use `python3 -I`.

## Sources and remaining obligations

Exact primary Pei16 and Wu24 PDFs were downloaded over HTTPS, rehashed locally and
text-extracted to check their version headers and construction anchors. The provenance
record gives URLs, byte sizes, SHA-256 values and one-based PDF pages. Source PDFs
remain in the own local archive; the text review bundle carries provenance and links,
not a claim of completed reference ingestion. No registry, dataset or proofmatch output
was changed. N01's ingestion/approved-matching work remains open.

N02 retains scoped native/integration limits and the 17 inherited warnings. N03's
honest samplers, actual-law implementation, useful profiles, machine adapters and
required sample quantifiers remain consumer obligations. This slice states some of
their mathematical prerequisites; none is silently declared discharged by an admission.

## Branches and shared files

The user changed integration routing to the central LWE/SIS branch. The unpublished
draft's two code/export commits were replayed onto PR #236's audited head, removing
unrelated campaign-record ancestry without changing any checked Lean/pin byte. Planning
records were brought into this draft; their former branch is inactive.

The eight new math modules are in commit `56cabe7f3`; exports are isolated in
`a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`. The only existing-file Lean changes
relative to the audited dependency are:

* `TCSlib.lean`: two imports, `Cryptography.Encryption` and `Cryptography.Hashing`.
* `TCSlib/Cryptography/Encoding.lean`: one child import and contents entry.
* `TCSlib/Cryptography/LWE.lean`: two child imports and contents entries.

No existing owner definition/theorem/API changed. Until the user merges PR #236 into
the central branch, the new draft also includes that audited dependency's diff. The
publication helper retargets #236 and creates/updates this draft against the central
branch; it never pushes to the central or Pass–Shelat campaign ref and never merges.
Connector mutation remains HTTP 403; no new PR publication or external dispatch is
claimed until the client command succeeds. The user selects and dispatches the reviewer.

**Not yet clear to merge — the construction statements await external review;
source ingestion/matching, later proof fills and user-approved integration remain open.**
