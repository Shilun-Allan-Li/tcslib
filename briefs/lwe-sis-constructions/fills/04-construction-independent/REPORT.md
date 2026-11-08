# Independent construction proof report

Thirty-one audited obligations are now proved in seven modules at
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a`, on existing draft PR #250's branch,
`cryptography/lwe-sis-construction-statements`. Seventy other owned obligations
remain admitted. This is a partial proof gate above the passed combined statement
surface, not full primitive-security completion or merge approval.

## Audit intake and freeze

The combined statement review passes 0/0/1/4 at source
`17b2a282b545c6ebca3fccc88d518d18ae78f485`, records
`03f13bc817f4d281801e2025d3722bcab513c6c0`, exchange
`64e245b345d908d835030efede1c91312a4e6cce`. The sole minor F01 correctly
identified missed registration wording in BooleanVector. Its separate comment
repair is `f1b75a7d17dc7ef5fddd7403a2d7c740ba365c9c`, checked with identical
comment-stripped source and a passing per-module/style check. The proof baseline
including intake is `13aff4d33d282ccaed2727af3febc0ebddeba0e5`.

All 220 ordered source declarations, 62 earlier closed `rfl` readers, definition
bodies, signatures, imports, options, namespaces and attributes remain fixed.
Exactly 31 former `by sorry` bodies change. All seventy other admissions and all
non-owned frozen paths match the baseline. There is no new handwritten helper,
host, instance, exported declaration or copied proved infrastructure. Mathematical
code changes are limited to seven existing owned modules. The earlier six export
overlaps remain in their separate statement export commit; this fill adds none.
No shared API, registry, pin, other campaign record or checkout is modified.

## Completed mathematics

| Module under `TCSlib/Cryptography/` | Filled proofs | Main argument |
|---|---:|---|
| `Encoding/DyadicUniform` | 9 | Public canonical numeral recovery, coordinatewise bijections and finite-bijection sums give exact dyadic laws and ordered bit recovery. |
| `LWE/BitNoise` | 4 | Exact seed preimage counts, bounded integer bit counts, a complement involution and independent coordinate relabeling prove the actual noise properties. |
| `LWE/Sampling` | 3 | Matrix/secret product equivalences retain every noise seed; public pushforward/averaging equations preserve independently randomized tests. |
| `Encryption/PublicKey/Regev/Basic` | 4 | Public dot-product/matrix algebra preserves the original integer residual; the public subadditive-sum bound and decoder give every-coin correctness. |
| `Pseudorandom/Generators/LWE/Basic` | 5 | Existing advantage readers, the conditional DLWE assumption and exact full entropy budgets give the basic generator results. |
| `Pseudorandom/Generators/LWE/Bits` | 3 | Faithful encoder injectivity plus output cardinality gives the concrete full-word bijection; real-law and ideal-word relabelings preserve all test coins. |
| `Pseudorandom/Generators/LWE/Flat` | 3 | Existing explicit bit equivalences relabel seeds/outputs, retaining the full seed cost and stated endian convention. |
| **Total** | **31** | **Every selected target is standard-axiom only.** |

Five sketches are adjusted to describe the final public-API routes: bitwise
complementation, single-coordinate averaging, the matrix/dot-product identity,
the averaged-pushforward acceptance equation, and the faithful encoder/cardinality
argument. Completed-module overviews are updated. No proposition or definition
is changed by these prose updates. No foreign definition is named for unfolding;
local proof lets and permitted core/Mathlib `change`/`rfl` reductions are used.

The uniform-law proofs each apply the existing finite-bijection sum contract;
they introduce no local general pushforward theorem or new host. The mean uses
a different coordinate argument rather than copying the complementation proof.
The generator's proof-local encoder equivalence does not change its program into
an arbitrary-choice construction. No new machine implementation is asserted.

## Final native and inventory evidence

`evidence/final-sweep/` records the exact seven-facade, 144-module dependency
closure in a newly empty `.lake/construction-independent-final-oleans` tree.
All modules pass serially through `scripts/lean_check_tree.sh`: zero errors,
seventy owned and seventeen inherited admission warnings, **303.792 seconds**.
The separate final axiom probe passes with fresh output in **53.149 seconds**.
This does not elaborate the whole library root.

All 220 source and 48 selected backing-contract axiom prints agree with the raw
environment walk. The inventory is:

| Category | Count |
|---|---:|
| Earlier audited foundation/core/adapter/scalar constants | 302 |
| Combined statement source declarations | 220 |
| Original generated non-simp projection readers | 40 |
| Original compiler auxiliaries | 13 |
| New compiler auxiliaries | 14 |
| **Total owned constants** | **589** |

Exactly seventy source obligations retain `sorryAx`. The other 519 constants,
all 31 selected targets and all 48 backing contracts use only `propext`,
`Classical.choice` and `Quot.sound`. All prior kinds/visibilities remain fixed;
all prior axiom sets remain fixed except those of the 31 filled targets.

Two old compiler helpers, `DyadicUniform.bitsToVector.congr_simp` and
`DyadicUniform.bitsToMatrix.congr_simp`, now originate in DyadicUniform rather
than the later Sampling module because a filled owner-module proof first needs
them. Their names, kinds, visibilities, axiom sets and exact elaborated types
remain fixed. All other 573 prior module origins are unchanged. This exception
is recorded explicitly in `compiler-origin-changes.json`, not hidden under an
all-origins-preserved claim. No handwritten declaration moves.

The inventory discrepancy prompted two supplemental native type probes. Exact
`reprStr` values of the level parameters and elaborated type expressions compare
equal for all 575 prior owned names. Raw baseline/current logs and SHA-256 rows
are retained. Probe times are 29.137 and 33.949 seconds. The baseline loads an own
copy of this chat's archived audited statement objects; that historical revision
is not independently rebuilt. These are scoped imported-environment checks, not
a whole-library type certificate or an external native rerun.

All eight scoped style checks reproduce **0 FAIL / 2 unchanged WARN over 41 files**.
The complete native logs additionally contain 144 non-admission warnings whose
messages match the statement baseline exactly, recorded separately from admission
counts; no new proof diagnostic is disguised as an inherited warning.

## Development, isolation and remaining scope

Thirteen numbered development runs preserve exact source snapshots, failures
and passing outcomes separately from final evidence. Corrections include the
Matrix function-space cardinality reading, unavailable append-equivalence candidate,
natural-number scalar cast, public noise seed-type reading and local length aliases.
The first internal import walk incorrectly included documentation examples; the
comment-aware correction identified the real import closure. No frozen import was
changed and no unavailable Mathlib construction was copied into the source.
Both internal agents did read-only research; root alone edited and checked code.

Development objects are a copy of this same chat's own statement final tree.
Final TCSlib objects start empty. Packages remain the own pinned copies; no new
Mathlib root/cache fetch, package change, foreign scratch object, native parallel
job or PID kill occurs. All fifteen manifest pins remain fixed. Physical package/
cache provenance, isolation and freshness remain maintainer attestations. Global
process inspection is unavailable; no absence of other chats' jobs is claimed.
Earlier finite models are retained, not rerun for unchanged definitions.

The statement report archive preserves the complete text returned by its
authoritative read, without editing: 13,818 bytes, while native metadata reports
13,819. Raw download failed; original-file byte identity is explicitly unverified
and no missing byte is guessed. The intake receipt records this distinction and
the exact retained text hash. Earlier issued reports, packs and evidence remain
unchanged.

N01 primary validation/ingestion/approved matching, N02 execution/landing limits
and N03 final primitive consumers remain. N04 pauses the affected random-bit and
probability-reader routes and counted-loop registry/host-gate consumers, with any
head-envelope requirement retained. Exact proposals remain unapplied. Seventy
remaining admissions include later independent work as well as held routes.
No all-but-one inverse, strong one-time signature, final CCA2 game, exact-seed
asymptotic PRG compiler, efficient family sampler, SIS–LWE bridge or lattice-basis
trapdoor is completed here. The user still controls audit dispatch and merging.

**Not yet clear to merge — these 31 fills need their combined proof audit;
seventy remaining admissions, shared-owner dispositions, source-policy work,
landing checks and user approval remain.**
