# Combined construction statement report

The user authorized this larger statement draft on 2026-11-08, after the dyadic
scalar proof audit passed. Its 19 mathematical modules contain 220 source
declarations: 57 definitions, 163 theorems, 62 closed `rfl` readers and **101
admitted proof obligations**. No nontrivial construction proof has been filled.
The user preselected Codex for the morning audit and retains dispatch and merge
control. This report records preparation, not an audit verdict or publication.

## Frozen identity and ownership

| Item | Identity |
|---|---|
| Worktree | `tcslib-lwe-sis-construction-statements` |
| Branch | `cryptography/lwe-sis-construction-statements` |
| PR target | `cryptography/lwe-sis-constructions` |
| Remote-verified central base | `2c37f3f486822a52f4a9e337c6b742e995ebb118` |
| Audited stack plus scalar-audit intake | `307cfdd1d6cadfda2ae9cca5367705ad770c5f42` |
| Mathematical commit | `2bf9dd52882bcafbce9eab48a5bab796275f2094` |
| Separate exports / frozen Lean and root | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Audited dependency PRs | #236, #237, #238, #239 |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

The complete library-tree comparison records 25 added Lean files: 19 mathematics
files and six new facades. Six existing files change only export wiring:
`TCSlib.lean`, `Cryptography/Encoding.lean`, `LWE.lean`, `Encryption.lean`,
`Hashing/SIS.lean` and `Pseudorandom.lean`. These changes occupy the separate
export commit. Every other existing library Lean file remains identical to the
stack baseline. No old mathematical definition, theorem, owner API, pin or registry
is edited. The Pass–Shelat, Arora–Barak and shared exchange checkouts are untouched.

## Mathematical surface

Paths below are relative to `TCSlib/Cryptography/`. Full names, bodies, attributes
and admitted targets are attached; the counts below count source declarations.

| Module | Declarations | Admissions |
|---|---:|---:|
| `Encoding/DyadicUniform` | 15 | 9 |
| `LWE/BitNoise` | 13 | 4 |
| `LWE/Sampling` | 7 | 3 |
| `Encoding/DyadicLinearAlgebra` | 24 | 14 |
| `Encoding/BooleanVector` | 10 | 6 |
| `Hashing/SIS/Universality` | 6 | 6 |
| `Hashing/SIS/CollisionOutput` | 14 | 8 |
| `Hashing/SIS/Implementation` | 5 | 3 |
| `Hashing/SIS/Asymptotic` | 4 | 2 |
| `Encryption/PublicKey/Regev/Basic` | 12 | 4 |
| `Encryption/PublicKey/Regev/Experiments` | 19 | 6 |
| `Pseudorandom/Generators/LWE/Basic` | 11 | 5 |
| `Pseudorandom/Generators/LWE/Bits` | 5 | 3 |
| `Pseudorandom/Generators/LWE/Flat` | 15 | 3 |
| `TrapdoorFunctions/Lossy/Gadget` | 14 | 6 |
| `TrapdoorFunctions/Lossy/Matrix` | 18 | 7 |
| `TrapdoorFunctions/Lossy/Experiments` | 12 | 4 |
| `TrapdoorFunctions/AllButOne/AntiCyclic` | 6 | 4 |
| `TrapdoorFunctions/AllButOne/Basic` | 10 | 4 |
| **Total** | **220** | **101** |

Sampling states exact pushforward laws from explicit bits, retaining noise
multiplicities and one common secret. The centered-binomial example has its actual
law, support, symmetry and mean specified. It does not assert an efficient family
sampler merely from a finite noise type.

The arithmetic layer implements dot products, matrix-vector products, Boolean
expansion and signed collision outputs with the existing public counted loop and
proved scalar operations. It states total raw-input size bounds and FP routes as
well as canonical modular equations. The sketches distinguish chunk parsing,
missing bits, leading zeros, malformed pairs and width zero.

SIS work reuses the existing binary matrix hash. Universality uses a differing
binary coordinate with coefficient +1 or -1, including composite moduli. Strong
leftover hashing supplies the PKE statistical bound without a SIS hardness premise.
The raw collision adapter separately preserves integer differences, validates the
output encoding and states negligible collision bounds under the independent
`SISAssumption`. No LWE-to-SIS hardness bridge is asserted.

Regev PKE retains the actual integer error sum through decryption, states perfect
bounded-error correctness for every coin choice, and separates its DLWE hybrid
from the strong leftover-hash term. The public-matrix orientation and common-secret
sample count are explicit. These are concrete algorithms and bounds, not the final
existing CPA primitive/game instantiation.

The generator modules expose structured, MSB-encoded and single-word versions.
Every seed bit is charged, including the public matrix, secret and noise coins.
The flat version uses the existing explicit bit/block equivalences. No efficient
arbitrary-noise sampler, standard exact-seed asymptotic PRG bridge or favorable
stretch is inferred without its displayed hypotheses.

CCA2 support follows the Peikert–Waters secret-matrix route: dyadic rounding and
gadgets, an injective/lossy matrix pair, column-by-column DLWE hybrids, and an
integer anti-cyclic all-but-one construction. The latter states other-branch
injectivity using bounded integer lifting; it does not claim that every nonzero
branch difference is a unit modulo a power of two. No all-but-one inversion
algorithm, strong one-time signature, CCA game sequence or completed CCA2 PKE is
claimed. There is no short lattice basis or Gaussian preimage sampling.

## Execution and inventories

The final evidence is **`evidence/audit-final-sweep/`**, after the projection-reader
refinement. A newly empty `.lake/construction-audit-final-oleans` tree receives a
serial `scripts/lean_check_tree.sh` sweep over the exact 144-module dependency
closure of seven facades. It records zero errors, 101 new and 17 unchanged inherited
admission warnings, and **288.743 seconds** of module time. The subsequent final
axiom probe records **44.702 seconds**, successful fresh output and no errors.
Neither check elaborates the whole `TCSlib.lean` root.

All 220 source axiom prints and 48 separately selected backing contracts reconcile
with the raw probe. The owned inventory is:

| Category | Constants |
|---|---:|
| Earlier constants, exact module/kind/visibility/axioms preserved | 302 |
| New source declarations | 220 |
| Generated non-simp projection readers | 40 |
| New compiler auxiliaries | 13 |
| **Total** | **575** |

Exactly the 101 disclosed source obligations contain `sorryAx`. All other owned
constants and all 48 backing contracts use only `propext`, `Classical.choice` and
`Quot.sound`. The foreign-qualified compiler auxiliary
`ZMod.finEquiv.congr_simp` originates in the new `Generators/LWE/Flat` module;
its axiom set is `propext` and `Quot.sound`. No handwritten helper, new host or
copied proved infrastructure is added. Tooling adapted from this campaign's own
earlier gate helpers is identified in its scripts.

The eight scoped style checks cover 41 files and reproduce **0 FAIL / 2 unchanged
WARN**. The two old acronym-reader warnings remain disclosed. The 153-path source
freeze includes the 144-module closure, root export, pins, policy, workflow,
machine registry and checking scripts. This is source-byte and declaration-census
evidence, not a reproduced elaborated type-hash comparison.

`check_semantics.py` independently passes 2,761 framed growth states (11,044
growth checks), 5,625 dot products, 16,352 expansion/signed-output cases, 3,008
matrix cases, 3,591 strict-rounding cases, 1,872 gadget inversions, 216 lossy-image
budgets, 121 rational anti-cyclic ranks and 17,836 all-but-one evaluations. These
finite models supplement the statement review; they prove no Lean theorem,
general complexity bound or cryptographic hardness claim.

Development failures and superseded successful sweeps are preserved separately.
The first broad sweep failed on a missing public import; it is not final evidence.
`evidence/final-sweep/` predates the reader refinement and is also not final
evidence. The nine-module reader recheck and preliminary probe are development
records. Only `audit-final-sweep` and `axiom-probe` support the final totals above.

Packages are APFS copies of this same chat's own pinned package tree, never
another chat's scratch objects. The final TCSlib object tree starts empty. No new
Mathlib root is fetched, no package is changed, and no native/cache PID is killed.
All 15 manifest pins remain fixed; eight physical package directories are present.
Their 8,235 selected non-build source/configuration files match the prior own
package tree byte-for-byte. The initial setup Git probe accidentally returned the
enclosing checkout revision because these package directories have no `.git`;
`setup.json` retains and invalidates those values, and `package-provenance.json`
records the corrected scope. They are not package-revision attestations.
Physical archive/cache origin and native freshness remain maintainer attestations.
Disk/memory observations are retained. Global process inspection is unavailable;
no absence of other chats' jobs is claimed. Root native/cache work was serial.

## Open coordination and later consumers

`COORDINATION.md` includes exact unapplied proposals for `Randomized.blockVal_eq`
and catalogue registration of the already public counted loop. The missing reader
blocks its named proof route; the unregistered-loop policy issue blocks the
affected efficiency fills pending owner/registry disposition. No fill brief for
those routes is issued. Earlier probability readers and source-registry proposals
also remain data only. The audit should assess these issues explicitly rather
than treat preparation as their approval.

Eight earlier reports and dispositions are retained unchanged. Their continuing
N01–N03 limits remain: primary-source validation/ingestion/approved matching,
execution/landing provenance and inherited warnings, and later sampler/schedule,
uniform asymptotic, machine and primitive-security bridges. PW10 was consulted
through its primary web PDF, but native retrieval failed DNS; no complete frozen
PW10 PDF hash or source-policy closure is claimed.

**Not yet clear to merge — the combined statement gate, 101 later proof fills,
shared-owner dispositions, source-policy work, landing checks and user approval
remain.**
