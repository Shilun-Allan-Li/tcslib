# LWE and SIS constructions

## Scope and ownership

The user approved this scope on 2026-11-07:

1. Regev's direct symmetric encryption, not the generic PRF construction.
2. Regev's CPA-secure public-key encryption.
3. Pseudorandom generators from decisional LWE.
4. Collision-resistant hashing from SIS, including the SIS definition and assumption.
5. Standard-model CCA2-secure public-key encryption through Peikert--Waters.

For item 5, secret-matrix cryptographic trapdoors are in scope. Short lattice bases,
lattice Gaussian preimage sampling, search/decision LWE reductions, worst-case lattice
reductions, and bridges between SIS and LWE are outside scope. Commitments, PRFs, MACs,
general signatures, OT, and MPC are not additional headline targets. Supporting
strongly unforgeable one-time signatures are required by the selected CCA2 route.
Any LWE-only hashing used to make those signatures compact is supporting CCA2 work;
the selected standalone CRH target remains the SIS construction.

Audited changes are integrated through PRs into the campaign's own central branch,
`cryptography/lwe-sis-constructions`. The user approves and merges Lean changes.
The Pass–Shelat campaign branch remains upstream context, rather than the target of
new LWE/SIS construction PRs. Drafts may use separate branches/worktrees.

| Item | Identity |
|---|---|
| Active worktree | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-construction-statements` |
| Active draft PR branch | `cryptography/lwe-sis-construction-statements` |
| Central integration branch / PR target | `cryptography/lwe-sis-constructions` |
| Observed central head | `2c37f3f486822a52f4a9e337c6b742e995ebb118` |
| Current audited stack / intake baseline | `307cfdd1d6cadfda2ae9cca5367705ad770c5f42`, PRs #236/#237/#238/#239 |
| Combined statement Lean / root freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| Current independent proof source | `f293b63200ee3c6de6e709925f67c4d60fdc7b4a`, existing draft PR #250 |
| Checked F02 comment repair | `af54d28f6d412bc56844e7371e2b0b9b394c494c` |
| Audited dependency / phase-1 baseline | `0769cba3e44c56700349f954190fc99d9e622270`, PR #236 |
| Phase-1 statement freeze | `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf` |
| Construction-core proof freeze | `690217cc1aaefe411158808a8b0797fd887a8abc` |
| Upstream campaign context | `cryptography/pass-shelat-ch2-4` at `74b02c1d5c1dcea241c95d625586a7a324925cc9` |
| Original kickoff baseline | `9db11986edfce462d91958856a763577ee15457f` |
| Implementation baseline | `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49` |
| Lean | `leanprover/lean4:v4.25.0` |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

Both baselines were read with `git rev-parse`. The implementation baseline was confirmed
through the GitHub connector and fast-forwarded in this worktree only. Its Lean sources,
root exports, toolchain and manifest match the original baseline. Shell GitHub fetch is
blocked by DNS restrictions; no successful shell fetch is claimed.

The phase-1 draft was initially created from the remote-verified campaign context and
the audited foundation. When the user selected a central LWE/SIS integration branch,
its two unpublished code/export commits were replayed onto the audited dependency,
removing unrelated campaign-record ancestry. Every checked Lean/pin byte was unchanged.
Client publication retargeted PR #236 and opened draft PR #237 against the central
branch. Its proof-audit publication head was
`d4db3f832f5a4b98e8ecfde79f7fcb04977b956e`; the current records-intake head is
`ff8345b1d2ac2f605d81cdf6c23216aadb918abb`. The statement audit passed 0/0/0/3.
The user has now dispatched the proof audit at exchange
`aaeb9b3764e7fa3c2d4f3e93905e8654ea1786f5`, source
`690217cc1aaefe411158808a8b0797fd887a8abc`, bundled records
`42a400a1b88eecf9172a91ba287894450c72f9b0`. GitHub verifies the publication
metadata. The returned construction-core proof audit now passes 0/0/0/3; the
pasted report and separate gate resolutions are preserved under `audits/`. No
proof repair was needed, and the issued input packet remains unchanged.

## Passed combined statements and current independent fill

The combined statement audit passes 0/0/1/4 on #250; its F01 documentation minor
is corrected at `f1b75a7d17dc7ef5fddd7403a2d7c740ba365c9c`. The subsequent independent
fill completes 31 obligations in seven modules at
`f293b63200ee3c6de6e709925f67c4d60fdc7b4a`, with all definitions/statements/imports
frozen. Seventy owned admissions remain. A fresh 144-module sweep (303.792 s),
589-constant axiom probe (53.149 s) and scoped style 0/2/41 pass. All selected
targets are standard-axiom only. Two older compiler helpers change emitting module;
all 575 earlier elaborated type representations compare exactly. See
`briefs/lwe-sis-constructions/fills/04-construction-independent/` for the separate
proof gate. N01–N04 and user-controlled integration remain open.

The larger overnight draft has 19 mathematical modules and 220 source declarations:
57 definitions, 163 theorems, 62 closed `rfl` readers and 101 explicit admissions
for later fills. Its mathematical commit is
`2bf9dd52882bcafbce9eab48a5bab796275f2094`; the separate export commit and frozen
Lean/root are `17b2a282b545c6ebca3fccc88d518d18ae78f485`. It covers exact dyadic
sampling and bit-noise laws, encoded matrix arithmetic, SIS universality/raw-output
and asymptotic adapters, Regev PKE algorithms/concrete bounds, direct DLWE generators,
and secret-matrix lossy/all-but-one trapdoor mathematics for the later CCA2 endpoint.

The final fresh serial seven-facade sweep covers 144 modules with zero errors,
101 new and 17 inherited admission warnings. All 575 owned constants reconcile:
302 earlier constants, 220 source declarations, 40 generated non-simp projection
readers and 13 compiler auxiliaries. Exactly the intended 101 admissions use
`sorryAx`; all 48 selected backing contracts are standard-axiom only. Scoped style
is 0 FAIL/2 unchanged WARN over 41 files. No whole-library root elaboration or
completed primitive endpoint is claimed.

Six existing export files overlap with shared facades, in the separate export
commit. No old mathematical declaration or shared owner API changes. Exact proposals
for a random-bit reading lemma and registration of the existing public counted
loop remain data only; dependent proof routes await coordination. The user
preselected Codex and dispatched the combined statement audit. Publication is
verified as draft PR #250 at exchange `64e245b345d908d835030efede1c91312a4e6cce`.
The independent proof fill was published at exchange
`8efc0e669ed3ed004616c4aab81317ebf5fa17e6` and its Codex audit passes
0 blockers/0 majors/1 documentation minor/4 notes. The F02 overview repair at
`af54d28f6d412bc56844e7371e2b0b9b394c494c` is checked. The earlier-stack
source-policy inputs were published at exchange
`a4e19bd3cf029b9bf5fb2e53989ddc0d61006ac1`; their partial return is preserved
and verified under `continuation/landing-source-policy/intake-r1/` in the briefs.
Following the user's feedback, review targets consumed PDF passages and proposed
matches. Unrelated whole-document transcription is postponed and does not expand
the formalization scope or block independent work. Matching/source integration
and landing checks remain; full-reference validation is not claimed.
See `briefs/lwe-sis-constructions/gates/08-construction-statements/`.

## Historical construction-core and arithmetic gates (passed)

The separate phase-1 draft contains eight mathematical modules: explicit polynomial
sample replacement, canonical modular parsing, bounded-error bit decoding, direct
Regev symmetric encryption and its concrete two-DLWE bound, and SIS binary hashing
with a collision bound and dyadic profile. All 31 audited obligations are filled,
with the same 62 source declarations and unchanged definitions/signatures.

The fresh serial scoped sweep covers 68 modules with zero new admissions and
17 inherited warnings. All 263 owned constants have only standard axioms.
It is not a whole-library root build. The new facade/root exports are isolated in
commit `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`; the construction-core commit is
`56cabe7f3` (full history and hashes are in the phase-1 records). Existing owner
APIs and pins are unchanged. The current proof-review evidence is under
`briefs/lwe-sis-constructions/fills/01-construction-core/`. No completed
machine/primitive-security endpoint is claimed.

Independent records-only source/adapter/PKE preflight lives under
`briefs/lwe-sis-constructions/continuation/proof-audit/`. Its exact proposed
shared probability-reader patch is unapplied and needs user coordination before
implementation. The next owned adapter statement phase may now proceed after
this scoped proof gate; source-policy and user integration remain open.

The next isolated encoding-adapter statement slice is checked at
`6eec97be8f54d9990340900a5595dab32fb477f5`, on top of full audited stack baseline
`ff8345b1d2ac2f605d81cdf6c23216aadb918abb`. It has 3 definitions, 17 theorems,
3 closed defining equations and 14 explicit admissions. A fresh 93-module sweep,
283-constant inventory and nine public machine-contract axiom checks pass.
The only prior-file Lean overlap is a separate Encoding facade export commit.
No shared-owner API or pin is changed. The user dispatched Codex for its external
statement gate. Draft PR #238 targets the central branch; the exact published
exchange input is `a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4`. The returned
statement audit now passes 0/0/0/3. Its report is preserved verbatim from the user
paste. All 14 audited theorem bodies are now filled at
`b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`, with the trusted surface fixed.
A fresh 93-module sweep and 284-constant standard-axiom inventory pass, including
one disclosed arithmetic compiler auxiliary; all 100 other frozen paths are
unchanged. The separate adapter proof audit now passes 0/0/0/3 at exchange
`228c265d642013da76afa6cec976eaf11a8eb1b9`. Its full pasted report and separate
dispositions are preserved under `audits/`; no proof correction is required.
Source-policy and integration remain open. The next owned statement slice is
scalar dyadic arithmetic using the proved encoders and existing public machines.
The new 18-declaration statement slice is checked at
`dbacd91218c19f0df106d316ce4ff0e22b869e66`, with twelve explicit admissions,
a fresh 94-module sweep and sixteen axiom-clean backing contracts. Its separate
Encoding export is the only existing-file overlap. The returned statement gate
passes 0/0/0/3 at exchange `1ac4e2e45df94d0b5f20259218d067843458c770`, with
draft PR #239 targeting the central branch. Its twelve audited bodies may now
be filled, keeping all definitions/signatures and issued inputs fixed.
Those twelve bodies are now proved locally at
`ec72ed773a690c17ac253707350935cc9e0acb34`: fresh 94-module sweep, zero owned
admissions, all 302 owned constants and sixteen backing contracts only standard
axioms. No new compiler auxiliary or import is added. The user freshly selected
Codex for the separate proof audit. Its returned report now passes 0/0/0/3
at exchange `083448cef9229dc95b96ef45686ce7f3768992ab`, with no proof repair.
Source-policy work and user integration remain open. The user authorizes a larger
combined overnight statement draft, leaving sorries for later fills and using
Codex for all morning external audits; the user still dispatches those jobs.

The exact Pei16 and Wu24 PDFs were retrieved directly over HTTPS, independently
hashed and text-extracted in this worktree's source archive. Their provenance is
under `briefs/lwe-sis-constructions/gates/02-construction-core/evidence/`.
Reference ingestion and approved source matching remain open; no source-ingestion
pipeline or paid cleanup/matching job was launched. Historical issued source-status
records are unchanged. Independent raw extraction and machine-adapter preparation
are recorded under `briefs/lwe-sis-constructions/continuation/`.

Do not edit the maintainer's campaign checkout or any Pass--Shelat records. Frozen
Gate06 source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` and PR #232 belong to their
maintainer. Do not merge that branch as a shortcut to its APIs. Do not access or mutate
the Arora--Barak campaign checkout or exchange namespace. The user alone dispatches
external jobs; this continuation launches none.

## Organization

Problem definitions and assumptions belong under their problem; constructions belong
under their primitive. A matching facade imports each topic's children.

| Directory under `TCSlib/Cryptography/` | Owner-side content |
|---|---|
| `Encoding/` | Fixed-width modular vectors and matrices shared by the two new problem directories |
| `LWE/` | Parameters, noise, sample distributions, encodings, decisional games and assumptions |
| `SIS/` | Parameters, integer solution relation, encodings, success experiment and assumption |
| `Encryption/Symmetric/Regev/` | Direct noisy-inner-product construction and security |
| `Encryption/PublicKey/Regev/` | Subset-sum construction, correctness, CPA security and bitwise bridge |
| `Pseudorandom/Generators/LWE/` | Explicit seed allocation, generator and security |
| `Hashing/SIS/` | Binary-domain matrix hash, compression and collision reduction |
| `TrapdoorFunctions/Lossy/` | Generic lossy/all-but-one contracts and LWE matrix implementations |
| `Encryption/PublicKey/PeikertWaters/` | CCA2 construction, parsing, re-encryption checks and game sequence |

The last two directories are supporting cryptographic trapdoor functionality and its
consumer, not a lattice-basis library. A small supporting one-time signature module is
placed under a primitive directory after its contract is settled. Its exact location
must avoid creating a competing owner for PR #232's ordinary signature API.

## Sources and source-access status

| Tag | Reference and relevant locations | Official author-hosted URL |
|---|---|---|
| Reg09 | O. Regev, *On Lattices, Learning with Errors, Random Linear Codes, and Cryptography*, JACM 56(6), 2009; author version dated 2009-05-02, section 5 for PKE | https://cims.nyu.edu/~regev/papers/qcrypto.pdf |
| Reg10 | O. Regev, *The Learning with Errors Problem*, CCC 2010 invited survey, sections 1 and 4 | https://cims.nyu.edu/~regev/papers/lwesurvey.pdf |
| Pei16 | C. Peikert, *A Decade of Lattice Cryptography*, author version dated 2016-02-17; Definitions 4.1.1, 4.2.1 and 4.2.3, sections 5.2.1 and 5.7.1 | https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf |
| PW10 | C. Peikert and B. Waters, *Lossy Trapdoor Functions and Their Applications*, author version dated 2010-06-04; sections 3.1--3.2, 4.3 and 6.2--6.5 | https://sites.cc.gatech.edu/fac/cpeikert/pubs/lossy_tdf.pdf |
| Wu24 | D. Wu, CS395T *Topics in Cryptography* lecture notes, Spring 2024 compilation last updated 2024-04-30; Definition 20.5 and Lecture 21 for direct symmetric Regev encryption | https://www.cs.utexas.edu/~dwu4/courses/sp24/static/notes.pdf |

The original foundation packet used live primary-source views because shell downloads
failed DNS. During phase 1, the Node runtime retrieved exact Pei16 and Wu24 PDF bytes;
local hashing and text extraction independently checked the hashes and version headers.
Their precise URLs, sizes, SHA-256 values and page anchors are in the phase-1 provenance
record. The remaining future-phase sources have no byte-archive attestation yet.
Reference ingestion, approved proofmatch and bibliography registry changes remain open.
The historical foundation packet is unchanged and does not retroactively acquire a
source archive. Shared registry changes need their own reviewable diff.

The direct symmetric scheme is the elementary noisy-inner-product encryption obtained
from the LWE distribution: add the encoded bit to a fresh sample's last coordinate.
Wu24 Definition 20.5 and Lecture 21 provide an instructor-hosted source anchor. The notes
describe themselves as lightly edited; their mathematical details still need independent
checking at that construction's gate. This is not the generic PRF construction.

## Foundation decisions

### D1. Explicit dimensions, modulus, noise and sample count

The asymptotic security parameter is separate from LWE dimension, sample count, and
modulus. Numeric parameters form a bundle with modulus at least two. The first ideal
experiment uses a uniform secret in `(ZMod q)^n`, a uniform `m`-by-`n` matrix, and
independent coordinate errors. A single secret is shared across all `m` rows. Sampling
fresh secrets per row would state a different problem and is forbidden.

Hardness for one sample-count schedule and hardness for every polynomial schedule are
distinct predicates. No sample-extension, small-secret, normal-form, modulus-switching,
or noise-change equivalence is implicit. Parameters alone do not assert hardness.
The public predicates are `LWE.DLWEAssumption` and `SIS.SISAssumption`, following the
user's naming decision; the `D` explicitly identifies decisional LWE.

### D2. Noise laws versus implementations

The first implementation-facing model is a scalar integer sampler from a finite,
nonempty uniform seed type. It specifies its induced noise law, not uniform noise on
its support: repeated seed images retain their multiplicities. Taking an independent
seed per coordinate gives the product law. Bit samplers are an additional refinement;
efficient samplability is a separate machine obligation.

The first executable profiles use power-of-two moduli and explicit bit samplers for
the scalar noise. Fixed-length unbiased coins cannot exactly implement uniform
residues modulo an odd modulus or an arbitrary rational finite-seed noise law. General
moduli remain part of the mathematical problem; a general-modulus implementation must
account for its sampling error explicitly.

This model expresses finite rational laws. It does not claim to sample an infinite
discrete Gaussian exactly. A Gaussian-to-bounded implementation, if used, needs an
explicit statistical-distance lemma, a tail bound and an implemented sampler. The
hardness hypothesis always names the actual error law or an explicitly proved transfer.

### D3. Perfect correctness

Existing encryption structures require correctness for every coin string. Use bounded
errors and quantitative modulus conditions sufficient for this stronger guarantee.
For an even modulus, `|e| <= B` and `m B < q/4` are sufficient for the PKE subset sum;
the symmetric scheme only needs the corresponding one-error bound. The final statement
must handle the encoding distance for arbitrary allowed moduli, ties, and finite small
parameters explicitly. A negligible-error Gaussian theorem does not inhabit the existing
perfect-correctness structure without an additional argument.

For nearest-codepoint decoding with encoded bit one at `floor(q/2)`, sufficient strict
bounds are `2B < floor(q/2)` for the symmetric scheme and
`2mB < floor(q/2)` for PKE. For example, at odd modulus five, error one can produce a
tie even though it is less than `q/4`. The initial dyadic profiles avoid that boundary.

### D4. SIS is an independent assumption

Use integer solution vectors, required to be nonzero over the integers, with a squared
Euclidean norm bound. Naming the bound as `sqNormBound` avoids a hidden square root:
`sum_i z_i^2 <= sqNormBound`. The kernel equation is evaluated modulo `q`.

For the binary-domain hash, compression needs `2^m > q^n`; a collision difference has
entries in `{-1,0,1}` and squared norm at most `m`. The assumption used by that theorem
must cover this bound. Nonvacuity and exclusion of trivial solutions are checked
separately; in particular a bound admitting `q` times a coordinate vector is unsuitable.
No SIS--LWE or worst-case-lattice theorem is used or asserted.

### D5. PRG seed accounting and indexing

The first direct generator theorem has an explicit bit sampler for each error and an
exact fixed-width representation of residues; power-of-two moduli give a first exact
implementation. If each residue uses `k` bits and each scalar error uses `r` seed bits,
then sampling `(A,s,e)` uses `(mn+n)k + mr` bits and publishing `(A,As+e)` uses
`(mn+m)k` bits. Expansion requires `m(k-r) > nk`.

This inequality is a hypothesis on the actual noise sampler, not merely its support
size or Shannon entropy. A Gaussian sampler with wasteful randomness does not meet it
automatically. The final `PRG` bridge also accounts for the existing API's actual seed
length, polynomial parameter schedules, unused seed bits, output truncation to a fixed
syntactic stretch, and finite exceptional lengths. No unproved OWF-to-PRG theorem or
search-LWE reduction is substituted for these obligations.

The seed-length schedule must be increasing and efficiently computable, with polynomial
bounds on its value and its next value, so selecting the largest fitting profile does
not lose the polynomial relationship between the profile index and the actual seed
length. Independence of copied unused bits and the reindexing of nonuniform adversaries
are explicit bridge obligations.

### D6. Cryptographic trapdoors and CCA2

The allowed LWE trapdoor is a secret matrix for decoding a concealed gadget encoding.
Lossy and all-but-one function contracts are generic and public before the consumer's
fill. They need quantitative lossiness, indistinguishability, inversion and encoding
contracts. No private one-off trapdoor abstraction is built inside CCA2.

PW10 Theorem 4.2 also requires a *strongly* unforgeable one-time signature. Ordinary
fresh-message one-time security is insufficient: a new signature on the same signed
tuple can produce a different challenge-key ciphertext. Expose this stronger supporting
contract and construct an instance from the LWE-derived primitives. An intermediate
conditional theorem is allowed, but the headline LWE-only CCA2 theorem must discharge
this dependency; the independent SIS assumption must not leak into it silently.

The source review identified a signature-size cycle in raw Lamport: the signed tuple
grows with the ABO width, while its uncompressed Lamport verification key is longer
than that width. Merely increasing the ABO width does not fix this. A proposed route is
fixed-block LWE-only CRH from lossy functions (PW10 section 3.4.3), canonical domain
extension, then hash-and-Lamport using the perfectly injective trapdoor evaluator.
Injectivity gives unique signatures for a fixed digest. Hash security and inversion
security cover the remaining strong-forgery cases. The hash and signature parameters
must be independent of the eventual ciphertext length, and the ABO width must be chosen
after the resulting verification-key width is bounded. This remains a design/proof
obligation, not a claimed construction or gate closure.

PW10's lattice functions are originally almost-always injective/invertible. The existing
PKE correctness requirement must be met by an explicit bounded-noise specialization or
another checked argument, not by ignoring the bad-key event. The CCA proof retains the
full ciphertext's signature verification, inversion, canonical parsing, recomputation
checks and exact challenge-ciphertext exclusion.

A proposed exact dyadic specialization takes gadget moduli dividing the LWE modulus,
so encoding is a group homomorphism. The source review gives candidate deterministic
inversion and image-cardinality inequalities under bounded errors; these must be proved
in the statement/fill sequence. PW10's original almost-always Gaussian theorems are not
relabeled as perfect-correctness results. The ABO anti-cyclic branch matrix is inverted
over the rationals, not modulo the LWE modulus, so its role must not impose an unstated
prime-modulus assumption.

### D7. Efficiency and reuse

Use existing `Complexity.NUPPT`, `PolyExpr`, bit encodings, probability, game and machine
hosts. Do not change their public interfaces without proposing the exact diff to the
user. `Candidates.ArithmeticFP` is existing conditional arithmetic infrastructure; it is
not evidence that unconditional binary-arithmetic machines have been constructed.
Before efficiency gates, inventory the needed arithmetic/loop rows and explicitly
identify any residual hypothesis. A conditional endpoint must be labelled as such.

Reuse `InformationTheory.LeftoverHash` rather than reproving the leftover hash lemma.
The required binary-subset linear family still needs its own universality proof.

## Statement phases and audit gates

| Phase | Frozen surface to prepare | Fill starts only after |
|---|---|---|
| 0 | LWE/SIS parameter bundles, scalar noise, sample maps, solution relation, canonical encodings, concrete/asymptotic games | External foundation gate with zero blockers/majors |
| 1 | Direct symmetric encryption and SIS hash definitions, correctness/security/compression statements, machine contracts | Their statement gates |
| 2 | Regev PKE and direct PRG, parameter profiles, leftover-hash and indexing obligations | Their statement gates |
| 3 | Lossy/all-but-one contracts and LWE constructions; strong one-time signature dependency | Separate supporting gates |
| 4 | PW10 CCA2 construction, exact game sequence and final existing-API bridge | Supporting gates and CCA2 statement gate |

At each phase: precise imports, source-tagged statements, prose sketches, owner-side
non-simp readers, native per-module checks, admission/axiom inventory, style lint and
explicit shared-file overlap inventory. No phase is called checked or dispatched while
its evidence is incomplete. The user selects Codex or Claude and dispatches external
jobs; prepare self-contained inputs before asking for that selection.

## Shared interfaces and exports

Current work adds only new topic files and this campaign's records. No existing
Asymptotic, Candidates, Games, ZeroKnowledge, probability/PAC or randomized interface
is changed. PR #232's CRH and CCA notions are read as prospective consumers, not copied
into a competing API or assumed merged. The hash/CCA bridges wait for the owner version
to land or for an explicit coordination decision.

Root exports are a separate small commit. Phase 0's exact additions are:

```lean
import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
```

Those were phase 0's only existing shared-file changes. Relative to the audited
dependency, phase 1 adds only `Cryptography.Encryption` and `Cryptography.Hashing`
at the root and the new children in the Encoding/LWE facades. Its export commit
is separate from the eight mathematical modules. No existing owner definition,
theorem or machine interface is changed. The five scoped facade roots and their
complete transitive TCSlib dependencies have native checks; this is not a
whole-library root elaboration or merge clearance. Each PR discloses this overlap.

## Verification and current execution limits

Use only this branch's `.lake/packages/` and fresh
`TCSLIB_OLEANS=<worktree>/.lake/dyadic-final-oleans`. Do not use another chat's
TCSlib scratch objects. The installed Lean 4.25.0 executable has been checked. Disk
space exceeds 400 GiB. Process inspection via `ps` is denied by the execution sandbox.
The user subsequently increased the coordination budget by two and authorized up to
two sub-agents. This resolves the earlier scheduling hold. Root performs cache/native
work serially; sub-agents receive no native/cache slot unless explicitly allocated.
Phase 0 independently hashed pinned sources and selected official package archives.
Phase 1 makes an isolated APFS clone copy of that same chat-owned package setup;
it copies no TCSlib objects and fetches no new cache root. Its TCSlib objects are
freshly compiled here. Other chats' packages and scratch objects are not reused.

Check one module at a time through `scripts/lean_check_tree.sh`. No `lake build`, no
unfiltered cache download, no package changes in another checkout, no borrowed scratch
oleans, and no killing another job. Only required Mathlib roots at the manifest pin are
eligible for the isolated cache. Python commands use `python3 -I`.

The original statement phase had 14 admitted representation statements and 17 inherited
warnings. Its external audit passed. All 14 proofs are now filled at
`893e921bf2afeca293be9da9d495613bb1486796`; a new fresh 55-module sweep has zero errors,
zero new admissions and the same 17 inherited warnings. All 166 elaborated constants
use only standard axioms. The full library root has not been swept. Original statement
evidence is unchanged; the proof fill has its own source freeze and evidence.

Shell fetch/push remains blocked by DNS, and connector PR creation previously returned
HTTP 403. The user completed client publication: draft
[PR #236](https://github.com/Shilun-Allan-Li/tcslib/pull/236) was initially opened
against the campaign base from `cryptography/lwe-sis-encoding-proofs`; its
retarget to the central LWE/SIS branch is now remotely verified. Codex reviewed the exchange
input at `ebe777ba3bf904f6a6909aaf8b931fcb0c53f358`. The returned representation-proof
audit passes with 0 blockers, 0 majors, 0 minors and 3 continuing notes. Its report
is preserved verbatim under `audits/lwe-sis-encoding-proofs-findings.md`; the separate
resolutions close only this proof gate. Reference ingestion/source matching and
relevant integration checks remain open. The central ref and issued snapshots have
not been changed by preparing phase 1; the user controls approval and merging.

## Decision log

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-07 | User selected the five headline constructions; SIS assumption independent of LWE. | Approved scope |
| 2026-11-07 | User approved problem/primitive folder organization and secret-matrix trapdoors for CCA2; excluded short bases/Gaussian preimage sampling. | Approved scope |
| 2026-11-07 | Own branch renamed; own checkout fast-forwarded to the remotely verified baseline. Other worktree branches verified unchanged. | Executed |
| 2026-11-07 | Native/cache activity cannot be inspected in this sandbox; heavy checks deferred. | Superseded by the approved budget increase below |
| 2026-11-07 | User increases the resource coordination budget by two and authorizes up to two sub-agents. Scheduling hold lifted; root cache/native jobs remain serial. | Approved / executing |
| 2026-11-07 | Read-only source review confirms the five mathematical foundation modules' conventions and identifies dyadic-sampling, odd-modulus tie, PRG indexing and CCA signature-size obligations. No external gate or proof completion inferred. | Internal review data |
| 2026-11-07 | User selects `DLWEAssumption` and `SISAssumption` for consistency with existing named assumptions; readers are `dlweAssumption_iff` and `sisAssumption_iff`. | Approved naming |
| 2026-11-07 | Phase-0 foundation modules pass a fresh serial 55-module dependency sweep. Four renamed-module/facade rechecks pass. Fourteen representation obligations remain admitted; no construction/security fill has started. | Native evidence; external gate pending |
| 2026-11-07 | Own remote branch creation via GitHub connector fails with HTTP 403; shell fetch still fails DNS. | Publication blocked; local work continues |
| 2026-11-07 | Foundation source frozen in `458d178ab23d06d7cb04f6672af9f8e23eac0b4b`; three root imports isolated in `4364d0e0fe9accd649b6acb4751e8684aa93ad1e`. Final 61-declaration axiom probe passes; 14 admitted statements, 164 elaborated constants. | Prepared external review; no verdict |
| 2026-11-07 | Final style: zero FAIL, two check-8 acronym-reader heuristic WARNs. Actual `dlweAssumption_iff` and `sisAssumption_iff` readers follow RSA/DDH convention; no shared lint edit or zero-WARN claim. | Explicit review item |
| 2026-11-07 | User selects Codex for phase-0 external review and offers to publish the own PR branch. The delivered round-1 pack/source freeze stays unchanged; the separate Codex kickoff records the selection. Publication is only to `cryptography/lwe-sis-constructions`; no campaign push or merge is authorized. | Codex selected; user dispatch/publication pending |
| 2026-11-07 | User corrects the audit input transport: Codex reads pinned inputs from GitHub on the exchange branch and returns Markdown in chat. Prepare only `lwe-sis-constructions/outbox/gates/00-foundations-r1/` plus its namespace README in a separate sparse publisher clone; leave the shared exchange checkout/index and all other namespaces alone. The frozen bundle is unchanged. | Supersedes ZIP-attachment kickoff; publication pending |
| 2026-11-07 | User dispatched the phase-0 audit at exchange `09d1456efacded71850c84497db5c8d1f65ab0a0`; report retained verbatim with SHA-256 `87ce303895f81064891eb7ab1401b4be601dbc3671d02e28428b5acd4386a906`. Verdict PASS, 0 blockers / 0 majors / 0 minors / 3 notes. | Statement gate closed; N01–N03 retained |
| 2026-11-07 | User requires future Lean updates through PRs for approval; maintainer records may be pushed directly. User pauses for relocation, then explicitly resumes work after the audit returns. | Binding / resumed |
| 2026-11-07 | All 14 representation proofs filled at `893e921bf2afeca293be9da9d495613bb1486796`. Fresh 55-module sweep passes with zero new admissions and 17 inherited warnings; all 166 constants use only standard axioms. Signatures and non-theorem bodies remain invariant. | Proofs checked; external proof gate pending |
| 2026-11-07 | User freshly selects Codex for representation-proof review at `lwe-sis-constructions/outbox/gates/01-encoding-proofs-r1/`: GitHub inputs, Markdown output in chat, user dispatch only. | Selected; publication/dispatch pending |
| 2026-11-07 | Shell GitHub/source-host access still fails DNS. Connector draft-PR creation returns HTTP 403, `Resource not accessible by integration`. | Client publication required; no PR claimed yet |
| 2026-11-07 | To enforce user-approved Lean updates, continue the verified proof fill on fresh PR branch `cryptography/lwe-sis-encoding-proofs`, from source commit `893e921bf2afeca293be9da9d495613bb1486796`, targeting the original campaign base. Leave the published `cryptography/lwe-sis-constructions` ref unchanged. Only the own checkout is switched. | Active PR route |
| 2026-11-08 | Client publication remotely verified: draft PR #236 at `aaf4d1d3ea2e5113b6f53c3fedd9b5d47e852de1`, targeting the campaign base. User dispatched Codex against exchange `ebe777ba3bf904f6a6909aaf8b931fcb0c53f358`. | Supersedes earlier publication/dispatch pending status |
| 2026-11-08 | Representation-proof report received verbatim, SHA-256 `21783a113298e880cfb7cc272607c787b0bf908cbaac9e23a646236e8bfb4857`. PASS 0 blockers / 0 majors / 0 minors / 3 continuing notes. Intake reverified all 63 frozen source files, 86 current evidence hashes, 82 historical hashes and 5 exchange-gate hashes; no Lean or pin change. | Proof gate closed; N01–N03 retained; no merge approval |
| 2026-11-07 (Pacific) | User publishes the audit records; remote PR #236 head `0769cba3e44c56700349f954190fc99d9e622270` verified. | Published; unmerged |
| 2026-11-07 (Pacific) | User selects `cryptography/lwe-sis-constructions` as the central integration branch for audited changes; separate draft branches/PRs remain permitted. PR #236 and subsequent PRs target it. | Supersedes earlier campaign-target routing; user still approves and merges Lean changes |
| 2026-11-07 (Pacific) | Replay the two unpublished phase-1 code/export commits onto the audited LWE/SIS dependency, removing campaign-record ancestry. The 68 checked Lean files and pins remain byte-identical. Bring planning records into the active draft; the old planning worktree is no longer used. | Own draft history adjusted; central/campaign refs unchanged |
| 2026-11-07 (Pacific) | Eight construction-core modules elaborate as statement skeletons: 62 source declarations, 31 direct admissions. Fresh serial 68-module sweep passes, with 17 inherited warnings. | Statement review pending; no proof-fill or construction-completion claim |
| 2026-11-07 (Pacific) | Retrieve exact Pei16 and Wu24 primary PDF bytes over HTTPS through the Node runtime; independently verify SHA-256 and source-version headers. No reference registry or dataset pipeline changed. | PDF acquisition complete for this slice; ingestion/source matching open |
| 2026-11-07 (Pacific) | User dispatches the construction-core Codex audit. PR #237 head `1b148307150a0b0a08dd80d68c54ba2db95de13c` and both PRs' central targets verified; exact exchange input `90d652e19508262b3bd81234260d0585aaf8e0a0`. All 76 frozen source files and seven payload hashes match. | Audit running; Lean freeze retained |
| 2026-11-07 (Pacific) | Deterministic local raw extraction covers the 90-page Pei16 and 106-page Wu24 sources, using the existing proofmatch formatter/diagnostics with installed pdftotext. Prepare an unapplied two-tag registry diff and a consumer machine-adapter map; no model job, shared-file edit or Lean change. | Independent preparation; source validation/matching still open |

| 2026-11-07 | Codex construction-core statement audit PASS 0/0/0/3 at `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`; report preserved verbatim and intake checks reconciled. No statement repair. Fill the 31 theorem bodies on existing PR #237; keep definitions/signatures fixed. | Scoped statement gate closed; proof gate and N01–N03 remain open |
| 2026-11-07 | Filled all 31 audited construction-core proofs at `690217cc1aaefe411158808a8b0797fd887a8abc` on existing PR #237; 62 declarations/definitions/signatures fixed. Fresh 68-module sweep, 263-constant axiom probe, freeze and scoped style checks pass; no shared API/export/pin edit. | Proof audit not yet selected; N01–N03 and user integration remain open |
| 2026-11-07 | User reports construction-core proof audit dispatched; GitHub metadata verifies code head `d4db3f832f5a4b98e8ecfde79f7fcb04977b956e` and exchange `aaeb9b3764e7fa3c2d4f3e93905e8654ea1786f5`. Independent records compare nine primary PDF pages, identify existing dyadic sampling/width-normalization hosts, and prepare an unapplied two-reader proposal plus quantitative PKE preflight. | Proof input frozen; no new Lean/API/native/external job or merge |
| 2026-11-07 | User supplies construction-core proof report as Markdown paste: PASS 0/0/0/3. Preserved the entire report body, verified 76 source files and all 174/106/86/82/5 nested evidence entries, and closed only this proof gate. No Lean repair, native rerun or merge. | Next owned adapter statement draft authorized by gate; N01–N03 and user integration remain open |
| 2026-11-07 | Created isolated adapter draft from central base `2c37f3f486822a52f4a9e337c6b742e995ebb118` plus audited stack `ff8345b1d2ac2f605d81cdf6c23216aadb918abb`; 20 statements/14 admissions, 93 fresh modules, 9 consumed FP contracts axiom-clean. One required Mathlib cache root added without changing pins. | Statement gate prepared, user selection/dispatch pending; no merge |
| 2026-11-07 (Pacific) | User selects and dispatches Codex for the adapter statement audit. GitHub verifies draft PR #238 at `a3eb3627f3b26b78613a41367221788057ca4142`, central target, exchange `a0b0d03b5694a0e9ab3df3ff6dfdd88ed7326ef4`, and #237 records intake at `ff8345b1d2ac2f605d81cdf6c23216aadb918abb`. Rechecked 101 frozen source hashes, 199 evidence entries and seven payload hashes. | Findings pending; Lean/root/pins and issued bundle frozen; no native rerun or merge |
| 2026-11-07 (Pacific) | Adapter statement audit PASS 0/0/0/3 at `6eec97be8f54d9990340900a5595dab32fb477f5`; retained the complete pasted report and rechecked 101 frozen sources plus 199/174/106/86/82/9 nested evidence entries. Prepared an undispatched source-validation scope covering 143 declarations, 19 modules and all 196 raw PDF pages. | Only the 14 audited adapter theorem bodies enter fill on PR #238; source-policy, proof audit and integration remain open |
| 2026-11-07 (Pacific) | Filled all 14 audited adapter proofs at `b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`; 20 declarations and trusted surface fixed, 100 other frozen paths unchanged. Fresh 93-module sweep (194.383 s), 284 owned constants and nine backing contracts only standard axioms, scoped style 0/2/19. One arithmetic compiler auxiliary disclosed; nine development runs retain two failures. | Separate proof-review preparation on existing PR #238; fresh worker choice/user dispatch, source-policy and landing obligations remain; no push or merge |
| 2026-11-08 (UTC) | User freshly selects Codex for the separate adapter proof audit. The 1009-section bundle, filled source and bundled-record pins remain fixed. | Codex selected; client publication and user dispatch pending; no code change or merge |
| 2026-11-08 (UTC) | User supplies the adapter proof report: PASS 0/0/0/3. Published PR #238 head `3350700f054ba07b31bcf23cab9f590afd998e28` and exchange `228c265d642013da76afa6cec976eaf11a8eb1b9` verified; rehashed all 101 sources and 146/199/174/106/86/82/9 nested evidence entries. All 14 proofs close their scoped gate. | No repair/native rerun/merge; scalar arithmetic may enter its next owned statement gate; N01–N03 and user integration remain open |
| 2026-11-08 (UTC) | Isolated dyadic arithmetic statement branch from central `2c37f3f486822a52f4a9e337c6b742e995ebb118` plus audited stack `8627edde9892607a699cf997c8dd5a8a2a700e26`. New source `dbacd91218c19f0df106d316ce4ff0e22b869e66`: 18 declarations / 12 admissions, 94 fresh modules, 16 standard-axiom backing contracts. No new Mathlib root or shared-owner API. | Statement gate prepared next; fresh worker choice/user dispatch and N01–N03 remain; no central push or merge |
| 2026-11-07 (Pacific) | User resumes with dyadic scalar statement report PASS 0/0/0/3. PR #239 head `659770d616160be594eb1d6eff6fc78807992a26` and exchange `1ac4e2e45df94d0b5f20259218d067843458c770` verified; rehashed 102 frozen source files and 126/146/199/174/106/86/82/9 evidence entries. No statement correction. | Twelve frozen proof bodies enter fill on existing PR #239; no merge; N01–N03 retained |
| 2026-11-07 (Pacific) | Filled all twelve audited scalar proofs at `ec72ed773a690c17ac253707350935cc9e0acb34`, with eighteen declarations and all definitions/signatures fixed. Fresh 94-module sweep (251.162 s), 302 constants and sixteen backing contracts only standard axioms; no new compiler auxiliary. Three passing development runs retained. | Separate proof audit prepared next on existing PR #239; no export/shared API/pin edit, push or merge; N01–N03 retained |
| 2026-11-08 | User freshly selects Codex for the separate scalar proof audit. Filled source `ec72ed773a690c17ac253707350935cc9e0acb34`, bundled records `a9b97213c616ef7afe80dcaa57eb5a503cf6b110` and the 1301-section packet remain fixed. | Codex selected; client publication and user dispatch pending; no code change or merge |
| 2026-11-08 | Scalar proof audit PASS 0/0/0/3 at `ec72ed773a690c17ac253707350935cc9e0acb34`; full pasted report retained, 102 frozen sources and all nine nested checksum sets rehashed. Published #239 head and exact exchange input verified. User authorizes a larger combined overnight statement draft with sorries for later fills and preselects Codex for morning audits. | Eight scoped gates pass; no merge; pause only dependent fronts requiring user input and continue independent work |
| 2026-11-08 (UTC) | Isolated combined draft from central `2c37f3f486822a52f4a9e337c6b742e995ebb118` plus audited/intake stack `307cfdd1d6cadfda2ae9cca5367705ad770c5f42`. Mathematics `2bf9dd52882bcafbce9eab48a5bab796275f2094`, separate exports/freeze `17b2a282b545c6ebca3fccc88d518d18ae78f485`: 19 modules, 220 declarations, 101 admissions; final fresh 144-module sweep (288.743 s), 575 constants and 48 backing contracts reconciled, style 0/2/41, finite models pass. Two internal agents supplied read-only research; root native work stayed serial. | Combined Codex statement review prepared; no external dispatch, central push or merge; shared reader/catalogue proposals remain unapplied and dependent fills paused; N01–N03 retained |
| 2026-11-08 (Pacific) | Combined statement audit PASS 0/0/1/4 at exchange `64e245b345d908d835030efede1c91312a4e6cce`, PR #250 verified open/draft. F01 comment-only repair `f1b75a7d17dc7ef5fddd7403a2d7c740ba365c9c` passes native/style/source invariance checks. Independent fill `f293b63200ee3c6de6e709925f67c4d60fdc7b4a` closes 31 obligations in seven modules; 70 remain. Fresh 144-module sweep 303.792 s, 589 constants and 48 backing contracts reconciled, selected fills sorry-free; all 575 prior elaborated types preserved, two compiler-origin migrations disclosed. | One combined Codex proof review prepared on existing #250; no shared proposal, external dispatch, central push or merge; N01–N04 retained |
| 2026-11-08 (Pacific) | Independent 31-proof audit PASS 0/0/1/4 at exchange `8efc0e669ed3ed004616c4aab81317ebf5fa17e6`, PR #250 verified open/draft. F02 overview-only repair `af54d28f6d412bc56844e7371e2b0b9b394c494c` passes module/style and unchanged-code checks. Rehashed 153 sources, 2796 attachments and all 12 nested checksum sets (2411 entries). Prepared first-landing source-policy job: 161 declarations/20 modules at audited earlier-stack source `ec72ed773a690c17ac253707350935cc9e0acb34`, Pei16/Wu24 PDFs/raws, 196 pages. | Ten gates pass; user dispatch and source/matching review required. No new proof wave, registry/dataset edit, paid pipeline, external dispatch or merge; N01–N04 retained |
| 2026-11-08 (Pacific) | User supplies the source-policy ZIP locally. Intake verifies 58 delivery and 10 input checksums, four exact primary assets, 191 frozen blobs and 703 typed matching records; all 161 names are accounted for. Original PARTIAL report and bytes are preserved. User asks to defer PDF-to-Markdown work for material not being formalized; root narrows review to consumed passages. All 59 proposed matches cite seven already-repaired pages. | Bulk transcription deferred, not an additional landing prerequisite. No whole-reference validation, approved matching, registry/blueprint/dataset or Lean edit, new dispatch, push or merge; scoped source integration and landing checks remain |
| 2026-11-09 (UTC) | Gate 12 round one accepts the mathematics of all 40 fills and holds on a duplicated subset-sum bound. F02 is repaired in `d3bb52db5aaf249a35e83506371a3c86e76cb69a`. The user approves the exact F01 patch, applied at `93dc88648f117877e42aaf58ba7b911c76a4b63a` on #250. A fresh 144-module sweep, 220 type comparisons and 309 axiom prints reconcile. | Round two includes the shared owner theorem and both existing wrappers. The 18 admissions, scoped source review, and landing checks remain open. |
| 2026-11-09 (Pacific) | Gate 12 round two passes the 40-fill proof gate with zero blockers, majors, and minors. Both repairs are closed at Lean `93dc88648f117877e42aaf58ba7b911c76a4b63a`. Intake verifies published exchange `3d1d76833cf36a614559338dd31a2dc0459618d5`, 260 attachments, and 44 nested evidence checksums. | Four continuing notes remain. The 18 admissions, scoped source review, and landing checks are open. |
| 2026-11-09 (Pacific) | Filled both anti-cyclic rank obligations at `75a4214dc098cd6c363d00c34f569bac23eb4555`. All four affected modules and three probes pass. 216 types match exactly and four have kernel-checked definitional equality. Restored 178 missing official archives for the pinned cyclotomic import. | Sixteen admissions remain. The next combined proof audit requires a fresh scoped sweep. The shared positional reader still awaits approval. |
| 2026-11-09 (Pacific) | Applied the user-approved block reader at `2414fd3eae05c99474d1888609b01ac5989523a5` and checked seven gadget and inversion fills at `713093c36ac66f7e56e9354581f0bb3f59772341`. The fresh 144-module scope passes. | Nine owned admissions remain. The combined rank and gadget review awaits maintainer publication. |
| 2026-11-09 (Pacific) | Gate 13 round one PASS with zero blockers, majors, and minors at exchange `4cd97c861b80fb7d3ea7f40a772657c7aad367eb`. The auditor independently replayed the 144 modules and both probes for Lean `713093c36ac66f7e56e9354581f0bb3f59772341`. | The four continuing notes, nine counted-loop and CRH admissions, and landing checks remain open. |
| 2026-11-09 (Pacific) | Checked the existing counted-loop FP host composed with H14 clean installation and its head envelope. Prepared the exact one-row H16 proposal against the common registry blob. | The shared registry awaits maintainer coordination and Gate 14 review. |
| 2026-11-09 (Pacific) | The maintainer approved the exact H16 row. Applied the registry-only change at `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11` and pinned the 45-module head-envelope probe closure. | Gate 14 independent host review precedes the consumer fills. |
| 2026-11-09 (Pacific) | Gate 14 round one PASS with zero blockers, majors, and minors and one scope note. The 45-module replay and both public-contract specializations pass at exchange `20436a1bea0ebeb636c2a0ca39acfa9969a4caae`. | The approved H16 registration is cleared for the seven efficiency fills and two dependent SIS CRH fills. Scoped source matching and landing remain open. |
| 2026-11-16 | **Phase 5 (GSW leveled homomorphic encryption) opened by Seyoon; the maintainer of the Pass–Shelat campaign runs it on `cryptography/pass-shelat-ch2-4`, which already contains this campaign's central branch.** Design and draft statements: `briefs/lattice-gsw/` (plan section, 37 targets, questions). Scope: leveled GSW from ordinary LWE, then full FHE with a polynomial modulus-to-noise ratio (phase 6: bootstrapping under weak circular security; phase 7: BV14, Barrington plus permutation branching programs). **Rulings Q1–Q16 accepted, with Q9 changed: modules under `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`** ([rulings](briefs/lattice-gsw/rulings.md)). Sources GSW13, BV14, AP14 received (not committed). | Approved scope |
| 2026-11-16 | Phase 5 statements compiled on `stmt/gsw` `48d796a8`, which sits on `stmt/dagcircuit-readers` `94eae71b`: 35 targets `sorry`, seals 48/48, root `TCSlib` OK. Statement-text rulings: QS1 `Matrix.of` in `hashColumns_eq_mul`; QS2 `GSW.mul` qualified in `Encrypts.mul_bit` and `mul_le`. Evidence `briefs/lattice-gsw/statement-phase/EVIDENCE.md`. | Approved |
| 2026-11-16 | **Gate 41 pack** (Codex statement gate, standing ruling): `briefs/lattice-gsw/gates/41-gsw-statements/` for draft [PR #332](https://github.com/Shilun-Allan-Li/tcslib/pull/332) (DAGCircuit readers, `94eae71b779c4ca0f76c138d699f4d737dbd6cee`) and draft [PR #333](https://github.com/Shilun-Allan-Li/tcslib/pull/333) (GSW phase 5, `48d796a8a68cd50897047f01825a8132dd19e8d8`, stacked on #332), audited together; base `523d80d2`; 13 files +1457/−0. Fidelity of the gadget presentation to GSW13, AP14 §3.2 and Pei16 §6.1.3; truth of the 35 targets with the noise bounds (`N·β₁ + |x₁|·β₂`, `β₀ + k·N·β`, `(N+1)^depth·β`, `2·(ℓ·((N+1)^L·mB)) < ⌊q/2⌋`) re-derived by hand, no off-by-one found, put to Codex; IND-CPA (two DLWE + `2·N·ε`); reuse and the Q11 duplicate; #332's `getD_lt_depth` and `runWith_rel` audited as proofs; Rule 10 (48/48), docstrings, roadmap fit (Q12). Source excerpts of only the passages used (GSW13, AP14, BV14; Pei16 from the committed raw extraction). Evidence `stmt-gsw.zip` (`4b144e17`) filed at `statement-phase/evidence/` (545/545). Open, for a ruling: Q14's GSW13 ingest is not in #333; Pei16 §5.4.3/§6.1.3 are only in the raw extraction. Merge interaction (git objects): clean with the tip `0542dd92`, #324, #327, #331 (#332); union conflict #333×#331 in the shared facade. Merge conditions: #332 first; rebuild `DAGCircuit` downstream (281 modules; both sides change `DAGCircuit.lean`, disjoint hunks) and the 16/41 joint modules with #324/#327; union by whichever of #331/#333 lands second. verification.zip `63afa3f6` (74 entries), sources.zip 118 files, pack `359b880b`. | Ready to stage |
| 2026-11-16 | **Gate 41 staged** on the exchange (local commit, for the maintainer to verify and push): `outbox/gates/41-gsw-statements-gate/` at `c72de14a98d2ad107600323b171985017465e33a` (on the Gate 40 exchange commit `870bed6c`; bundle 21 sections, SHA-256 `04144215`; SHA256SUMS `67237cf9`, 15/15 from a fresh archive; `verification.zip` `63afa3f6`, 73/73 inner; records pin `86d19094aafecc1e19d208c6629b179cfdd14009`, signed; Lean heads `94eae71b` (#332), `48d796a8` (#333)). Local branch `stage/gate41-exchange`. Dispatch prompt `briefs/lattice-gsw/gates/41-gsw-statements/dispatch.md`, with two questions for Seyoon (Q14 ingest timing; Pei16 scoped coverage). | Ready to dispatch once pushed |
| 2026-11-16 | Gate 41 (Codex) closed by disposition. #332 CLEAR. #333: no mathematical issue; the Q14 ingest is deferred as DW-7 (Seyoon); docstring minors fixed in `486f44f8`. Next: integration builds, then merge #332 before #333. | Gate closed |
| 2026-11-16 | **GSW fill wave ruled** (Seyoon): issue F1–F7 tonight against the gate-closed #333 head `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, once #333's integration build passes, without waiting for the merge (F0 is #332). Worker **Claude, 2 jobs**: `gsw-core` (F1 Gadget, F2 Noise, F3 Scheme, F7 Symmetric, F4 Eval; about 760 lines; multi-agent, up to 2 sub-agents) and `gsw-security` (F5 SIS columns, F6 Security; about 270 lines; single agent). Pairing fills wait for Gate 40 round 2. Maintainer stages both packs on the exchange. | Staging |
| 2026-11-16 | **GSW fill packs issued** (Claude, 2 jobs): `gsw-core` (F1, F2, F3, F7, F4; 29 targets; lead plus up to 2 sub-agents; brief `c1a603cc`) and `gsw-security` (F5, F6; 6 targets; single agent; brief `5ce6f12e`), on the issue base `486f44f8414c20a2d21e452c44de8b8c8d8513a0` (#333 head; contains #332 `94eae71b` as `486f44f8~3`, so F0's readers are proved in the base; no combined base needed). Target counts match §G7 (35). Exchange `523d4e97302606b0301ecbcff13882abb917ec1f` (the staged `665b89fd` replayed onto the new tip `04d0adc8`, whose two new commits touch only `arora-barak-ch3-4/`; identical diff); records `briefs/lattice-gsw/fills/{gsw-core,gsw-security}/issued-r1/` (SHA256SUMS 7/7 each; the exchange copies of the briefs are byte-identical). Integration check of #333 on the tip: pending at issue. | Ready to dispatch |
| 2026-11-16 | **GSW fills dispatched** (Seyoon): `gsw-core` (Claude lead plus up to 2 sub-agents) and `gsw-security` (Claude, single agent), from exchange `523d4e97` on base `486f44f8`. Deliveries expected under `inbox/fills/gsw-core/` and `inbox/fills/gsw-security/`. | Running |
| 2026-11-16 | **Integration check of #333 on the tip: PASS** (recorded for the GSW fill wave). Scratch merge tip `c58597e6` × #332 `94eae71b` × #333 `486f44f8` (clean; DAGCircuit auto-merged with #323's `isFaninTwo_iff` intact): 292 modules rebuilt on top of build 3's oleans (996 reused by closure key), all rc 0, 0 `error:`/`error(`; root `TCSlib` and both `audits/*/Checks` included; state check of all 1288 modules OK. Admissions in #333's modules: exactly the 35 targets; none new elsewhere. Axioms: the DAGCircuit readers standard; each GSW headline reaches `sorryAx` only through itself. Lint 92 FAIL / 101 WARN, unchanged. The issued `gsw-core`/`gsw-security` base is therefore sound on the current tip. | Fills running |
| 2026-11-16 | **Integration builds for #331, #332, #333: all PASS** (`dl-oleans-2`; evidence `briefs/pass-shelat-ch5-8/maintainer/int-stmt-331-333-2026-11-16/`, zip `9ffa41bbb1fb703bcd36ff15bc810a7ee09f3236445f81e1096eb63144617172`, 1141 files). Scratch merges on the tip `c58597e6` (unpushed, unsigned scratch): C1 tip+#332 `df4cfea4` (clean; #323's `isFaninTwo_iff` intact); C2 C1+#333 `18777085` (clean); C3 tip+#331 `c67f94a4` (clean); C4 C2+#331 `cbfa9d85` (tree `26a68b89`; add/add on `AdvancedEncryption.lean` and content conflict on `TCSlib.lean`, resolved by union; resolved files in `resolved/`, to be applied by the maintainer when #331 is updated for merge). Builds, every module rc 0 with 0 `error:`/`error(`: 3 tip+#331 652/652; 2 tip+#332+#333 292 rebuilt; 1 tip+#332 3 rebuilt; 4 combined 4 rebuilt; reuse keyed on source and import closure, state check OK after each; whole-tree check at C4 (1299 modules) OK. Admissions: tip 202, C1 202, C2 237 (+35 GSW targets), C3 206 (+4 T1–T4), C4 241; no other change. Axioms: #332 readers standard; Joux and `bb1_correct` sorry-free; T1–T4 and the 10 GSW headlines each reach `sorryAx` only through themselves; `bb1_sidSecure` inherits exactly T2–T4. Lint Cryptography 92/101 at tip, C1, C2; 92/103 with #331 (two new check-8 WARNs: `SIDSecure`; `BDHAssumption`/`DBDHAssumption`; passed to LE-gate40). `dl-oleans-2` restored to `457ba704` (SNAPSHOT EQUAL). Stray `/lint-a` at the filesystem root (a mistyped redirect, tip lint lines) left for Seyoon; its deletion was refused to the job. #332 and #333 marked ready. | #332, #333 clear to merge |
| 2026-11-16 | **#332 and #333 merged** (Seyoon): the records tip now holds the DAGCircuit readers and the GSW statements. GSW fills `gsw-core`/`gsw-security` were issued on `486f44f8`, now an ancestor of the tip. Cross-build tip × #327 × #324 running on `dl-oleans-2` (#327 and #324 touch `SequentialZK`, `ComposeSecurity` and `ZeroKnowledge/Defs`, downstream of `DAGCircuit`); #327 (Gate 39 CLOSED) marked ready. #331 must take the resolved facade union (`maintainer/int-stmt-331-333-2026-11-16/resolved/`) when it is updated after LE-gate40. | #327, #324 after cross-build |
| 2026-11-16 | **gsw-core final delivered** (exchange `9e52a5019`; checkpoint 1 `5b72e346b`): REPORT claims all 29 targets proved, standard axioms only, no statement change, no frozen-file edit, no scope request; 3 unsigned commits on `486f44f8` (head `d4ebb0be`), reproduction checked; 3 private helpers (`halfVector_eq_zero_of_ne_last`, `decrypt_eq_decode_errorSum`, `exists_equiv_symEncrypt`) with overlap disclosures; admissions 35 → 6 (gsw-security's). Maintainer review started: static phase now, Lean phase when an olean tree frees. | Under review |
| 2026-11-16 | **gsw-security final delivered** (exchange `5857e850e`; checkpoint 1 `b08456186`): REPORT claims all 6 targets proved (F5 `hashColumns_eq_mul`, `distAdv_hashColumns_uniform_le`; F6 `real_uniformKey_advantage`, `uniformKey_uniform_advantage_le`, `distAdv_encrypt_le`, `distAdv_encrypt_le_of_width`), no statement change, no gsw-core target cited; head `a9f97edd` on `486f44f8`; admissions in its order 53 → 47. Maintainer review started (static now, Lean when a tree frees). | Under review |
| 2026-11-16 | **gsw-core review, phase 1 (static): interim ACCEPT** (`briefs/lattice-gsw/fills/gsw-core/final-r1/review.md`, interim): manifests exact (544/544; evidence 533/533); `git am` reproduces `d4ebb0be`; only the 5 owned files (+542/−89), no imports; frozen-statement check 0 differences with 9 controls; widths ≤ 100; no new tags; 3 private helpers, no clash; no undisclosed duplicate; unfold scan 0 foreign; delivered seals 0 errors both forms, axioms standard for all 114 constants, admissions 35 → 6; lint line set unchanged; merge-tree with the tip clean. Info findings GC-01 (inline getD/`List.ofFn` chain, brief-prescribed: extend DL-47), GC-02 (Bool `toNat` identities, optional shared lemma), GC-03..06 (none). Phase 2 (Lean) waits for an olean tree. | Phase 2 pending |
| 2026-11-16 | **gsw-security review, phase 1 (static): provisional ACCEPT**, no Lean LE edits: `git am` reproduces `a9f97edd`; only the two owned files; one authorized import (`Pseudorandom.Indistinguishability`); frozen-statement check 0 differences (controls OK); decls2 0/0/0 (no new declarations); widths ≤ 100; lint line set unchanged; unfold scan 0 foreign; delivered seals and controls valid; axioms standard; admissions 53 → 47; merges with the tip and with gsw-core's `d4ebb0be` clean. Findings: GS-01 info (the ~95-line inline column hybrid in F5 and Regev-mirroring steps in F6, disclosed and brief-sanctioned: proposed as ledger debt with promotion P-1, **for Seyoon's ruling in the morning**); GS-02 minor (overlap disclosure misses `pairHybrid`/`pairRed` in `ZeroKnowledge/Commitment.lean`, `distAdv_multi_le_sum`, `distAdv_comp`: erratum, no code change); GS-03 minor (`evidence/probes/CacheProbe.lean` listed but not delivered; reconstructed, hash matches); GS-04..06 info. Phase 2 waits for an olean tree. | Phase 2 pending |
| 2026-11-16 | **DW-7 done; GSW phase-6 plan drafted** (overnight, maintainer): records `6078f369` ingests the scoped passages of Jou00, BB04, GSW13, AP14, BV14, BV11 and Barrington (Bar89, read from page images; left-to-right product order checked by computation) as `blueprint/src/references/<key>.raw.md` + `.md`, extends Pei16 with §5.4.3 and §6.1.2–6.1.3, registers the seven tags (`sources.py status`: ingested, not yet matched); validation 0 hard failures. Records `35376518` adds `briefs/lattice-gsw/phase6/plan-section.md` and `questions.md` (P6-Q1..Q13): FHE at a polynomial modulus-to-noise ratio by the BV14 route (Barrington on `TreeCircuit`; width-5 permutation branching programs evaluated by GSW selector steps costing additive `2Nβ` via the exact `|x₁|·β₂` term; per-gate bootstrapping through the augmented decryption formula; evaluation key = public-key encryptions of the bits of `G⁻¹(t)`; explicit weak circular security; uniform-secret DLWE only); 13 new files, about 55 targets, gates 42 (complexity) and 43 (cryptography); main risk: no depth term linear in `log q` (rounding as an interval test). Source notes: BV14's "[BV11, Lemma 4.1]" is Lemma 4.5 in the BV11 version held; typos transcribed as printed with notes. **P6 questions await Seyoon.** | Phase 6 awaiting rulings |
| 2026-11-16 | **gsw-security review r1: ACCEPT, no landing edit** (`fills/gsw-security/final-r1/review.md`; evidence zip `447f651d`, 1023 entries). Phase 2 on `dl-oleans-2`, tip × `a9f97edd`: 650/650 rc 0, 0 `error:`/`error(` (root and both Checks); state and whole-tree checks OK; admissions 237 → 231; axioms of the 6 targets and 32 constants standard, no sorried constant reached, no gsw-core target cited; own seals 8/8 0 errors (coe-A canonical 0 failing), controls as expected; restored (SNAPSHOT EQUAL). Findings: GS-01 info (**awaiting Seyoon's ruling**: inline column hybrid and Regev-mirroring steps as ledger debt with promotion P-1), GS-02 minor (erratum: missed relatives `pairHybrid`/`pairRed`, `distAdv_multi_le_sum`, `distAdv_comp`), GS-03 minor (CacheProbe reconstructed, hash matches), GS-04..06 info (GS-06 to the DW-4 queue). **Landed** as draft [PR #338](https://github.com/Shilun-Allan-Li/tcslib/pull/338), branch `land/lattice-gsw-security` at `d45d3682089cb6fd04f4d075f48a464fefaa143c` (the two worker commits cherry-picked onto the tip `15d8f01a`, authorship kept, signed; diff byte-identical to the delivered series). Codex gate to be staged. | Gate to stage |
| 2026-11-16 | **gsw-core review r1: ACCEPT, no landing edit** (`fills/gsw-core/final-r1/review.md` final; evidence zip `4c481a79`, 1096 files). Phase 2 on `dl-oleans`, tip `4941b511` × `d4ebb0be` (tree `76fae5c8`): 650/650 rc 0, 0 `error:`/`error(` (root and both Checks); state and whole-tree checks OK; admissions 237 → 208 (exactly the 29 targets; the 6 left are gsw-security's); axioms of all 29 targets and 114 constants standard, no sorried constant reached; own seals 20/20 0 errors (coe-A canonical 0 failing), controls as expected; GC-05 settled by a probe (matcher reductions pass under the seal; the proof uses the published reader; tooling note); restored (SNAPSHOT EQUAL). Info findings GC-01 (DL-47 site), GC-02..06. **Landed** as draft [PR #339](https://github.com/Shilun-Allan-Li/tcslib/pull/339), branch `land/lattice-gsw-core` at `839f36cca9b4af0570c014f03f19858d0a03cbfb` (three worker commits cherry-picked onto the tip `347665bd`, authorship kept, signed; diff byte-identical to the delivered series). With #338 and #339, leveled GSW (phase 5) is fully proved modulo nothing. Codex gate (both PRs) to be staged. | Gate to stage |
| 2026-11-16 | **Gate 43 staged** (Codex; fill gate for #339 `gsw-core` at `839f36cc` and #338 `gsw-security` at `d45d3682`; 42 is reserved for sc-yao, and the phase-6 plan's provisional 42/43 will be renumbered): records pin `4ed91289d6132f71ace06b3d9fd87539956d6a88` (`briefs/lattice-gsw/gates/43-gsw-fills/`: pack `e1be6cfa`, verification.zip `a67700ec` 138 entries, sources.zip `c99418c9`, both PR diffs byte-equal to the delivered series; DL-47 extended with the GC-01 site `GSW/Eval.lean:262–264`); exchange `outbox/gates/43-gsw-fills-gate/` at `14e681e6cfe2e70fb5248fbf2938a024290b061d` (on `641d7af7`; 12 files; 11/11 from a fresh archive). Put to Codex: proofs of all 35 targets; frozen statements; duplication incl. GC-01..06 and GS-01..06, with GS-02(c) (`distAdv_comp` is in an allowed import: is F6's relabelling at `Security.lean:225–232` an undisclosed re-proof?) graded on its own; Rule 10; sources (`[Vad12]` cited in `Columns.lean` is not registered in `sources.json`); merge condition: a combined build of both (expected admissions 237 → 202). Also: GC-05 tooling note filed in `maintainer/tooling-followups.md`; the empty `fills/gsw-core/final-r1/evidence-SHA256SUMS` refilled from the zip's manifest. GS-01 awaits Seyoon. | Ready to dispatch |
| 2026-11-16 | **#327 and #324 merged** (tip `201bf57a`; Pass–shelat code only, none of #338's or #339's files, no name clash). Gate 43 dispatch prompt refreshed: only the merge-condition sentence changed (a combined build of #338 × #339 on the new tip is a maintainer merge condition; expected admissions 229 → 194); pins unchanged. | Gate 43 ready to dispatch |
| 2026-11-16 | **Gate 43 dispatched** (Seyoon; Codex) at #339 `839f36cc` and #338 `d45d3682`, exchange `14e681e6`, records pin `4ed91289`, with the refreshed prompt (merge-condition sentence after #327/#324). Awaiting findings. | Gate 43 out |
| 2026-11-16 | **Gate 43: CLEAR → CLOSED** (Codex; both heads; 0 blockers, 0 majors; #339 0 minors/6 notes, #338 2 minors/4 notes; `findings/gate43-gsw-fills-findings.md` `19ac93e0`; `resolutions-r1.md`). All 35 proofs accepted on the Gate 41 routes; frozen surface byte-identical; no further duplicate; Rule 10 passes. GS-02 erratum and corrected P-1 stand; GS-02(c) `distAdv_comp` is not a re-proof; GS-03 reconstructed to the manifested hash. Follow-ups: shared `Regev.augmentedEquiv` (GS-06) added to DW-4; `[Vad12]` registration added to DW-7; GS-04 `.pyc` note for future briefs. No Lean change. Remaining merge conditions: GS-01 ruling (#338) and the combined build #339 × #338 on the current tip (expected 229 → 194), queued with #331's. | Gate 43 closed; GS-01 + combined build |
| 2026-11-16 | **Ruling GS-01 (Seyoon): ledger debt with payback P-1.** Ledger row DL-50 (`Columns.lean:95–192`; `Security.lean:197–238`, `256–279` against `Regev/Experiments.lean`); P-1 as restated in GS-02 (shared-parameter `pairHybrid`/`pairRed`). #338's only remaining merge condition is the combined build #339 × #338 on the current tip. | GS-01 ruled |
| 2026-11-16 | **Phase-6 rulings (Seyoon): P6-Q1 to P6-Q13, plus a location ruling** (`briefs/lattice-gsw/phase6/rulings.md`). Eight are as recommended (Q1, Q2, Q5–Q8, Q12, Q13). The five changes: Q3 both Barrington directions (BWBP = NC¹); Q4 the general branching-program model with `IsPermutation`; Q9 NAND-only bootstrapping via a new DAGCircuit-to-NAND conversion; Q10 asymptotic `WeakCircularSecure` and asymptotic IND-CPA now (conditional on reduction efficiency); Q11 the full leveled scheme now (L+1 keys, IND-CPA from DLWE). **Location:** branching programs, Barrington and the NAND conversion go in `Complexity/` as general model-of-computation facts (proposed `Complexity/BranchingPrograms/`, `Complexity/CircuitComplexity/NANDForm.lean`; the formula layer in `Complexity/CircuitComplexity/FormulaArith/`). One phase 6, with statement gates **45** (6a, complexity) and **46** (6b, cryptography). Next: revise `plan-section.md` to the rulings (statement prep), then the 6a statement draft on a free olean tree. | phase 6 ruled |
| 2026-11-16 | **Phase-6 plan section r2** (`briefs/lattice-gsw/phase6/plan-section.md`, revised to the rulings; no Lean run). **6a under `Complexity/`:** the general BP model with `IsPermutation`, the classes `InBWBP`/`InPBP`, and the push-form host `evalWith`/`evalWith_rel`; Barrington Thm 1 (computable conjugator) and Thm 2; the corollary in a fifth file `BranchingPrograms/NC1.lean`; the NAND conversion as an instance of `DAGCircuit.rewrite`; the formula-arithmetic layer with facade `FormulaArith.lean`; owner PRs O1 (`combine` promoted as `TreeCircuit.balanced`) and O2 (`decode_iff_mem_Ico`). **6b:** NAND-only bootstrapping, the concrete and asymptotic security statements (`ReductionEfficient`), the full leveled scheme, and the ratio statements. Units go from 10 to 18 plus O1/O2; fill lines from 2,150–3,400 to 3,340–5,390; the statement surface is about 2,800–3,300 lines in 19 files. The Bar89 ingest covers Thm 2 fully (p. 153, `p004-b003`); Gen09 (the key chain) is not ingested. New questions **P6-Q14 to P6-Q19** (moved into `questions.md`) for Seyoon; Q15 flags that the ruled concrete `WeakCircularSecure` over all distinguishers holds only for ε near 1. | phase-6 plan r2; Q14–Q19 |
| 2026-11-16 | **Phase-6 rulings P6-Q14 to P6-Q19 (Seyoon).** Q15, Q16, Q17 and Q18 are as recommended: the per-distinguisher concrete `WeakCircularSecure` with the asymptotic family as the headline; NAND form as a `DAGCircuit` predicate through `rewrite`; registry rows H18–H20; Thm 2 as a `TreeCircuit` formula. **Changed:** Q14 uses the consecutive key chain plus a new generic **layering conversion** in 6a (`Complexity/`); Q19 **ingests Gen09** (needs the PDF from Seyoon; only 6b's leveled statements wait). Plan section to r3; 6a issue package for an external Claude statement job next. | Q14–Q19 ruled |
| 2026-11-16 | **P6-Q19 refined (Seyoon): Gen09 is not a bottleneck.** The 6b leveled statements proceed now, citing the ingested BV11 Thm 3.1, BV14 Thm 2.14 and AP14 §5.3 and disclosing the reconstruction. The [Gen09] citation is a docstring-only follow-up after the ingest (PDF later today). | Gen09 non-blocking |
| 2026-11-16 | **Phase-6 plan section r3 and the 6a statement-job package** (`briefs/lattice-gsw/phase6/plan-section.md` r3, SHA-256 `06824b3d`; `issued-6a-r1/`). r3 applies Q14–Q19. Q14 B: the consecutive chain over layered circuits, with a new 6a unit U7 `DAGCircuit.layerNAND` in `Complexity/CircuitComplexity/NANDLayering.lean` (`IsLayered`, `litInput`, N7–N13). Design within Q14 B: odd gaps are handled by a parity twin per vertex plus the `x, ¬x` literal inputs, because layered monotone-input NAND circuits cannot compute XOR; this is free in GSW, where `G − C` keeps key and noise (for Seyoon to confirm). Follow-on: G7/G9 return to BV14's single key block. Q15 A applied; Q19 needs no [Gen09] tag before the ingest. Totals: 19 units (6a 11, 6b 8) plus O1/O2, 72 target rows (about 102 lemmas), fill lines 3,450–5,580. **6a job** (external Claude, lead plus 2 sub-agents): O1 (`TreeCircuit.balanced`, with three Rule 10 repairs) then the 6a statements under `Complexity/`, registrations and registry rows H18–H20; base `f6f295a6`; delivery to `inbox/fills/gsw-6a-statements/`; checkpoint 1 at O1 plus Defs, Eval and NANDForm; a fallback split into 6a-1 (circuits) and 6a-2 (BPs). Gap noted for the fills: `GadgetCorrect` has no `_iff` reader (a one-line owner-side change for N2). | 6a package staged |
