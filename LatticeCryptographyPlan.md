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
| Active worktree | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-lwe-sis-phase1` |
| Active draft PR branch | `cryptography/lwe-sis-phase1-statements` |
| Central integration branch / PR target | `cryptography/lwe-sis-constructions` |
| Observed central head | `2c37f3f486822a52f4a9e337c6b742e995ebb118` |
| Audited dependency / phase-1 baseline | `0769cba3e44c56700349f954190fc99d9e622270`, PR #236 |
| Phase-1 frozen Lean/root | `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf` |
| Upstream campaign context | `cryptography/pass-shelat-ch2-4` at `74b02c1d5c1dcea241c95d625586a7a324925cc9` |
| Original kickoff baseline | `9db11986edfce462d91958856a763577ee15457f` |
| Implementation baseline | `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49` |
| Lean | `leanprover/lean4:v4.25.0` |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

Both baselines were read with `git rev-parse`. The implementation baseline was confirmed
through the GitHub connector and fast-forwarded in this worktree only. Its Lean sources,
root exports, toolchain and manifest match the original baseline. Shell GitHub fetch is
blocked by DNS restrictions; no successful shell fetch is claimed.

The active draft was initially created from the remote-verified campaign context and
the audited foundation. When the user selected a central LWE/SIS integration branch,
its two unpublished code/export commits were replayed onto the audited dependency,
removing unrelated campaign-record ancestry. Every checked Lean/pin byte was unchanged.
Client publication has now retargeted PR #236 to the central branch and opened
draft PR #237 there. The published new draft head is
`1b148307150a0b0a08dd80d68c54ba2db95de13c`. Its dispatched statement-audit input
is exchange `90d652e19508262b3bd81234260d0585aaf8e0a0`; source and records pins
are unchanged. The eight mathematical modules remain frozen while review runs.

## Current construction statement phase

The separate phase-1 draft contains eight mathematical modules: explicit polynomial
sample replacement, canonical modular parsing, bounded-error bit decoding, direct
Regev symmetric encryption and its concrete two-DLWE bound, and SIS binary hashing
with a collision bound and dyadic profile. It has 62 source declarations, including
31 explicitly admitted theorem obligations. No nontrivial proof fill has started.

The fresh serial scoped sweep covers 68 modules and retains 17 inherited warnings.
It is not a whole-library root build. The new facade/root exports are isolated in
commit `a1f1b2e0d9315dff2a8dc36e2a6f8339c0a5abdf`; the construction-core commit is
`56cabe7f3` (full history and hashes are in the phase-1 records). Existing owner
APIs and pins are unchanged. The next gate is a statement review, not a claim of
completed encryption/hash security or machine efficiency.

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
the Arora--Barak campaign checkout or exchange namespace. No external job is dispatched.

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
`TCSLIB_OLEANS=<worktree>/.lake/phase1-final-oleans`. Do not use another chat's
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
