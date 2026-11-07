# LWE and SIS constructions

## Scope and ownership

The user approved this scope on 2026-11-07 (America/Los_Angeles):

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

All work belongs to this PR branch:

| Item | Identity |
|---|---|
| Worktree | `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-crypto-parallel-kickoff` |
| Branch | `cryptography/lwe-sis-constructions` |
| Target | `cryptography/pass-shelat-ch2-4` |
| Original kickoff baseline | `9db11986edfce462d91958856a763577ee15457f` |
| Implementation baseline | `869c0d55bb1c4132ba8ccf4d636ea2184ef8bd49` |
| Lean | `leanprover/lean4:v4.25.0` |
| Mathlib | `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |

Both baselines were read with `git rev-parse`. The implementation baseline was confirmed
through the GitHub connector and fast-forwarded in this worktree only. Its Lean sources,
root exports, toolchain and manifest match the original baseline. Shell GitHub fetch is
blocked by DNS restrictions; no successful shell fetch is claimed.

Do not edit the maintainer's campaign checkout or any Pass--Shelat records. Frozen
Gate06 source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` and PR #232 belong to their
maintainer. Do not merge that branch as a shortcut to its APIs. Do not access or mutate
the Arora--Barak campaign checkout or exchange namespace. No external job is dispatched.

## Organization

Problem definitions and assumptions belong under their problem; constructions belong
under their primitive. A matching facade imports each topic's children.

| Directory under `TCSlib/Cryptography/` | Owner-side content |
|---|---|
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

The browsing service exposed these author versions. Direct shell retrieval of source
PDF bytes is currently blocked by DNS restrictions. No PDF checksum, byte identity,
reference ingestion, proofmatch, or bibliography registry update is claimed. Before
shipping a source-fidelity gate, archive and hash the exact source versions and arrange
the normal reference ingestion. Changes to shared source registries need a separate,
reviewable diff. Purely implementation-oriented sampler records cite their deviations.

The direct symmetric scheme is the elementary noisy-inner-product encryption obtained
from the LWE distribution: add the encoded bit to a fresh sample's last coordinate.
Its exact source anchor is to be checked before its statement gate; it is not silently
attributed to the generic PRF scheme or to a particular numbered PKE algorithm.

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

### D2. Noise laws versus implementations

The first implementation-facing model is a scalar integer sampler from a finite,
nonempty uniform seed type. It specifies its induced noise law, not uniform noise on
its support: repeated seed images retain their multiplicities. Taking an independent
seed per coordinate gives the product law. Bit samplers are an additional refinement;
efficient samplability is a separate machine obligation.

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

PW10's lattice functions are originally almost-always injective/invertible. The existing
PKE correctness requirement must be met by an explicit bounded-noise specialization or
another checked argument, not by ignoring the bad-key event. The CCA proof retains the
full ciphertext's signature verification, inversion, canonical parsing, recomputation
checks and exact challenge-ciphertext exclusion.

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

Root exports are a separate small commit. Phase 0's proposed additions are:

```lean
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
```

These are a proposed export diff, not a claim of root elaboration or merge clearance.
Other primitive facades are added as their checked phases become available. Every PR
calls out root/facade overlap explicitly.

## Verification and current execution limits

Use only this branch's `.lake/packages/` and fresh
`TCSLIB_OLEANS=<worktree>/.lake/crypto-parallel-oleans`. Do not use another chat's
TCSlib scratch objects. The installed Lean 4.25.0 executable has been checked. Disk
space exceeds 400 GiB. Process inspection via `ps` is denied by the execution sandbox;
current native/cache job activity therefore cannot be established. Resource-heavy
cache/native work is deferred while this is unresolved; source/review work continues.

Check one module at a time through `scripts/lean_check_tree.sh`. No `lake build`, no
unfiltered cache download, no package changes in another checkout, no borrowed scratch
oleans, and no killing another job. Only required Mathlib roots at the manifest pin are
eligible for the isolated cache. Python commands use `python3 -I`.

## Decision log

| Date | Decision/evidence | Status |
|---|---|---|
| 2026-11-07 | User selected the five headline constructions; SIS assumption independent of LWE. | Approved scope |
| 2026-11-07 | User approved problem/primitive folder organization and secret-matrix trapdoors for CCA2; excluded short bases/Gaussian preimage sampling. | Approved scope |
| 2026-11-07 | Own branch renamed; own checkout fast-forwarded to the remotely verified baseline. Other worktree branches verified unchanged. | Executed |
| 2026-11-07 | Native/cache activity cannot be inspected in this sandbox; heavy checks deferred. | Open environment constraint |
