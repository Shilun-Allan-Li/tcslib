# Phase 1 mathematical and API contracts

Internal design at the identities in [README.md](README.md). All formulas below
are mathematical obligations for future statement PRs, not completed Lean proofs.
Paths in this document are relative to `TCSlib/` unless specified otherwise.

## Direct Regev symmetric encryption

Source: [Wu24, Definition 20.5 and Lecture 21, printed pp. 80–82](https://www.cs.utexas.edu/~dwu4/courses/sp24/static/notes.pdf).
Use the noisy-inner-product construction from that source. Adapt it to the
repository's parameter-length messages, row-oriented LWE convention and perfect
correctness requirement. Resolve rounding and boundary cases explicitly rather
than copying the notes' informal rounding notation.

At security parameter \(\kappa\), let the LWE dimension be \(n\), the modulus
\(q\ge2\), and the scalar noise be the actual law specified by `LWE.Noise`.
Key generation samples one uniform secret \(s\in\mathbb Z_q^n\).
For a message \(\mu\in\{0,1\}^{\kappa}\), sample a uniform matrix
\(A\in\mathbb Z_q^{\kappa\times n}\) and independent errors \(e_i\), and output

\[
\bigl(A,\ As+e+\lfloor q/2\rfloor\mu\bigr).
\]

The Boolean vector is cast coordinatewise to residues. Encode this pair using
`LWE.encodeChallenge` with exactly \(\kappa\) rows. The whole batch uses one secret,
fresh matrix entries and independent scalar-noise seeds. The mathematical scalar
law and its bit-sampler implementation must agree, including seed multiplicities.

`Cryptography/Asymptotic/Encryption.lean:150` defines `PrivateKeyScheme` with
arbitrary `List Bool` keys/ciphertexts and messages `Fin κ → Bool`. Thus the
complete uniform secret fits directly. No separate single-bit scheme type or
change of security parameter is needed.

### Correctness and representation contracts

Subtract \(As\) and decode each coordinate to its nearest codepoint among
\(0\) and \(\lfloor q/2\rfloor\), using a specified total tie rule. Let
\(B\in\mathbb N\) bound every sampled error's absolute value. The sufficient
condition is

\[
2B<\lfloor q/2\rfloor.
\]

To justify this condition, write \(d_q\) for circular distance on the residues.
The codepoints have distance \(\lfloor q/2\rfloor\). A valid residual is within
\(B\) of the intended codepoint. The triangle inequality puts its distance to
the other codepoint at least \(\lfloor q/2\rfloor-B>B\). Thus every valid
encryption has a unique nearest codepoint, for either bit and either error sign.
This proof must include the circular-distance facts and the boundary parameters.
It cannot use a negligible Gaussian tail to inhabit an every-coin correctness field.

Add a canonical parser in a new `Cryptography/Encoding/ModularDecode.lean`:
reject wrong total lengths and entry representatives outside the modulus, prove
both canonical round trips, and give explicit behavior on every malformed input.
The current encoders' injectivity alone is not a parser or an efficiency theorem.
Keep their audited files unchanged. Reuse `Candidates.listToNat_natToList`,
`natToBits_bitsToNat` and `natToList_length_listToNat` through their public lemmas.

For an exact first implementation choose \(q=2^k\), with \(k\) polynomially
bounded and uniformly computable, and an explicit \(r\)-bit scalar-noise sampler.
The raw lengths are

\[
\begin{aligned}
\text{secret/key-generation coins}&=nk,\\
\text{encryption coins per message}&=\kappa(nk+r),\\
\text{compact ciphertext}&=\kappa(n+1)k.
\end{aligned}
\]

If these numeric schedules have only syntactic polynomial upper bounds, unused
coin padding needs its own projection/product-law accounting. It must not alter
the secret distribution. `LWE.Family` itself supplies no uniform parameter or
noise-computability contract. An executable profile must supply these separately.

### Required DLWE quantifiers

`PrivateKeyScheme.MultiMessageSecure` at
`Cryptography/Asymptotic/Encryption.lean:208` quantifies over a syntactic
polynomial \(Q\) and encrypts \(Q(\kappa)+1\) parameter-length messages with one key.
Therefore its direct reduction requires

\[
M(\kappa)=\kappa\bigl(Q(\kappa)+1\bigr)
\]

common-secret LWE samples. The extra one is part of the existing API.
`DLWEAssumption F` covers the sample schedule already stored in \(F\); one fixed
schedule does not cover every such \(M\).

Propose a new `Cryptography/LWE/SampleSchedules.lean`, with a structure-valued
`Family.withSamples F M` that preserves dimension, modulus, noise and residue
width and replaces only the sample count and its polynomial bound. Its public
field equations must be published beside it. The construction's hardness input
is explicitly

```text
∀ M : PolyExpr, DLWEAssumption (F.withSamples M).
```

This is an additional outer quantifier using the existing named assumption,
not a change to `DLWEAssumption` or a sample-amplification theorem. A result for
one selected message-count polynomial may instead assume just its required schedule.

For each fixed message vector, split the batch into messages, add its codepoints
and form the repository's `encodeList` ciphertext tuple. The real experiment is
exactly this postprocessing of an LWE sample. In the ideal experiment, translation
of the uniform value vector is a bijection and hides the whole message vector.
For any two vectors, the triangle inequality bounds their distinguishing
advantage by the two corresponding DLWE reduction advantages. There is no PRF
construction in this route.

For the API's quantifier order, a separate negligible bound for each arbitrarily
chosen message pair is insufficient. At each parameter choose a maximizing pair
from the finite message space, encode it as polynomial-length advice, and build
the two reductions for that sequence. Their negligible sum then bounds every
message pair. Reuse the existing worst-message argument in
`Cryptography/Asymptotic/MultiMessage.lean:647` and
`Complexity/Randomized/Closure.lean:360`, `NUPPT.exists_withAdvice`; do not assume
the maximizing messages are uniformly computable.

### Efficiency and the CPA boundary

| Existing public construction | Use |
|---|---|
| `HardcoreBit.pushesUniform_add_right`, `Cryptography/HardcoreBit/Basic.lean:201` | Uniform translation |
| `acceptProb_comp_equiv`, `Cryptography/Foundations/Experiments.lean:107` | Coin relabeling |
| `NUPPT.exists_compParam`, `Complexity/Randomized/Closure.lean:246` | Parameter-aware preprocessing/postprocessing |
| `NUPPT.ofPolyTimeUniform`, `Complexity/Randomized/PPT.lean:379` | Uniform honest algorithms after functional efficiency is proved |
| `polyTimeComputable_stateFind`, `Complexity/Randomized/Repetition.lean:241` | Existing state/iteration host |
| `polyTimeComputable_blockMap`, same file `:467` | Fixed-width block processing |
| `blockEncFun_poly`, `decListFun_poly`, `Cryptography/Asymptotic/BlockEncryptor.lean` | Optional nested-tuple implementation; the argument called `pk` can carry an arbitrary key string |
| `coinBlocks`, `Cryptography/Asymptotic/PublicKeyLemmas.lean:88` | Independent encryption-coin blocks |

The required additions are leaves/adapters built through these hosts, not private
replacement loop or parser hosts. Check their transitive axiom dependencies at
the consumer gate; this records-only inventory did not run a native probe.
`Candidates.ArithmeticFP` is an explicit conditional bundle and does not establish
unconditional arithmetic efficiency. The available `Complexity.BinArith` arithmetic
uses little-endian normalized words, whereas the candidate encoders use fixed-width
most-significant-bit-first words. Supply a proved conversion and width adapter.

The present `SingleMessageSecure` and `MultiMessageSecure` are nonadaptive
message-vector notions. No private-key adaptive CPA predicate was found in this
base. `Games.exists_handlerMachine`, `Cryptography/Games/Efficiency.lean:300`,
still has a `sorry` body. An adaptive CPA endpoint needs a coordinated owner
interface and an honest account of that host dependency. Do not label only the
existing multi-message theorem as adaptive CPA security.

## SIS binary matrix hashing

Source: [Pei16, Definition 4.1.1, Equation (4.1.1) and following observations, printed pp. 18–19; §5.1](https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf).
Use the binary-domain matrix hash. This section derives the elementary consumer
obligations directly; it uses neither a lattice reduction nor a bridge from LWE.

For \(A\in\mathbb Z_q^{n\times m}\), set

\[
h_A:\{0,1\}^m\longrightarrow\mathbb Z_q^n,\qquad h_A(x)=Ax.
\]

If \(x\ne x'\) and \(h_A(x)=h_A(x')\), define the integer vector
\(z_i=\operatorname{Bool.toNat}(x_i)-\operatorname{Bool.toNat}(x'_i)\).
Then

\[
z\ne0,\qquad A(z\bmod q)=Ax-Ax'=0,\qquad
z_i\in\{-1,0,1\},\qquad \sum_{i<m}z_i^2\le m.
\]

Nonzeroness follows because the two Boolean values have distinct integer casts
at a coordinate where the inputs differ. Each square is at most one, proving
the sum bound. Thus `SIS.IsSolution` follows whenever `sqNormBound ≥ m`.
Use the current `SIS.isSolution_iff` reader and the proved signed-output decoder
completeness theorem. No field or primality assumption is needed.

### Concrete dyadic profile

Let \(t=\kappa+1\), and choose

\[
n=t,\qquad q=2^t,\qquad m=2t^2,\qquad
\texttt{sqNormBound}=m,\quad\texttt{residueBits}=t,\quad
\texttt{magnitudeBits}=m+1.
\]

These are a candidate implementation profile and elementary inequalities, not a
hardness proof. The future theorem assumes `SISAssumption` for this actual family.

* **Compression and existence.** The binary domain has cardinality
  \(2^{2t^2}>2^{t^2}=q^n\), because \(t\ge1\). Pigeonhole gives a collision for
  every matrix; the preceding argument gives a valid SIS solution for every matrix.
* **Exclude trivial modulus multiples.** \(m<q^2\) for all \(t\ge1\).
  Base: \(2<4\). If \(2t^2<4^t\), then
  \(2(t+1)^2\le8t^2<4^{t+1}\), since \(t+1\le2t\).
  Any nonzero vector in \(q\mathbb Z^m\) has a coordinate of absolute value at
  least \(q\), hence squared norm at least \(q^2>m\). This excludes those
  trivial solutions, not every possible easy instance or attack.
* **Representation coverage.** \(m<2^{m+1}\), so the existing family's
  conservative magnitude-width condition holds. Residues fit with equality
  \(q=2^t\). All widths and dimensions are syntactic polynomials in \(\kappa\).

The exact bit budgets are

| Item | Bits |
|---|---:|
| Hash input | \(2t^2\) |
| Hash output | \(t^2\) |
| Matrix index and key-generator coins | \(nmt=2t^4\) |
| Prescribed signed SIS output | \(m(m+2)=4t^4+4t^2\) |

For uniform matrix sampling, prove the bijection from the key-generator bits to
matrix entries, using `bitsEquiv`, `bitsEquiv_val` in
`Cryptography/Asymptotic/Sampling.lean` and the pinned `ZMod` equivalence. The
matrix's canonical encoding then has exactly the same uniform distribution as
the SIS challenge. This dyadic profile has no rejection-sampling error.

For evaluation, parse the matrix, sum its selected columns modulo \(2^t\), and
encode the result with `Encoding.Modular.encodeVector`. Reuse the proved addition
body at `Complexity/ClassP/BinaryArith/AddSub.lean:162` and the registered iteration
hosts; provide the endian/width conversions and output-length contract. Honest
and malformed inputs both need total polynomial-time behavior. No general
modular division is needed for this profile.

The collision-to-SIS output machine is simpler: each pair of input bits gives
the sign and magnitude for \(-1,0,1\) by a four-case Boolean table. It does not
need a general signed-integer subtraction or hash-evaluation routine. Assemble
its exact signed blocks with the existing block/iteration hosts and prove that
the result is `SIS.encodeSolution` of the integer difference.

### Existing CRH owner and parser semantics

The current code base has no public CRH structure. The prospective owner is
`Authentication.CRH` in `Cryptography/Authentication/Defs.lean`, inspected only
at frozen Pass–Shelat source
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b` under its maintainer's PR #232.
It supplies `domLen`, `rangeLen`, `gen`, `eval`, domain/range membership,
`Compresses`, `collisionGame` and `CollisionResistant`. This is a future
dependency; do not edit that file, merge the frozen branch or copy its API.

Its game reads the finder's raw output using `padFin (domLen + domLen)` and
then `splitBits`. This pads short outputs and truncates long ones. The SIS
reduction must perform exactly the same operations before forming the difference.
Rejecting a raw word solely for wrong length would lose collisions accepted by
the primitive's game. The SIS output itself must have the exact signed format.

For the dyadic profile, take all domain and range bit strings as valid. Evaluation
has exact output length, so padding the hash output is inert. Compression follows
from the cardinalities above for every generated index, including parameter zero
since \(t=1\). For each collision finder construct a parameter-aware postprocessing
machine with `NUPPT.exists_compParam`; it retains the finder's coins and advice.
Coin relabeling and `Games.Bridge.prob_sample_pair`
(`Cryptography/Games/Bridges/Experiments.lean:81`) relate the two experiments and
give collision probability at most that machine's `SIS.Family.successAt`.
Negligibility then follows from the explicitly assumed `SISAssumption`.

## Proposed owned modules and review boundaries

| New module under `Cryptography/` | Responsibility |
|---|---|
| `LWE/SampleSchedules.lean` | Schedule replacement, all field equations and explicit sample quantification |
| `Encoding/ModularDecode.lean` | Canonical parsers, rejection equations and round trips |
| `LWE/BitEncoding.lean` | Shared codepoints, decoder and bounded-error correctness |
| `Encryption/Symmetric/Regev/Basic.lean` | Direct mathematical algorithms and correctness statements |
| Same directory, `Machines.lean`, `Security.lean` | Uniform implementations and batch/multi-message reductions |
| `Hashing/SIS/Basic.lean`, `Profiles.lean` | Binary matrix hash, collision solution, profile and compression |
| Same directory, `Machines.lean`, `Security.lean` | Exact bit implementations and future CRH bridge |

Every public definition needs its owner-side non-simp readers, and nontrivial
statements need source tags, deviations and sketches at statement time. These
module names are a design proposal, not changes to existing owner APIs.
Root/facade exports stay small and separate. Any required shared-host or adaptive
CPA owner change needs an exact proposed diff and coordination through the user
before implementation. The CRH bridge consumes the maintainer's approved API
after landing; independent SIS algebra can proceed first.

## Notation glossary

\(\kappa\): security parameter and symmetric message length. \(n\): LWE secret
dimension or SIS matrix row count, as specified in each section. \(m\): SIS
column count. \(q\): modulus. \(k\): residue width for a dyadic LWE profile.
\(r\): scalar-noise seed width. \(B\): bound on absolute scalar errors.
\(s\): shared uniform LWE secret. \(A\): public uniform matrix.
\(e\): independently sampled scalar errors, collected as a vector.
\(\mu\): symmetric plaintext bit vector. \(d_q\): circular residue distance.
\(Q\): polynomial message-count budget. \(M\): required sample-count polynomial.
\(F\): base LWE family. \(h_A\): SIS matrix hash. \(x,x'\): binary hash inputs.
\(z\): their integer difference; subscripts denote coordinates.
\(t=\kappa+1\): shifted parameter of the candidate SIS profile.
\(\mathbb Z_q\): residues modulo \(q\). \(q\mathbb Z^m\): integer vectors
whose coordinates are multiples of \(q\). \(\lfloor\cdot\rfloor\): floor.
