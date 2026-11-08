# Gate 06C, round 1: external Codex findings

**Verdict: PASS WITH MINORS — 0 blockers, 0 majors, 4 minors.** The specified statement gate meets its closure criterion. This verdict concerns the frozen trusted surface and its short correctness arguments; it does not complete the admitted security/composition proofs or clear the other Gate 06 prongs for merge.

## Scope and identity

| Item | Audited identity |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange snapshot | `5928e06c02b382b63b9b384db89d0458b520f351` |
| Lean source | `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` |
| Records | `c81baa7712ab1b43357276ef5df138d02616c9d0` |
| Checked comparison ancestor | `eee107e92a7db11f1f8c98a5c2867304f57ddc54` |
| Issued brief | `briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements/06C-pack.md` at the records pin |
| Primary scope | The eight `TCSlib/Cryptography/Composability/*.lean` modules and their facade; imported owners are context |

All source locations below refer to the frozen Lean source. No campaign branch was checked out, edited, committed or pushed. Inspection used extracted copies and read-only Git object access.

I checked definitions, theorem statements, attribution and sketches, including the construction correctness fields, padding correctness, the repetition phase lemma and the short derived corollaries. I inspected comment-stripped declarations before their prose comparison. The appendices separately cover all **72 explicit definitions/types/abbreviations and 161 explicit theorems**, including the private XOR lemma; generated public projection equations are addressed separately. Substantive admitted proof bodies remain outside proof-completion scope.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| C-01 | minor | `CCA2Scheme.lean:111`, `ccaDecOK`; module source note at line 37 | Every malformed ciphertext is rejected. | At `n=0`, the generated key has both components empty. The four-bit ciphertext `0000` is not a pair, but all default projections are empty. Both length checks hold and `hFE` at parameter zero makes the computed tag empty, so decryption returns the valid empty message. See the calculation below. | Check successful/canonical parsing of both ciphertext pair layers, or qualify the malformed-rejection prose by `n>0` and disclose the parameter-zero behavior. A canonical parsing guard is the cleaner algorithmic repair. |
| C-02 | minor | `CCA2Scheme.lean:369`, `ccaScheme_cca2`, sketch step 2 | Every fresh decryption attempt checks a fresh random-function value and has success probability `2^(-2n)`. | “Fresh” excludes prior encryption/challenge inputs, but does not exclude prior decryption inputs. At positive `n`, after one failed tag guess at a fixed input, a different guess succeeds with conditional probability `1/(2^(2n)-1)`. The stated total `q/2^(2n)` bad-event bound is still obtainable. | Couple to a game that rejects every fresh-pair decryption query. Before the first discrepancy, its guesses are independent of the unrevealed tag; union-bound those guesses. Alternatively, use a properly conditioned lazy-sampling analysis. |
| C-03 | minor | `SequentialZK.lean:380`, `ZK.seqRep` sketch steps 2–3; `StatZK.seqRep` inherits the construction | Truncating each simulated prover message to `B(n)` suffices for the asserted polynomial bound on the accumulated history. | A computational/statistical phase simulator may, with negligible positive probability, output a view with too many messages. Truncating message lengths leaves that count uncontrolled. A simulator can use its rare branch to output quadratically many empty messages in its auxiliary-input length; iterating that branch can violate strict polynomial time. This does not refute either theorem. | Normalize each phase output to the prescribed number of prover messages as well as the per-message length, inserting the known empty fillers. Map malformed phase views to a fixed canonical phase view. This efficient normalization fixes every real phase view, so the hybrid/statistical arguments survive. |
| C-04 | minor | `CCA2Scheme.lean:30`, module counterattack on tagging only `c1` | The constructed altered query is necessarily different from the challenge. | If the selected plaintext is `0^n` and the auxiliary encryption happens to use the challenge nonce, its masked message and short tag coincide with the challenge's, so the proposed query is exactly the refused challenge. Conditional on that selected plaintext, this event has probability `2^(-n)` for every evaluator. | Branch explicitly on ciphertext equality and charge this branch, together with other accidental masked-message collisions, to a negligible failure event in the PRF/random-function analysis. The short-tag construction remains insecure; the displayed attack is overwhelmingly successful rather than unconditionally query-distinct. |

None of these findings supplies an asymptotic security counterexample to a headline statement. C-01 affects a finite parameter prefix; C-02 through C-04 repair local sketch details without changing theorem statements.

### C-01: exact zero-parameter calculation

The pairing used by the code doubles the first component, then appends the separator `01` and the second component. Thus

\[
\operatorname{pairEncode}([],[])=01,
\qquad
c_{\mathrm{honest}}=\operatorname{pairEncode}([],01)=0101.
\]

For the different ciphertext `w=0000`, `pairDecode w = none`, hence

\[
\operatorname{pairFstD}(w)=\operatorname{pairSndD}(w)=[],
\quad r=c_1=t=[],
\quad |r|=|c_1|=n=0.
\]

For every evaluator satisfying the actual `hFE` premise,

\[
E(\operatorname{pairEncode}([],[]))
=\operatorname{List.ofFn}(F\ 0\ (\text{empty function})\ (\text{empty function}))
=[].
\]

Therefore `ccaDecOK E z = true` on the valid machine layout containing this key and `w`, and `ccaDecFun E z = []`. Its decoding at message length zero is `some` of the unique empty message. The game accepts four-bit ciphertext queries at `n=0`, so this is an actual malformed query in its domain, rather than a test on an inadmissible length. At positive `n`, successful length tests force successful parsing: a failed parser has empty projections and cannot supply an `n`-bit nonce or first ciphertext component. Valid pair parsing is unique, so this example does not extend to positive parameters.

The inherited Algorithm 99.1 guard uses the same default-projection pattern and has the analogous parameter-zero caveat. Its positive-parameter guard repair is present and protects the evaluator domain as intended; this audit does not reopen that prerequisite as a new gate.

## Integrity and verification

Both supplied `SHA256SUMS` files verified in full: nine listed files in `06C-r1-gate` and five in `06-common-r1-gate`. The following independently computed hashes match the dispatch evidence:

| Artifact | SHA-256 |
|---|---|
| `gate06C-source-bundle.md` | `15dfbca8d2d255b5b31bd71393a8c87bd7b88946cd46c9a3a2ff32a65a34654b` |
| `gate06C-source-manifest.json` | `f649a5fa5ff1dee8395586345f0dc1a22efab783e850f46185e7230fbfb1406b` |
| `gate06C-records-bundle.md` | `bbe2dd42b94e591abdb7976f19c60473d48f4000dba8962d881e73bd041be7c0` |
| `gate06-common-evidence.zip` | `960ab0c708c9efdd9a5ef01175889afa0b97be0984e35ace25f4001265ee0749` |
| `FINAL-EVIDENCE.md` | `0e011edc90d469d1b3dd1156a74f6f7856f756e15e085343486a232ea24aa73b` |
| Provided `Pass-Shelat.pdf` | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` |

I verified the bytes and lengths of all **171 source sections** against the source manifest and the raw Git objects at the stated source pin. All **20 records sections** match raw Git at the records pin. All **3,419 archived evidence entries** match the byte counts/hashes in `ZIP-CONTENTS.tsv`. The ancestor was used as the comparison base, not substituted for the final-head source.

The archived seal records for all eight Composability math modules report valid harnesses and successful source elaboration. I independently checked those eight raw log hashes and found zero error diagnostics in them. These are observations about the provided runs, not new executions by this auditor. The common archive still contains its other 17 failed source seals and the stated legacy observations; I do not convert that evidence into an all-library pass.

No Lean/lake executable was available on this auditor's normal executable path; I did not install a toolchain or perform an independent Lean elaboration. The short correctness arguments were checked mathematically against the actual bodies. Independent finite Python transcriptions additionally checked:

| Check | Coverage and result |
|---|---|
| Canonical-padding inverse | All 8,188 bit strings of lengths 2 through 12; every accepted string repads to itself at its own length |
| Encrypt/decrypt correctness and length | 33,825 key/message/nonce instances at `n=0,1,2,3`, using the length-preserving test evaluator `E(k,x)=k XOR x`; all decryptions and `6n+4` lengths agree |
| Malformed zero-parameter ciphertext | `0000` fails pair parsing and decrypts to the valid empty message, reproducing C-01 |
| Repetition phase identity | 160 phase instances: both first movers, `k=0,...,7`, `Q=0,...,4`, every `j<Q`, using history-sensitive deterministic strategies |
| Move-index recovery | Both first movers at global moves 0 through 100: 202 instances |

These transcriptions are finite checks of the encodings/control flow, not kernel proofs or tests of pseudorandomness.

The actual source has **13 direct admitted bodies** in the primary modules. The provided axiom census identifies **19 admitted-dependent Composability identities**: those 13 plus six derived results. In particular, the proved numerical negligibility estimate does not discharge the generic repetition premises used by the 3COL corollary. Neither this audit nor the archived successful elaborations fill those admissions.

## Source access and precise comparison limits

| Source | What I accessed and compared | Exact limitation |
|---|---|---|
| PS10 | The supplied, hash-verified 1,771,458-byte PDF; chapter 7 book pp. 167–176, Algorithms 99.1/104.3 and Theorem 104.4, and book pp. 124–129 for the 3COL uses. Book page is PDF page minus 12. Relevant chapter-7 pages were also rendered and inspected. | No alternative edition was substituted. |
| [PSV06 author PDF](https://www.cs.cornell.edu/~rafael/papers/PSV06a.pdf) | Directly retrieved 294,488 bytes, SHA-256 `f5087d68df8782e2ca0465ce511c9dd6778dea70052d666a8ff86bd85873a6e6`. Definition 3, PDF pp. 6–7, matches the one-challenge CPA experiment after the declared fixed-length encoding: the final observer sees decryptions, and challenge copies become bottom. | I did not obtain/compare the historical publisher-upload bytes with SHA-256 `7b470f4e3f26a56dbfd8956d4f07201ac163cbf716d4c0830b375ac022db8c49`. Author/publisher textual identity is unverified. |
| [PSV07 author PDF](https://www.cs.cornell.edu/~rafael/papers/newdefs.pdf) | Directly retrieved 226,230 bytes, SHA-256 `d0d6f5edd2527265d20213b35e2042e018ef7e357049cdd5d379ae1d0938c98e`. Checked Definitions 1–4 on PDF pp. 6–8 and Corollary 1/Theorems 3–4 on p. 9. The real/ideal simulator interfaces, COPY convention, CPA equivalence and CCA separation agree with the repaired attribution. | The linked 17-page version defers the relevant equivalence proofs. No longer proof version was available in the issued linked material. The historical publisher-upload bytes, SHA-256 `c899bf7cff4c8144ac28c31f703d567178f96e31ec9b28d6f4bddf4f337ea57d`, were not obtained/compared. |
| [Goldreich official chapter-4 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf), [official draft index](https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html) | The web PDF reader supplied the official 120-page chapter. Checked Definition 4.3.1, PDF p. 16/printed p. 142, and §4.3.4, including draft Lemma 4.3.9, PDF p. 28/printed p. 154. The strict aborting definition is distinct from the expected-time formulation; the sequential result uses auxiliary input and independent phase coins. | Direct urllib and curl byte retrievals returned HTTP 503. Consequently I could not recompute the manifest's PDF hash `97e67c3cae68701705839386a31f462803c6c9e6d1984638442010df99b6f977`. Content access through the official-URL reader succeeded, but byte identity with the recorded download is unverified. I did not compare against the published 2001 book or transfer draft pagination/lemma numbering to that edition. |
| Gar26 §1.2 and earlier probability/3COL dependencies | Contextual source tags and the consumed formal interfaces were inspected where needed. The new repeated-error estimate is also checked directly below. | I did not independently retrieve Gar26, KV94 or SSBD14 in this gate. This is not a fresh fidelity audit of those previously gated prerequisites. Goldreich volume 2 is outside 06C's requested comparisons. |

The author versions were compared directly, rather than accepting the maintainer's source summaries. Missing publisher comparisons and deferred proofs are not granted blanket fidelity approval. No third-party PDF, extracted full text or rendered source page is included in this deliverable.

## Answers to the issued questions

### 1. Oracle games and fixed lengths

For both private and public schemes, `decOpen` gives exactly:

| Attack | Before first challenge | After first challenge |
|---|---|---|
| CPA | Refused | Refused |
| CCA1 | Open | Refused |
| CCA2 | Open | Open, except the recorded ciphertext |

The first challenge records its ciphertext; every later challenge returns that same value without encrypting new messages. Repeating this query adds no information. An adversary can stop without a challenge, or with budget zero; then the IND/NM experiment has no dependence on the challenge bit. The machine framework permits a final return after its last permitted oracle call (`buildComp_zero_of_ret`), so the ideal simulator's budget of one really allows “query once, then output.”

The private model fixes plaintext length to the parameter and honest ciphertext length to `ctLen(n)`, and only offers decryption at that length. This is a declared restriction, not a theorem equating every arbitrary variable-length private scheme with this model. For the two private constructions here, valid positive-parameter ciphertext fields force exactly the stated total length; other-length decryption queries supply no omitted useful well-formed cases. C-01 records the finite zero-parameter exception. Public message length is an explicit polynomial, allowing the single-bit instance as well as `n`-bit messages.

### 2. Canonical public-key padding

At an admissible fixed length,

\[
\begin{aligned}
|\operatorname{padCt}(L,c)|&=2|c|+2+(L-2|c|-2)=L,\\
\operatorname{pairFstD}(\operatorname{padCt}(L,c))&=c,\\
\operatorname{isPadded}(w)=\mathrm{true},\ |w|=L
&\Longrightarrow\operatorname{padCt}(L,\operatorname{pairFstD}(w))=w.
\end{aligned}
\]

Thus there is one accepted padded representation per raw ciphertext at this length. A changed padding bit either fails the test or changes the underlying ciphertext; a second canonical representation of the challenge cannot bypass the challenge check. On a refused `L`-bit query, `padDecFun` returns `L+1` bits, which cannot decode to a message because the constructor requires `msgLen(n) ≤ L`. Correctness and the length proof use the same transported encryption coins.

There is a real, disclosed strength limit: this game only decrypts raw ciphertexts with `2|c|+2 ≤ L(n)`. Increasing `L` admits additional raw queries. I accept the explicitly indexed padded games; I do not infer unrestricted variable-length CCA security from one chosen `L`.

### 3. The bottom-valued non-malleability game

`nmGame` gives the adversary the public key, permits the attack's decryption calls, and applies the final distinguisher only to the vector of encoded decryptions. A challenge copy and an invalid decryption both become the all-false bottom code. This agrees with the selected CPA definition and with the declared convention; replacing those copies by distinguishable COPY markers would be a different experiment. The formal game also permits no challenge and zero output blocks, both harmless extensions: neither can create dependence on the challenge bit by itself.

### 4. The simulation experiment

`snmReal` instead exports separate COPY and validity bits. `snmIdeal` gives its simulator `pk`, no decryption oracle, and at most one query that chooses the sampler parameter and returns the history of the resulting hidden message. Its output can explicitly select COPY. The observer receives the parameter, sampled message, decrypted/COPY entries and auxiliary output, with all boundaries fixed by public length polynomials.

The sampler reparameterization is defensible: for a fixed sampler it explicitly quantifies every parameter-choosing adversary; conversely a clocked universal sampler can interpret a padded machine description and run it on `1^n`. The polynomial clock is fixed for the adversary class, and padding/truncating the sampled output gives the required fixed message length. A source history function is represented by choosing a large enough history bound; arbitrary truncation already defines another efficient history function. This is a polynomial-overhead encoding argument, rather than a new proved Lean bridge.

When no challenge/history query occurs, both experiments use the all-zero parameter, sample its message independently of the machine's pre-query behavior, and set no real copy flags. The simulator can reproduce that branch directly. Repeated real challenges preserve the first parameter and history; they do not resample the message.

### 5. Both non-malleability sketches

**SIM implies bottom-valued IND-NM for every attack.** Use a sampler that chooses uniformly between the supplied message pair and a constant history. On the event that the pair differs, the sampled message reveals the choice bit to the final observer. Mapping COPY to bottom makes the real output the corresponding NM output. In the ideal experiment the output entries are independent of that hidden choice conditional on the chosen parameter. Testing also whether the two parameter messages differ handles a simulator that changes that event's probability. The stated factor-two sum bound is sufficient. If the adversary never challenges, the default pair is equal and that branch contributes zero IND advantage. Forwarding the permitted real decryption calls does not give the ideal simulator a forbidden decryption interface.

**Bottom-valued IND-NM implies SIM under CPA.** The proposed simulator runs the adversary on an independently sampled dummy encryption, supplies the actual history obtained from its single query, and flags equality with its dummy challenge. This is efficient under CPA and needs no invalid-ciphertext generator or secret key. The reduction can compare the actual sampled message with the dummy sampled message in its single IND-NM challenge.

The auxiliary information omitted from the NM observer's input can be exported without losing it to the copy-to-bottom rule. For a bit `x` and positive message length `L`, append encryptions of `x^L` and `(not x)^L`. Correctness makes their plaintexts different, so the same challenge cannot equal both ciphertexts. Read `x` from the first valid decryption, or complement the second if the first is bottom. Applying this to the parameter, sampled message, auxiliary output and each equality flag reconstructs the complete simulation observer's input, including COPY markers. It remains valid for deterministic encryption and when one export ciphertext equals the challenge. At `L=0`, that export must not be used: actual and dummy messages are the unique empty message, and the simulator's challenge can be coupled directly with the real challenge. The written split handles this case.

These arguments justify the stated one-challenge implications. They do not establish a many-challenge bridge, nor a converse for CCA1/CCA2. The code and its declarations preserve those limits.

**CCA2 secrecy iff bottom-valued non-malleability.** In the forward direction, finalize the IND adversary by asking its permitted CCA2 oracle to decrypt each output block; its challenge refusal is exactly the NM copy-to-bottom rule. In the reverse direction, export the IND guess with the same complementary-encryption pair. The zero-message-length case is again bit-independent. This repairs the source's informal “decrypt the challenge” wording without making that forbidden oracle call.

### 6. Repetition, abort and 3COL

The repetition is a declared padded schedule: `k` real moves and `k` filler positions per phase. Every phase therefore starts with the original mover. For global move `2kj+t`, `0 ≤ t < k`, the recovered move index has quotient `j` and remainder `t` modulo `2k`; each party has exactly `jk` received messages from earlier phases. Dropping that prefix supplies precisely the original phase history. The verifier's complete-history verdict has not yet fired during these real moves. This gives the stated induction in `seqRep_exec_phase`; `k=0` is immediate from the empty execution. The final verifier message can carry the repeated verdict when it is the last mover, as the module explicitly explains.

The tapes have `Q(n)` disjoint blocks of each original party's coin length. Uniform tapes induce independent uniform phase blocks, including the unique empty block when a coin length is zero. Conditioned on any cheating-prover tape and completed prefix, the next honest-verifier block remains fresh. The one-phase soundness bound therefore multiplies to `s(n)^Q(n)`; no independence of the cheating prover's behavior is assumed. A positive phase count is required for the proof-system statements; the ZK-only statements correctly allow zero phases.

There is exactly one canonical `Protocol.ProverBounded` definition in the imported interaction owner. It bounds each honest message for every history/tape on every witnessed instance. Both efficient-prover interfaces expose this bound, and the 3COL corollary obtains it from the base interface. With the phase-output normalization in C-03, the simulated prefix has polynomially many bounded messages, giving the needed strict-PPT composition. The computational hybrid can complete its suffix with the simulator rather than an inefficient honest prover. Statistical composition uses the same post-processing and the triangle inequality.

The abort statement concludes statistical ZK, not exact perfect ZK. Independent strict-PPT attempts give

\[
\Pr[\text{all }n\text{ attempts abort}]\le (1/2)^n,
\qquad
\operatorname{distance}(\text{repeated real view},\text{simulator})\le Q(n)2^{-n}.
\]

The exact conditional output law of a successful attempt is preserved by selecting the first successful independent attempt. For `n=0`, the bound is one and remains valid. There is no inference from truncating an arbitrary expected-time simulator. `PerfectZK.seqRep` instead specializes statistical composition to zero error; its short proof has precisely that scope.

For 3COL the count is `Q(N)=2(N+1)^2`, not the source's graph-dependent count and not `colProtocolRep`. For sufficiently large positive `N`,

\[
\begin{aligned}
2^{-N}&\le\frac1{2N},\\
0\le 1-\frac1N+2^{-N}&\le 1-\frac1{2N}\le1,\\
Q(N)&\ge 2N^2,\\
\left(1-\frac1N+2^{-N}\right)^{Q(N)}
&\le\left(1-\frac1{2N}\right)^{2N^2}
\le e^{-N}\le2^{-N}.
\end{aligned}
\]

The code obtains the first estimate from the degree-one negligible tail of twice the dyadic function, and then applies eventual domination. At `N=0`, Lean's total real division gives the one-run expression `2`, and the repeated expression is `4`; the proof explicitly removes that finite prefix. It never claims the expression is a probability at every input length. The corollary consumes the explicit-error efficient-prover theorem and `col_zk`, then the generic repetition statements. Its references identify the 3COL/NP ingredients; it does not itself prove the full NP reduction or construct commitments from one-way permutations.

## Adversarial instances and disposition

| Instance | What it tests | Outcome |
|---|---|---|
| Distinct second challenge pair after a first challenge | Accidental multi-challenge access | The recorded answer is returned; no new encryption or message choice occurs. |
| Query budget zero; machine never asks a challenge | Degenerate game trivialization | Each IND/NM bit game has the same law; one-query ideal simulation still permits a final output. |
| Original PRF scheme, positive `n`, flip the challenge's last bit | Actual CCA2 break | The altered ciphertext is valid and distinct, and decrypts to the selected message with its last bit flipped; advantage one. |
| Encrypt-then-tag, change the nonce while reusing a tag | Whether authentication covers the entire old ciphertext | The tag input changes because it is `r ++ c1`, unlike the source's erroneous short notation. |
| Short-tag counterattack with repeated auxiliary nonce and selected plaintext zero | Whether the purported modified query can equal the challenge | It can, giving C-04's omitted failure branch. |
| Repeated distinct tag guesses at one fresh pair | Adaptive decryption feedback | Reveals C-02's conditioning issue, without invalidating the total bad-event bound. |
| `n=0`, malformed ciphertext `0000` | Failed parsing versus empty components | Reveals C-01. |
| Change a padded challenge's suffix bit | Re-padding attack | The altered non-canonical suffix is refused; a fixed-length accepted padding cannot re-encode the same raw challenge differently. |
| Deterministic encryption and export ciphertext equal to the challenge | Loss of exported copy flags | Complementary-pair export recovers the bit because both members cannot copy one challenge. |
| Message length zero; output-vector length zero | Empty-space/vacuity hazards | IND comparison is bit-independent; CPA simulation couples directly; no complementary-pair argument is used at zero length. Empty output vectors alone convey no challenge-dependent data. |
| Sampler parameter/history/auxiliary lengths zero | Boundary alignment | Fixed concatenation boundaries and empty functions remain defined; one history query is still optional. |
| Odd phase length, both first movers; zero phase length/count | Scheduling and final-verdict overlap | Padded `2k` phases preserve the mover; phase identity holds. Zero repetitions accept everything, correctly excluded from proof-system claims. |
| Negligibly rare malformed simulated phase with many empty messages | Worst-case efficiency of the composed simulator | Reveals C-03; canonical phase-shape normalization repairs it. |
| `N=0` in the 3COL repeated-error expression | Invalid global probability bound | Value is `4`, a harmless finite prefix of an eventually negligible numerical bound. |

## Declaration-by-declaration review

The following tables use file-local names; `PublicKeyScheme` and `BitPublicKeyScheme` retain their explicit root namespaces. “Matches” is a statement/docstring comparison, not an assertion that an admitted proof is complete. The definitions' body restatements are independent descriptions of the formulas, followed by the prose assessment.

### `Defs.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `Attack` · 72 | An enumeration of CPA, pre-challenge CCA, and adaptive CCA. Matches the three advertised attack classes. |
| `FixedLengthScheme` · 83 | A correct private-key scheme whose honest encryptions of parameter-length messages have one polynomially specified length. Matches, with decryption queries restricted by the later codec. |
| `inLens` · 95 | The three query lengths are n, ctLen(n), and 2n. Matches encryption, decryption and message-pair queries. |
| `outLens` · 111 | The answer lengths are ctLen(n), n+1, and ctLen(n). Matches the validity-bit decryption convention. |
| `indSpec` · 126 | The three bit-string oracles at those input/output lengths. Matches. |
| `decOpen` · 132 | Decryption is closed for CPA, open only before challenge for CCA1, and open for CCA2. Matches; challenge equality is checked elsewhere. |
| `encryptAt` · 147 | Read the encryption machine output at ctLen(n), padding/truncating as necessary. Matches; the honest-key length field ensures no truncation in the actual game. |
| `decAnswer` · 157 | Encode some plaintext with a leading true bit, and failure with all false bits. Matches, including empty plaintexts. |
| `splitHalf` · 169 | Project the first and second n-bit blocks of a 2n-bit word. Matches. |
| `indImpl` · 187 | Fresh encryption, phase-gated challenge-refusing decryption, and one stored challenge. Matches the advertised oracle behavior. |
| `indCodec` · 245 | Use the common bit codec with these three oracles and a one-bit result. Matches. |
| `indGame` · 267 | Sample key/adversary tapes, run the next-move machine from the unchallenged state, and return its final bit. Matches. |
| `INDSecure` · 285 | Every nonuniform adversary and polynomial query budget has negligible bit-game advantage, with the bound allowed to depend on them. Matches. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `inLens_zero` · 101 | Matches: the selected case has exactly the encryption query length n. |
| `inLens_one` · 104 | Matches: the selected case has exactly the decryption query length ctLen(n). |
| `inLens_two` · 107 | Matches: the selected case has exactly the challenge-pair length 2n. |
| `outLens_zero` · 117 | Matches: the selected case has exactly the encryption answer length ctLen(n). |
| `outLens_one` · 120 | Matches: the selected case has exactly the decryption answer length n+1. |
| `outLens_two` · 123 | Matches: the selected case has exactly the challenge answer length ctLen(n). |
| `indSpec_eq` · 129 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `decOpen_cpa` · 138 | Matches: decryption is closed in both phases. |
| `decOpen_cca1` · 141 | Matches: decryption is open exactly before a challenge. |
| `decOpen_cca2` · 144 | Matches: decryption is open in both phases before the separate equality check. |
| `encryptAt_eq` · 152 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `decAnswer_some` · 162 | Matches: some plaintext receives a true validity bit, whereas none receives the all-false failure code. |
| `decAnswer_none` · 166 | Matches: some plaintext receives a true validity bit, whereas none receives the all-false failure code. |
| `splitHalf_fst` · 173 | Matches: it exposes the indicated message half at the appropriate offset in the concatenated challenge pair. |
| `splitHalf_snd` · 177 | Matches: it exposes the indicated message half at the appropriate offset in the concatenated challenge pair. |
| `indImpl_enc` · 204 | Matches: encryption samples a fresh tape and preserves the challenge state. |
| `indImpl_dec` · 211 | Matches: decryption is governed by both availability and challenge equality, with the stored state preserved. |
| `indImpl_challenge_none` · 220 | Matches: an absent challenge is created from the selected message half and recorded. |
| `indImpl_dec_cpa` · 228 | Matches: every CPA decryption query returns the fixed bottom answer. |
| `indImpl_dec_cca2_challenge` · 234 | Matches: querying the stored CCA2 challenge returns bottom. |
| `indImpl_challenge_repeat` · 240 | Matches: a repeat returns the original stored ciphertext independently of its new message pair. |
| `indCodec_decodeMove` · 249 | Matches: it exposes exactly the common move decoder at this codec's input, answer and final-output lengths. |
| `indCodec_encodeEntry` · 254 | Matches: a log entry is the unary oracle index paired with its query/answer pair, in the stated order. |
| `indCodec_timeout` · 261 | Matches: budget exhaustion yields the all-false result at the full final-output length, with no extra oracle call. |
| `indGame_eq` · 275 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `INDSecure_iff` · 291 | Matches: it exposes precisely the predicate's quantifiers, negligible bound and game/error expression, without weakening a hypothesis. |

### `PRFScheme.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `prfFixedScheme` · 55 | Reuse Algorithm 99.1 with ciphertext-length polynomial 3n+2. Matches; its length field follows from the exact pairing and equal-length pad. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `prfFixedScheme_gen` · 82 | Matches: this projection is the preserved original key generator. |
| `prfFixedScheme_enc` · 87 | Matches: this projection is the advertised original encryptor (PRF wrapper) or padded encryptor (public-key wrapper). |
| `prfFixedScheme_dec` · 92 | Matches: this projection is the advertised original decryptor (PRF wrapper) or canonical-padding decryptor (public-key wrapper). |
| `prfFixedScheme_cpa` · 113 | Matches the CPA claim under PRF security; the random-pad argument needs the usual collision event covering other encryption calls. Its body is admitted. |
| `prfFixedScheme_cca1` · 124 | Matches the CCA1 claim under PRF security; the repaired positive-parameter decryption guard keeps oracle evaluation on-domain. Its body is admitted. |
| `prfFixedScheme_not_cca2` · 143 | Matches the quantified advantage-one adversary claim for every positive parameter, without a PRF assumption. The flip attack supports it; its body is admitted. |
| `not_prfFixedScheme_cca2` · 151 | Matches the negative security conclusion and correctly derives it from the advantage-one claim and the degree-zero negligible tail; it inherits that admission. |

### `CCA2Scheme.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `ccaGenFun` · 68 | Split the raw random tape after the parameter length and pair the two pieces. Matches the stated layout; the machine supplies exactly 3n coins. |
| `ccaMaskFun` · 81 | XOR the decoded message with the evaluator on the first key and encryption coins, using zipWith. Matches on the stated layout and equal-length inputs. |
| `ccaEncFun` · 94 | Pair the nonce with the masked message and the second-key evaluator on nonce concatenated with masked message. Matches the repaired whole-ciphertext tag. |
| `ccaDecOK` · 111 | Check nonce length, masked-message length, and tag equality through total projections. Matches its local formula, but malformed rejection has C-01. |
| `ccaDecFun` · 133 | On the guard, XOR the decoded masked message with the first-key pad; otherwise output one bit more than the parameter. Matches; C-01 qualifies the module-wide rejection assertion. |
| `ccaGen` · 240 | A uniform machine for the raw generator with 3n random bits. Matches. |
| `ccaEnc` · 244 | A uniform machine for the raw encryptor with n random bits. Matches. |
| `ccaDec` · 248 | A uniform machine for the raw decryptor with no random bits. Matches. |
| `ccaScheme` · 311 | Bundle those machines, perfect correctness, and ciphertext length 6n+4. Matches the declared repaired construction and doubled tag-key parameter. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `ccaGenFun_eq` · 74 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `ccaMaskFun_eq` · 87 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `ccaEncFun_eq` · 102 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `ccaDecOK_eq` · 121 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `ccaDecFun_eq` · 141 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `polyTimeComputable_ccaGenFun` · 152 | Matches: the stated polynomial-time property of `ccaGenFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `polyTimeComputable_ccaMaskFun` · 160 | Matches: the stated polynomial-time property of `ccaMaskFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `polyTimeComputable_ccaEncFun` · 171 | Matches: the stated polynomial-time property of `ccaEncFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `polyTimeComputable_ccaDecOK` · 187 | Matches: the stated polynomial-time property of `ccaDecOK` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `polyTimeComputable_ccaDecFun` · 218 | Matches: the stated polynomial-time property of `ccaDecFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `runAt_ccaGen` · 252 | Matches: machine execution splits the 3n-bit tape after its first n bits. |
| `runAt_ccaEnc` · 259 | Matches: execution returns the nonce, XOR mask and second-key tag of their concatenation. |
| `runAt_ccaDec` · 270 | Matches the guarded valid-triple execution formula, with explicit nonce/message lengths and tag equality; it does not assert parsing rejection for arbitrary strings. |
| `length_eval_of_length` · 289 | Matches: equal-length key/input lists yield an evaluator output of that common length by hFE and exact Fin padding. |
| `zipWith_xor_xor_self'` · 300 | This private lemma has no docstring: XORing twice with a sufficiently long pad recovers the original list, and the head/tail induction establishes that formula. |
| `ccaScheme_cca2` · 384 | Matches the repaired CCA2 theorem under PRF security; the security argument remains credible after the adaptive-guess clarification C-02. Its body is admitted. |

### `PublicKey.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `padCt` · 72 | Pair a raw ciphertext with enough true bits to reach L when its pair overhead fits. Matches the formula; the length lemma correctly requires that fit. |
| `isPadded` · 80 | Require exact re-encoding of the parsed pair and a second component containing no false bit. Matches canonical padding at the input word's own length. |
| `padEncFun` · 138 | Evaluate the underlying uniform encryption program on a reconstructed empty-advice layout and canonically pad its result. Matches. |
| `padDecFun` · 165 | Unpad accepted words before applying the old decryptor; otherwise prefix the supplied word with true. Matches; failure decoding requires the wrapper's message-length bound. |
| `padEnc` · 185 | A uniform padding-encryptor machine using the original coin polynomial. Matches. |
| `FixedLengthPKScheme` · 219 | Uniform key/encryption machines, an efficient deterministic decryptor, polynomial message/ciphertext lengths, and exact honest correctness/length fields. Matches; it need not itself be a padded instance. |
| `ofPadded` · 250 | Preserve key generation and message length, wrap encryption/decryption, and carry honest ciphertext and message-length bounds. Matches; both correctness and length fields use the original coins via transport. |
| `PublicKeyScheme.padded` · 320 | Specialize the padding constructor to the existing n-bit-message scheme. Matches. |
| `BitPublicKeyScheme.padded` · 361 | Specialize it to one-bit messages, identifying a Fin 1 word with its sole bit. Matches. |
| `inLens` · 479 | The two query lengths are ctLen(n) and twice msgLen(n). Matches decryption and challenge selection. |
| `outLens` · 490 | Return msgLen(n)+1 decryption bits or ctLen(n) challenge bits. Matches. |
| `indSpec` · 501 | The two bit-string oracles at these lengths. Matches. |
| `indImpl` · 523 | Use the deterministic decryptor with phase/equality refusal, or create/repeat the single encrypted message-pair challenge. Matches. |
| `indCodec` · 578 | Use the common bit codec with two oracles and one final bit. Matches. |
| `indGame` · 602 | Generate keys, expose only pk to the adversary, run the oracles from no challenge, and read the verdict. Matches. |
| `INDSecure` · 623 | Negligible challenge-bit advantage for every nonuniform machine and polynomial query budget. Matches the indexed fixed-length notion. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `padCt_eq` · 76 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `isPadded_eq` · 85 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `length_padCt` · 90 | Matches: the padding has exactly L bits under the explicit pair-overhead bound. |
| `pairFstD_padCt` · 96 | Matches: unpadding recovers the raw ciphertext, even when an undersized L makes the output longer than L. |
| `isPadded_padCt` · 100 | Matches: every constructed padding passes the shape/all-true test. |
| `padCt_of_isPadded` · 104 | Matches: every accepted word is the unique padding of its recovered ciphertext at that word's own length. |
| `polyTimeComputable_isPadded` · 124 | Matches: the stated polynomial-time property of `isPadded` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `padEncFun_eq` · 144 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `polyTimeComputable_padEncFun` · 149 | Matches: the stated polynomial-time property of `padEncFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `padDecFun_eq` · 171 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `polyTimeComputable_padDecFun` · 177 | Matches: the stated polynomial-time property of `padDecFun` follows from the listed projection/pairing/list operations and the explicit evaluator/decryptor hypothesis where present. |
| `padEnc_coins` · 189 | Matches: wrapping encryption preserves its coin polynomial. |
| `runAt_padEnc` · 194 | Matches: for a uniform encryptor the wrapper runs the original machine with transported coins, then pads its output. |
| `padDecFun_padCt` · 204 | Matches: decrypting an explicitly padded ciphertext delegates exactly to the old decryptor. |
| `padDecFun_of_not_isPadded` · 209 | Matches: failed canonical-padding checks return a word one bit longer than the query, which is the needed failure code under the constructor bound. |
| `ofPadded_msgLen` · 291 | Matches: this projection is the specified message-length polynomial. |
| `ofPadded_ctLen` · 296 | Matches: this projection is the specified ciphertext-length polynomial. |
| `ofPadded_gen` · 301 | Matches: this projection is the preserved original key generator. |
| `ofPadded_enc` · 306 | Matches: this projection is the advertised original encryptor (PRF wrapper) or padded encryptor (public-key wrapper). |
| `ofPadded_dec` · 311 | Matches: this projection is the advertised original decryptor (PRF wrapper) or canonical-padding decryptor (public-key wrapper). |
| `PublicKeyScheme.padded_msgLen` · 338 | Matches: this projection is the specified message-length polynomial. |
| `PublicKeyScheme.padded_ctLen` · 342 | Matches: this projection is the specified ciphertext-length polynomial. |
| `PublicKeyScheme.padded_gen` · 346 | Matches: this projection is the preserved original key generator. |
| `PublicKeyScheme.padded_enc` · 350 | Matches: this projection is the advertised original encryptor (PRF wrapper) or padded encryptor (public-key wrapper). |
| `PublicKeyScheme.padded_dec` · 354 | Matches: this projection is the advertised original decryptor (PRF wrapper) or canonical-padding decryptor (public-key wrapper). |
| `BitPublicKeyScheme.padded_msgLen` · 387 | Matches: this projection is the specified message-length polynomial. |
| `BitPublicKeyScheme.padded_ctLen` · 391 | Matches: this projection is the specified ciphertext-length polynomial. |
| `BitPublicKeyScheme.padded_gen` · 395 | Matches: this projection is the preserved original key generator. |
| `BitPublicKeyScheme.padded_enc` · 399 | Matches: this projection is the advertised original encryptor (PRF wrapper) or padded encryptor (public-key wrapper). |
| `BitPublicKeyScheme.padded_dec` · 403 | Matches: this projection is the advertised original decryptor (PRF wrapper) or canonical-padding decryptor (public-key wrapper). |
| `PublicKeyScheme.exists_padBound` · 417 | Matches the existence of both honest ciphertext and message bounds; generator/encryptor output-length polynomials yield the stated construction. |
| `BitPublicKeyScheme.exists_padBound` · 449 | Matches the analogous single-bit bound, including the constant pair overhead and the lower bound one. |
| `inLens_zero` · 484 | Matches: the selected case has exactly the decryption query length ctLen(n). |
| `inLens_one` · 487 | Matches: the selected case has exactly the challenge-pair length twice msgLen(n). |
| `outLens_zero` · 495 | Matches: the selected case has exactly the decryption answer length msgLen(n)+1. |
| `outLens_one` · 498 | Matches: the selected case has exactly the challenge answer length ctLen(n). |
| `indSpec_eq` · 505 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `indSpec_dom` · 508 | Matches: each oracle's domain is a bit vector of its published query length. |
| `indSpec_rng` · 513 | Matches: each oracle's range is a bit vector of its published answer length. |
| `indImpl_dec` · 541 | Matches: the deterministic decryption branch enforces the availability/equality guards and preserves the state. |
| `indImpl_challenge_none` · 551 | Matches: the first challenge encrypts the chosen message and stores its fixed-length ciphertext. |
| `indImpl_challenge_repeat` · 561 | Matches: subsequent challenge queries repeat that stored ciphertext. |
| `indImpl_dec_cpa` · 566 | Matches: CPA decryption is always refused. |
| `indImpl_dec_cca2_challenge` · 572 | Matches: the CCA2 oracle refuses the recorded ciphertext. |
| `indCodec_decodeMove` · 583 | Matches: it exposes exactly the common move decoder at this codec's input, answer and final-output lengths. |
| `indCodec_encodeEntry` · 589 | Matches: a log entry is the unary oracle index paired with its query/answer pair, in the stated order. |
| `indCodec_timeout` · 596 | Matches: budget exhaustion yields the all-false result at the full final-output length, with no extra oracle call. |
| `indGame_eq` · 611 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `INDSecure_iff` · 629 | Matches: it exposes precisely the predicate's quantifiers, negligible bound and game/error expression, without weakening a hypothesis. |
| `BitPublicKeyScheme.SingleBitSecure.padded_cpa` · 653 | Matches adaptive single-bit CPA security for every admissible padding length; flipping the output on reversed challenge pairs aligns the two advantages. Its body is admitted. |
| `TrapdoorCollection.tdpBitScheme_padded_cpa` · 664 | Matches Claim 172.a with explicit hard-core/one-way hypotheses and admissible padding; the short application preserves all premises and inherits the padded-CPA admission. |

### `NonMalleable.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `nmCodec` · 77 | Keep the public-key IND oracles but replace the final bit with a fixed number of ciphertext blocks. Matches. |
| `nthCt` · 101 | Read a ciphertext block through the product-to-flat finite index. Matches. |
| `nmDecrypt` · 111 | Return bottom for equality with the recorded challenge; otherwise decode the deterministic decryption with a validity bit. Matches. |
| `nmOutput` · 126 | Flatten the vector of those decryption codes in block order. Matches. |
| `nmGame` · 140 | Run the public-key adversary, decrypt its final blocks with the copy rule, and give only that plaintext vector to a separate distinguisher. Matches. |
| `NMSecure` · 169 | Every adversary, polynomial query/output budget and distinguisher has negligible difference between the two NM bit games. Matches. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `nmCodec_decodeMove` · 82 | Matches: it exposes exactly the common move decoder at this codec's input, answer and final-output lengths. |
| `nmCodec_encodeEntry` · 88 | Matches: a log entry is the unary oracle index paired with its query/answer pair, in the stated order. |
| `nmCodec_timeout` · 96 | Matches: budget exhaustion yields the all-false result at the full final-output length, with no extra oracle call. |
| `nthCt_eq` · 106 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `nmDecrypt_eq` · 118 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `nmOutput_eq` · 131 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `nmGame_eq` · 153 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `NMSecure_iff` · 177 | Matches: it exposes precisely the predicate's quantifiers, negligible bound and game/error expression, without weakening a hypothesis. |
| `nmDecrypt_challenge` · 184 | Matches: an exact challenge copy receives the same bottom code as an invalid decryption. |
| `indSecure_cca2_iff_nmSecure_cca2` · 207 | Matches the CCA2 equivalence for these one-challenge games; final decryption queries and complementary-pair export justify both sketches. Its body is admitted. |

### `SimNonMalleable.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `MsgSampler` · 94 | A nonuniform sampling machine with a fixed parameter length and an efficient deterministic history function read at a fixed length. Matches the declared parameterized-sampler encoding. |
| `draw` · 111 | Run the sampler on the parameter and its fixed tape, then pad/truncate to the requested message length. Matches. |
| `histAt` · 119 | Apply the history function to the sampled message and pad/truncate to histLen(n). Matches. |
| `simSpec` · 127 | One parameter-input/history-output oracle. Matches. |
| `snmInLens` · 144 | Real decryption takes a ciphertext; real challenge takes a sampler parameter. Matches. |
| `snmOutLens` · 158 | Return a validity/plaintext code or a ciphertext/history concatenation. Matches. |
| `snmSpec` · 171 | The real experiment's two bit-string oracles. Matches. |
| `SnmState` · 181 | Either no challenge or the first ciphertext paired with its sampler parameter. Matches. |
| `snmImpl` · 196 | Phase-gated decryption plus a challenge/history response using one hidden sampler tape; repeats reuse both the first parameter and the same message. Matches. |
| `snmCodec` · 244 | Real final outputs contain ciphertext blocks followed by a fixed-length auxiliary string. Matches. |
| `snmCt` · 268 | Extract ciphertext block i while excluding the final auxiliary suffix. Matches. |
| `snmSigma` · 277 | Extract the fixed auxiliary suffix after the ciphertext/entry prefix. Matches. |
| `snmEntry` · 287 | Encode COPY separately; otherwise encode successful decryption or bottom with a second flag. Matches and preserves COPY versus invalidity. |
| `snmView` · 304 | Concatenate parameter, sampled message, decoded entries and auxiliary suffix. Matches; known lengths make the fields recoverable. |
| `snmReal` · 320 | Sample all tapes, run the real adversary on pk, use the recorded or default parameter, and test the complete semantic output. Matches. |
| `simImpl` · 362 | Remember the first queried parameter and return the history of its hidden sampled message. Matches; the enclosing ideal game limits calls to one. |
| `simCodec` · 375 | Ideal output blocks each contain an explicit COPY flag and a ciphertext, followed by the auxiliary suffix. Matches. |
| `simEntry` · 405 | Split one ideal block into its COPY flag and ciphertext payload. Matches. |
| `snmIdeal` · 417 | Run the simulator on pk with one history query and no decryption access, then decrypt unflagged entries for the observer. Matches; no query uses the default zero parameter. |
| `SimNMSecure` · 460 | For every sampler/adversary and polynomial budgets, one simulator must fool every nonuniform distinguisher with negligible error. Matches the stated quantifier order. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `draw_eq` · 115 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `histAt_eq` · 123 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `simSpec_eq` · 132 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmInLens_zero` · 149 | Matches: the selected case has exactly the real decryption query length ctLen(n). |
| `snmInLens_one` · 153 | Matches: the selected case has exactly the sampler-parameter query length paramLen(n). |
| `snmOutLens_zero` · 163 | Matches: the selected case has exactly the real decryption answer length msgLen(n)+1. |
| `snmOutLens_one` · 167 | Matches: the selected case has exactly the challenge/history answer length ctLen(n)+histLen(n). |
| `snmSpec_eq` · 176 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `SnmState_eq` · 186 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmImpl_dec` · 213 | Matches: real decryption follows the attack table and refuses the first recorded challenge. |
| `snmImpl_challenge` · 224 | Matches both first and repeated challenge branches, preserving the original parameter and sampled history on repeats. |
| `snmImpl_dec_cpa` · 237 | Matches: the real CPA experiment never supplies decryption information. |
| `snmCodec_decodeMove` · 249 | Matches: it exposes exactly the common move decoder at this codec's input, answer and final-output lengths. |
| `snmCodec_encodeEntry` · 255 | Matches: a log entry is the unary oracle index paired with its query/answer pair, in the stated order. |
| `snmCodec_timeout` · 263 | Matches: budget exhaustion yields the all-false result at the full final-output length, with no extra oracle call. |
| `snmCt_eq` · 273 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmSigma_eq` · 281 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmEntry_eq` · 295 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmView_eq` · 310 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `snmReal_eq` · 340 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `simImpl_eq` · 368 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `simCodec_decodeMove` · 382 | Matches: it exposes exactly the common move decoder at this codec's input, answer and final-output lengths. |
| `simCodec_encodeEntry` · 390 | Matches: a log entry is the unary oracle index paired with its query/answer pair, in the stated order. |
| `simCodec_timeout` · 399 | Matches: budget exhaustion yields the all-false result at the full final-output length, with no extra oracle call. |
| `snmIdeal_eq` · 436 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `SimNMSecure_iff` · 469 | Matches: it exposes precisely the predicate's quantifiers, negligible bound and game/error expression, without weakening a hypothesis. |
| `nmSecure_of_simNMSecure` · 495 | Matches the every-attack SIM-to-NM implication; the two tests control the differing-message event as well as the choice-bit correlation. Its body is admitted. |
| `simNMSecure_of_nmSecure_cpa` · 520 | Matches the CPA-only NM-to-SIM implication; complementary pairs export all needed bits at positive message length, and direct coupling handles zero length. Its body is admitted. |
| `simNMSecure_cpa_iff_nmSecure_cpa` · 526 | Matches exactly the CPA equivalence assembled from the two previous directions; it inherits their admissions. |

### `SequentialZK.lean`

| Definition/type · line | Independent restatement and prose comparison |
|---|---|
| `proverMoveIndex` · 107 | Recover the prover's next global move from received-message count, using saturated subtraction when verifier-first. Matches at actual prover positions. |
| `verifierMoveIndex` · 114 | Recover the verifier's next global move from received-message count and the first mover. Matches at actual verifier positions. |
| `proverMoves` · 121 | Count prover positions below a supplied move bound. Matches. |
| `seqProver` · 199 | At real phase positions, invoke the original prover on that phase's tape block and received suffix; otherwise send empty. Matches. |
| `seqVerdict` · 214 | Accept exactly if the original verifier accepts each phase's real prover-message segment on its own tape block. Matches. |
| `seqVerifier` · 235 | On complete received history compute the repeated verdict; otherwise invoke the original verifier at real positions or send an empty filler. Matches, including the final-message convention. |
| `seqRep` · 253 | Bundle these parties, preserve the first mover, and use 2kQ total moves. Matches the explicitly padded schedule. |

| Theorem · line | Statement/docstring assessment |
|---|---|
| `proverMoveIndex_eq` · 110 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `verifierMoveIndex_eq` · 117 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `proverMoves_eq` · 124 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `moverIsV_two_mul_add` · 128 | Matches the period-two mover identity for either first mover. |
| `countP_moverIsV` · 133 | Matches the verifier-move count, with the ceiling/floor selected by the first mover. |
| `countP_not_moverIsV` · 143 | Matches the complementary prover-move count. |
| `exec_fst_length` · 153 | Matches: the prover has received exactly one message per verifier move, independently of message contents. |
| `exec_snd_length` · 163 | Matches: the verifier has received exactly one message per prover move. |
| `proverMoveIndex_exec` · 174 | Matches index recovery at an actual prover position; the mover premise correctly excludes spurious count inputs. |
| `verifierMoveIndex_exec` · 182 | Matches index recovery at an actual verifier position with the same necessary mover premise. |
| `seqVerdict_eq` · 222 | Matches: it publishes the exact defining formula, with the same arguments, field ordering and length indices as the corresponding definition reviewed above. |
| `seqRep_rounds_eval` · 261 | Matches the exact 2kQ move count. |
| `seqRep_exec_phase` · 280 | Matches the two honest received-history identities at the end of a phase's real moves; the body's induction handles empty k separately and keeps the verdict guard closed in real moves. |
| `ZK.seqRep` · 392 | Matches computational ZK preservation with an explicit honest-message bound, including zero repetitions; C-03 repairs the simulator-size justification. Its body is admitted. |
| `StatZK.seqRep` · 404 | Matches the explicit Q times delta statistical bound with the same message-bound premise; C-03 applies to the inherited simulator construction. Its body is admitted. |
| `PerfectZK.seqRep` · 411 | Matches exact perfect preservation by specializing statistical composition to zero; the short proof is correct and inherits that theorem's admission. |
| `PerfectZKAbort.seqRep` · 431 | Matches the advertised statistical, rather than perfect, conclusion at error Q(n) times 2^(-n); the short proof uses the established abort bridge and inherits statistical composition's admission. |
| `InteractiveProof.seqRep` · 450 | Matches preservation of the proof-system predicate when every length has at least one phase; zero phases would falsify soundness on nonmembers. Its body is admitted. |
| `InteractiveProofErr.seqRep` · 471 | Matches the s(n)^Q(n) soundness bound and perfect completeness under a positive repetition count; conditioning on the prefix justifies the product. Its body is admitted. |
| `EfficientProverProofErr.seqRep` · 483 | Matches preservation of prover efficiency, bounded messages and witness completeness together with the repeated soundness bound. Its body is admitted. |

### `ThreeColoring.lean`

| Theorem · line | Statement/docstring assessment |
|---|---|
| `negligible_colSeqSound` · 55 | Matches the explicit repeated-error negligibility claim; its proved eventual dyadic domination properly omits the finite zero-length prefix. |
| `colSeq_efficientProverProof_zk` · 120 | Matches the efficient-prover and computational-ZK conjunction for the explicit padded schedule under Commitment; its short application is correct and depends on generic repetition admissions. |

### Generated readers and facade

The `simps` field readers agree with their constructor bodies: `prfFixedScheme` exposes `toPrivateKeyScheme` and `ctLen`; `ccaScheme` exposes `gen`, `enc`, `dec`, `ctLen`; `seqProver` and `seqVerifier` each expose `coins` and `next`; `seqRep` exposes `P`, `V`, `rounds`, `verifierFirst`; `simEntry` exposes `fst` and `snd`. These projection statements do not add security hypotheses or substitute for a security proof. The facade imports all eight modules, and the root source imports the facade. Root-export source coverage was inspected; root-export elaboration was not independently run or inferred from the records.

## Attribution disposition

The substantive private/public security statements identify the relevant PS10 claims, and the source errors in Algorithm 169.3 and the relation-based theorem are explicitly described rather than silently retained. The non-malleability directions are labeled as maintainer arguments with the appropriate numbered paper references and CPA/CCA scope. The sequential module distinguishes the Goldreich strict-abort convention from PS10's expected-time prose. Its perfect and aborting corollaries have different conclusions for a stated reason. The 3COL declaration lists Theorem 124.1, Propositions 127.6/128.8 and Theorem 175.1, while identifying its altered count/schedule and admitted dependencies. Technical readers are implementation glue and need no invented textbook theorem numbers. I found no additional attribution defect material to this gate, subject to the exact source-version limits above.

## Glossary

All mathematical symbols used here follow the audited sources/code. `n` is the security parameter; `N` is the encoded 3COL input length; `L` is a padding target in the padding calculation and a message length in the export argument, as specified locally. `k` is the original protocol's move count in the repetition calculation; `j` and `t` are phase and within-phase indices; `Q` is the phase count; `B` is the honest per-message length bound; `s` and `delta` (δ) are one-phase soundness and statistical-error bounds. `F` is the function family and `E` its string evaluator; `r`, `c1`, and `t` in the ciphertext calculation are nonce, masked message, and tag (the tag use of `t` is local to that calculation); `w` is a raw ciphertext word. `m` is a sampled/plaintext message; `m0`/`m1` are challenge messages; `x` is a bit in the complementary-export argument and an evaluator input in the finite test. `q` is the oracle-query budget; `A` is an adversary, `D` a distinguisher, `M` a sampler, `S` a simulator, and `P`/`V` the original protocol parties. The choice bit is denoted beta (β) in the code/source discussion; epsilon (ε) is a negligible bound. `z` is an auxiliary input or the fully encoded machine layout where specified. `pk`/`sk` are public/secret keys; `c` is a raw ciphertext and `c_honest` its honestly generated instance in the zero-parameter calculation. `COPY` is the distinguished copy marker, and bottom/`⊥` is failed or copy-suppressed decryption according to the experiment. `[]` is the empty list, and a displayed bit word such as `0101` is a list of Boolean bits.
