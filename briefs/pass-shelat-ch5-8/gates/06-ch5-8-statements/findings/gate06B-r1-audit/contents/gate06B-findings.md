# Gate 06B findings — round 1

**Verdict: PASS for the issued statement gate. Zero blockers, zero majors, five minors.**

This is approval of the scoped definitions, statements and correctness/phase proofs, subject to the specific minor corrections below. It is not certification that the admitted cryptographic security or efficiency proofs have been completed. The narrower source-version comparisons that were unavailable are identified explicitly.

Audit date: 7 November 2026 (America/Los_Angeles). Auditor: external Codex.

## Frozen input and independent verification

| Identity | Verified value |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange checkout | `5928e06c02b382b63b9b384db89d0458b520f351` exactly |
| Lean source | `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` |
| Records | `c81baa7712ab1b43357276ef5df138d02616c9d0` |
| Checked comparison ancestor | `eee107e92a7db11f1f8c98a5c2867304f57ddc54` |
| Source bundle SHA-256 | `66f3ac9e11a1100a276f3336f54ee4a6f5b3a109e5c647523575b95e828ef9ff` |
| Source manifest SHA-256 | `e33f8aa437668a506a31a5f7c1c2e3d2632ff999023be5d2847e324cbcd83990` |
| Records bundle SHA-256 | `1e5d62aebbb9d5197d438af67b8f4543dd264c7bc4218266782f66127beca01f` |
| Common archive SHA-256 | `960ab0c708c9efdd9a5ef01175889afa0b97be0984e35ace25f4001265ee0749` |
| Final evidence index SHA-256 | `0e011edc90d469d1b3dd1156a74f6f7856f756e15e085343486a232ea24aa73b` |
| Supplied PS10 PDF SHA-256 | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` |

I read both gate READMEs and the issued `06B-pack.md`, including its scope, retained findings, questions and evidence limitations. Both folders' complete `SHA256SUMS` pass: nine entries in 06B and five in the common folder. I independently compared all 129 extracted source sections with their raw-byte manifest **and the exact Lean Git objects**, all 20 records sections with their revision-qualified Git objects, and all 3,419 archive members with their size/hash manifest and records Git objects. The ZIP CRC check also passes. The checked ancestor and records commit have identical `TCSlib/` and `TCSlib.lean` bytes.

I inspected all thirteen primary modules and their facade, reading comment-stripped declaration bodies before comparing their prose. The declaration reviews below cover 102 explicit definitions/types/abbreviations and 234 explicit theorems, including 12 private glue theorems. The sixteen requested generated field equations are listed separately. Import-closure owners were read as needed to determine semantics, particularly `Interaction`, `Collections`, the encodings, the DAG model and probability/security interfaces; this is not a new statement audit of every prerequisite.

The independent checks did **not** run Lean elaboration: this executor has no Lean/Lake toolchain installed. I read the included correctness/phase proof terms and checked their mathematical arguments; the finite checks below are Python models, not kernel checks. The native-build, seal, control and axiom reports remain maintainer evidence. Byte verification establishes their identity, not that I independently reran those checks. In particular I do not turn the retained 17 seal failures into passes, reinterpret the 46 admitted-dependent identities as proof completion, or claim elaboration of `TCSlib.lean`.

The checkout remained clean. No campaign branch was changed and no push was attempted.

## Findings

All locations below refer to the frozen Lean head and `TCSlib/Cryptography/SecureComputation/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| B-01 | minor | `ObliviousTransfer.lean:29–30` · module explanation | The paragraph's grammar says the generator, sampler, evaluator and inverter all run on an all-true tape. | `otSender` uses its actual generator tape; `otKnown` and `otRaw` use Bob's two fresh tape blocks. Only `otMask` fixes the inverter tape; `eval` is deterministic. Reading the paragraph literally would describe a different, insecure protocol. The definitions and correctness proof use the right randomness. | State separately that Gen and sampling use fresh coins, eval is deterministic, and the inverter alone uses a fixed all-true tape, justified by all-tape inversion correctness. |
| B-02 | minor | `SpecialEncryption.lean:34`, `spDecStr:77` · malformed-ciphertext rejection | The module broadly says decryption refuses malformed ciphertexts. | At `n=ℓ=0`, `k=c=[]`, and `E=fun _ => []`, both default pair projections are empty. Every length test and prefix test succeeds, so `spDecStr E 0 0 [] [] = some []`, although `pairDecode [] = none`. This is a finite-parameter prose/guard edge case; it does not invalidate encryption correctness or asymptotic secrecy. | Qualify the rejection claim as the stated component-length checks, explicitly noting the zero-length exception, or test successful pair parsing before using its projections. A guard repair would require the prescribed affected checks. |
| B-03 | minor | `ObliviousTransfer.lean:218` · `EnhancedHardCore` attribution | Appendix C.1 alone is cited for the formal Boolean prediction predicate. | In the accessed official Appendix draft, Definition C.1.1 is an **inversion** condition. The predicate motivation and its use with receiver sampler coins are in Chapter 7, §7.3.2, draft pp. 639–641. The issued pack correctly distinguishes these, but the declaration/module reference list does not give that second location. The formal prediction experiment itself has the right semantics. | Cite Appendix C.1 for enhanced inversion and §7.3.2 for the predicate/OT argument; label the Boolean predicate as the explicit prediction hypothesis used here, rather than a transcription of C.1.1. |
| B-04 | minor | `Garbling.lean:23`, `Good:336`, `uprob_not_good_le:415`; `GarblingSecurity.lean:77` | The source's unique-opening description is identified with the formalized Claim 159.a. | `Good` asserts the value of the **first** successful opening for every assignment. With coincident labels, four rows can all open to the required label and `Good` still holds. Neither probability theorem's conclusion states uniqueness. Their union-bound sketches actually bound the stronger event of any cross-opening, so the current correctness statements are sound; they simply formalize less than the quoted source sentence. | Record this weaker formal target explicitly in the deviation/claim description, or additionally state the unique-opening conclusion using the same cross-opening bound. Do not silently strengthen the meaning of `Good`. |
| B-05 | minor | `ObliviousTransfer.lean:615–616` · `otProtocol_simulators` sketch, finite input cases | The sketch counts four predictor cases indexed only by the choice and unselected sender bit. | Constructing Bob's selected mask also uses the selected sender bit: it is `h(x) xor a_b`. Bob's tape makes `h(x)` computable, so a distinguisher may branch on this bit. Thus fixing only `(b,a_(1-b))` does not specify the complete view used by the stated reduction. This is finite bookkeeping, not a missing hardness hypothesis or a counterexample to the theorem. | Take the maximum over the eight triples `(b,a0,a1)`, or explicitly let the selected bit be chosen as worst-case nonuniform advice within each of the four predictor families. |

No blocker or major was found. B-01, B-03, B-04 and B-05 admit prose/sketch repairs without changing a theorem statement. B-02 also admits a prose-only repair; a stricter implementation is optional. None of these minors authorizes a source edit during this external audit.

## Primary-source access and exact comparison limits

| Source/version | What I accessed and compared | Exact limit |
|---|---|---|
| Supplied PS10, 3rd edition, January 2010 | The checksum-verified 1,771,458-byte PDF; book pp. 154–164, PDF pp. 166–176. I read the definition, encryption, garbling, OT and Yao text, and visually checked Algorithm 157.2. | None for the requested §6.2 comparisons. The source itself leaves the receiver OT simulation as an exercise and gives a sketch of Yao security. |
| [Goldreich official Chapter 7 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.pdf) | Read firsthand in the browser: cover version 3.2, 2 July 2003, 204 PDF pages; PDF pp. 47–50 and 52–55, printed pp. 633–636 and 638–641. Definitions 7.3.1–7.3.2, Theorem 7.3.3 and its sketch, Construction 7.3.5 and Proposition 7.3.6 are present. | Direct PDF/PS retrieval returned HTTP 503; browser rendering succeeded. A browser chapter-download attempt timed out, so I **did not independently recompute this PDF's supplied `a3ca…da84` hash**. The content comparison is firsthand, not based on the maintainer's access attestation. Published 2004 edition text and draft-to-published page/text identity were unavailable and are not certified. |
| [Goldreich official Appendix draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/errI.pdf) | Read PDF pp. 2–3, printed pp. 759–760, including C.1.1. Browser download succeeded: 425,995 bytes, SHA-256 `986c2c59a4b9144888ad1e27582ace383e2ee2d52491259975c3f41f76cb79a4`, matching the pack. Cover: revised third posted version, 15 June 2003. | No published-edition text/page equivalence claim. C.1.1 is not itself the Boolean hard-core definition. |
| [Official draft index](https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html) | Checked its provenance/version labels and personal-copy notice. | Its coarse June-2003 chapter label does not replace the accessed Chapter 7 cover's 2-July-2003 version date. |
| [Lindell–Pinkas author publication page](https://yehudalindell.com/publications/a-proof-of-security-of-yaos-protocol-for-two-party-computation/) and [ECCC TR04-063 revision 1](https://eccc.weizmann.ac.il/report/2004/063/revision/1/download) | The author page identifies the 2009 journal article. I read the official ECCC revision accepted 11 January 2011, especially its fake-garbling simulator on PDF pp. 18–19: a single active label encrypted in every row and output decoding pairs set from the ideal output. This supports the architectural attribution used by the sketch. | The author's linked `https://eprint.iacr.org/2004/175.pdf` returned HTTP 403. I did not compare the 2011 ECCC revision byte-for-byte or text-for-text with the 2009 journal version. |
| [BMR90 author copy](https://web.cs.ucdavis.edu/~rogaway/papers/bmr90) | Read the 11-page author-hosted extended abstract, especially protocol steps on printed pp. 508–509: random Boolean wire masks and masked row selection support the stated point-and-permute inspiration. Local SHA-256: `a3eb145d91a0a06b17f89f5b896ea50cd99df9e5598d248052c62aded43fb900`. | This supports attribution of an idea, not identity of the present independent per-gate shifts with BMR's full multiparty construction. No such identity is claimed. |

As additional primary-source corroboration, the [Goldreich–Rothblum author version dated 28 March 2018](https://www.wisdom.weizmann.ac.il/~oded/R1/tdp.pdf), Definition 2.2 and Claim 3.1, explicitly gives the enhanced predicate experiment and its semi-honest OT use. This is supplementary; it is not silently substituted for the requested Appendix/Chapter 7 comparison.

PSV06/PSV07, Goldreich Chapter 4 and their published-version equivalences belong to sibling prongs, not the issued 06B mathematical scope. I make no new comparison claim for them. No third-party PDF, extracted book text or rendered book page is included in this delivery.

## Answers to the five issued questions

**1. Definition 155.1.** The two real samples pair a party's full view with the *other* party's output. The corresponding simulator gets only its own original input and own ideal output. This correctly handles OT's private outputs. The polynomial input/output lengths and a bound uniform over inputs of each length are declared changes from PS10's equal-length display. The fixed simulators precede the distinguisher; no simulator depends on the opponent's private input.

`Functionality.PolyTime` gives the intended honest-execution PPT requirement in this model: the strategies are uniform, the round count and tapes are polynomial, and the encoded history has polynomial length because every honest message is bounded. A final next-message output is consequently polynomially computable too. The output clauses force correctness **except with negligible probability**, not perfect correctness at every parameter and tape. For a deterministic functionality, a nonuniform distinguisher can compare the appended output with its correct value supplied as polynomial-length advice. Choosing a worst failing input pair at each length yields one such distinguisher and a uniform negligible correctness-error bound. Constant wrong-output protocols therefore cannot satisfy the definition on infinitely many offending lengths.

**2. OT.** The actual five moves are index, element pair, mask pair, empty Bob filler, empty Alice filler. Alice's final next-message output is empty; Bob computes from his full three-message received history. This avoids exposing the mask pair as Alice's private output under D8. `SamplerCanonical` is derived, not assumed. More strongly, `encD_decD` makes every accepted inverter output canonical, so `Collection.apply_of_decD` legitimately extends the canonical-only `henc` equation exactly where correctness needs it.

The enhanced experiment supplies the receiver's raw-sampler coins, not just the sampled element. It is the right strengthening for the current protocol. It neither literally transcribes Appendix C.1.1 nor proves that arbitrary one-way trapdoor collections possess an appropriate predicate. The explicit `hH` and `henc` are present in the simulator/security interfaces and in real Yao; `EnhancedHardCore` is propagated as well. Ordinary `HardCore` has not been substituted for it. B-01, B-03 and B-05 are the remaining prose/attribution/sketch details.

**3. Special encryption and garbling.** For a correctly sized pad, `spEncStr` is Algorithm 157.2 split at the zero-padding boundary. `nestedSpecial` applies that algorithm twice with the correct inner ciphertext length, using `G1` for n-bit labels and `G2` for a `4n+2`-bit inner ciphertext. The zero- and one-input gate cases are handled explicitly. The wrong-key statements use independently sampled keys; they do not assume distinct sampled key values.

`Good` is the right invariant for this first-success evaluator: it quantifies over every gate and every argument assignment, not merely the selected global input. It is weaker than uniqueness, as B-04 records. `garbling_good_whp` samples a **uniform full `GarbleSeed`**, including row permutations; its error is explicitly gate-count times a negligible function. It does not promise a negligible error for circuits of arbitrary superpolynomial size. `yaoSeed_good_whp` instead samples Alice's actual fixed-length bit tape and separately includes output-label collisions. It does not identify XOR-shift sampling with uniform sampling from all 24 row permutations.

**4. Hybrid model and composition.** Nonadaptive ideal calls before the message phase are a genuine restricted case of the official oracle-aided model. Each call input is determined by that party's original input and main coins, so moving these calls before the garbling message is valid for the constructed Yao protocol. The augmented private inputs retain each party's answers; its view plus its original input/tape determines its call inputs. `HybridProtocol.PolyTime` deliberately bounds main for **all right-length answers**, which is stronger than the ideal-only clause and is needed for the composed protocol's time bound on rare subprotocol errors. This cost is explained in the declaration.

The layout faithfully runs each subprotocol in move/filler pairs, then inserts an Alice lead filler only for Bob-first main. Both parties use disjoint subprotocol tape blocks. The phase identities state exact history equalities even for zero calls or zero subprotocol moves; the **output** identities explicitly require a positive main move count. The documented zero-main swap example is valid. `hM` is necessary for a general theorem about this particular composer; it is not claimed necessary for every instance or for sequential composition in a different output model. Its stated all-n form is sufficient for the output alignment. Together with the uniform simulation definition and the all-answer efficiency condition, no further semantic premise was found missing from `hbcSecure_compose`.

The sketch also correctly treats a simulator's result as a **view**, then computes/reconstructs what is needed from it; it does not mistake the simulator result for the party's functionality output. The theorem and strategy-efficiency proofs remain admitted.

**5. Yao.** The hybrid uses n bit OTs for each Bob input wire, repeating the same choice bit for all n label bits. Flattening is wire-major and agrees with Bob's answer reader. The two-message main sends tables, Alice's selected input labels and output decoding pairs, then returns Bob's evaluated result. The real protocol is exactly its published composition with OT, with `10 * inB(n) * n + 2` moves and Alice first.

The XOR-shift change is explicit and mathematically sufficient for the stated simulation plan: after relabeling active/inactive wire labels, each gate's uniform shift can be translated by the true input assignment. The row nonce blocks must be reindexed along with those assignments; they are independent uniform blocks, so this is a permutation of the coin space. It is a new proof obligation for the fill, not a consequence of sampling a uniform arbitrary permutation.

Transmitting both output labels makes `outs_sink` essential: otherwise Bob can evaluate a downstream gate on both values of a revealed output wire. The condition is present. Adding unary identity gates to outputs fits the library's at-most-two-input gate model. The uniform family and polynomial size bound support computation of the circuit by both parties and both simulators. The joint PRF assumption is justified because the same unknown wire label can key both encryption families; separate marginal PRF assumptions do not establish their joint security. It is retained in `yaoProtocol_hbcSecure`, as are all strengthened OT premises. The theorem is consequently a faithful, explicitly specialized conditional realization of PS10's protocol, not an unconditional existence theorem for every bare `Functionality` or a completed proof from one-way TDPs alone.

## Checks of the included correctness and phase proofs

These are mathematical checks of the source proofs, not a claim of fresh kernel elaboration. The cryptographic security sketches were assessed for viable reductions and missing premises, not completed as formal proofs.

**Special encryption.** Let the pad have length `n+ℓ`, with n-bit key and nonce and an ℓ-bit message. The encrypted second component is the first n pad bits followed by the XOR-masked message. Its length is `n+ℓ`, so the decryption guards pass and the first n bits match exactly. The remaining computation is

\[
 (m\oplus p_{\ge n})\oplus p_{\ge n}=m.
\]

The source's list lemma carries the required length condition, preventing truncation from invalidating this equality. Pairing costs `2|r|+2` before the second component. For an n-bit message the inner length is therefore

\[
 2n+2+(n+n)=4n+2.
\]

For two keys, the outer pad has length `n+(4n+2)`. Applying the same correctness equation removes the outer encryption and then the inner encryption; exact n-bit decoding finishes. With zero keys, exact decoding of `ofFn` supplies correctness. With one key, there is one application. The longer-key branch is excluded by `DecCorrect`'s premise. `specialScheme.correct` supplies these lengths from its evaluator specification and uses an overlong failure sentinel, which cannot decode as an n-bit message.

**OT.** For Bob's known sample, the sampler contract gives an element whose evaluation is its encoded image under the permutation. Trapdoor inversion of that image decodes to the same element. Canonical decoding and `henc` therefore make both parties' H evaluations equal. At the selected coordinate,

\[
 h(x)\oplus\bigl(h(x)\oplus a_b\bigr)=a_b.
\]

This holds for every generator tape, both sampler tapes, and either choice bit, because inversion is specified on every inverter tape. The fifth move makes Alice's final next-message value empty. No enhanced hardness assumption is used for these exact correctness facts.

**Garbled evaluation.** The `runWith_sim` induction is on vertex number. The initial lists have the same length and satisfy the label relation at every input. For gate i, acyclicity places every argument below `inputs+i`, where the induction hypothesis applies. `gateOut_eq` equates the induced positional assignment with ordinary gate evaluation. `Good` then gives the correct label of the new value. Later appends leave earlier entries unchanged. This establishes `garbledValues_getD` at every vertex and, using the output-range field, `garbledOutput_eq`. Repeated fan-out is harmless. The probabilistic argument additionally uses the `Nodup` part of `IsFaninTwo` to make the different argument-position key pairs independent; it is not silently assuming independence for repeated arguments.

The union bound is valid uniformly in the plaintext: each gate has at most four assignments and at most three other rows per assignment, hence at most twelve cross-opening events. The output label of a gate is independent of its argument labels by acyclicity. Averaging the uniform-in-plaintext `WrongKeyBot` bound and summing over gates yields `12 * gates.length * δ`. This also explains why arbitrary table order is harmless for this correctness bound.

**Composition phases.** Write `L=calls(n)`, `R=ρ.rounds(n)`, `M=main.rounds(n)`. At global positions `2q` and `2q+1`, Alice's received-history length is q before her move and Bob's is q+1 before his. For `q<R*L`, division/remainder give the same run and local move to both parties. Filtering earlier selected slots therefore reconstructs the isolated subprotocol history. Induction on q gives the exact two slot lists after every complete pair. The empty-run case never uses a division with a positive-range premise; all corresponding slot lists are empty.

After all pairs, `answersFromA/B_run` read only those prefixes, independently of any appended main messages. The main mover parity is

\[
 \operatorname{moverIsV}(\mathrm{false},2LR+\mathrm{lead}+m)
 =\operatorname{moverIsV}(\mathrm{main.verifierFirst},m).
\]

For Bob-first main the lead is one; otherwise it is zero. Induction on the main prefix therefore gives `compose_exec_main` and the complete transcript/view identities. For outputs, `M>0` guarantees that Alice is past a possible leading filler and Bob is past the final run-pair filler. The two output identities then follow from the same total next-message functions. No correctness or security premise on ρ is needed for these layout identities.

**Yao.** The serialization equations recover the same garbled tables. `finProdFinEquiv` places call `(i,t)` at offset `i*n+t`; the OT functionality gives exactly bit t of Bob's selected input label there. Thus the initial label list equals `inputKeys` for the concatenated Boolean input, and the evaluated label list equals `garbledValues`. The vertex invariant gives the selected label at every output. Comparison returns false for its zero label and true for its one label **provided the labels are distinct**. The distinctness hypothesis is present throughout the conditional correctness chain. Bob returns that Boolean vector in the second move, and Alice's nonempty-history branch echoes it. Both outputs therefore equal the functionality under the stated conditions.

For actual Alice coins, the key blocks occupy the first `2Sn` bits; row nonce blocks use at most the next `8Sn`; masks use at most the final `2S`, since gate arity is at most two. They are disjoint. Output-label equality has probability `2^-n` at each output vertex; a valid negligible failure envelope is

\[
12S(n)\delta_0(n)+\mathrm{outLen}(n)2^{-n}.
\]

This is the right distribution and the right extra event for `yaoSeed_good_whp`. The probabilistic statement is admitted, rather than proved by the deterministic correctness lemmas.

## Adversarial instantiations

| Instance | Calculation or observation | Audit consequence |
|---|---|---|
| Malformed empty ciphertext, `n=ℓ=0` | `pairDecode []=none`; both total projections are `[]`; every raw decryption test is true; result is `some []`. | B-02. Does not affect honest round-trip correctness. |
| Equal zero/one output labels | `decodeOut k (pairEncode k k)=false`, including the unique zero-bit label. | `hdist` is necessary for the claimed exact conditional output theorem. At n=0 and nonempty output, the good-and-distinct event can be empty; a negligible envelope may be 1 at that finite length. |
| Ordinary hardness with a forward-evaluation sampler | For an arbitrary permutation f, use sampler `S(r)=f(r)`. Its output can still be uniform, but its coins reveal the inverse r and therefore the mask on the unselected OT input. | Canonicity and uniform sampling alone do not repair receiver privacy. The retained enhanced predicate premise excludes precisely this attack. This is a symbolic construction, not a finite demonstration of one-wayness. |
| Remove the sink condition | Put both inputs on Alice's side and output `(x0,x0 AND x1)`. For `x0=0`, both ideal outputs are `(0,0)`. Bob has the active x1 label and both x0 labels from the decoding pair; opening the AND row with x0's one-label returns the output label for x1, decoded by the second output pair. | The two x1 inputs have identical ideal outputs but are distinguished by this attack. `outs_sink` is load-bearing. |
| Zero-move main after one swap call | Standalone ρ has messages Alice's x, Bob's y, Alice's y, and outputs `(y,x)`. The composed run phase has six slots; Bob's final slot is empty. With no main move, his D8 output remains empty instead of x. | Reproduces the worker's counterexample. A zero-message local main can otherwise output the ideal answers. Positive main moves repair the phase transition. |
| Zero calls; zero subprotocol moves; either first mover | The exact histories were checked for call counts 0–3, subprotocol move counts 0–5, main move counts 1–6, both first movers in each protocol, and three tape/input salts. | All 1,728 history and output comparisons pass in the finite model; no extra `L>0` or `R>0` hypothesis is needed in the phase lemmas. |
| First-success versus unique opening | Give every wire identical zero/one labels and use correct key-matching encryption. Each of a two-input gate's four rows opens to its required (identical) output label. | `Good` is true and there are four openings. B-04 concerns claim coverage, not falsity of the first-success correctness theorem. |
| Duplicate gate arguments | Two positions reading the same vertex do not have independent key pairs. | Such gates fail `IsFaninTwo`, because it includes argument `Nodup`; the probability theorem does not apply to this attempted counterexample. |
| Separate versus joint PRFs | Setting both families to share an output prefix preserves plausible marginal pseudorandomness while a joint oracle reveals the common prefix immediately. | Marginal assumptions do not justify a two-family shared-key hybrid. `hG12` is an actual additional premise and is present. |

The executable finite checks pass 1,275 encryption round trips across key/nonce lengths 0–3 and message lengths 0–3, and 256 five-move OT correctness cases over both two-element permutations, every Boolean predicate, every sender input/choice, and both sampler tapes. They also exercise the malformed-zero case, output-label collision, nonsink attack, zero-main counterexample, and the distinction between Good and uniqueness. These finite checks do not test cryptographic hardness, prove the admitted theorems, or replace the mathematical source-proof review.

Reproduction: `python3 -I evidence/check_adversarial.py`; raw results are in `evidence/check_adversarial.json`. `python3 -I evidence/verify_inputs.py /path/to/exact-exchange-checkout` reproduces the byte checks when the four pinned commits are locally available; results are in `evidence/verification.json`.

## Declaration-by-declaration review

The following code-first definition restatements are my own descriptions. Each theorem row gives a statement/docstring assessment, including simple public reading equations rather than exempting them from review. An admitted theorem can have an appropriate statement; “matches” does not mean its proof has been completed. Private glue is marked. The generated field contracts follow the explicit declarations.

### [Defs.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/Defs.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `Functionality` · 74 | structure | Four polynomial length expressions and a deterministic map from the two input bit vectors to two private output vectors; no efficiency is built into the map. |
| `realA` · 93 | def | Encodes Alice's honest execution view together with Bob's actual output, using unary n as common input. |
| `realA_eq` · 99 | theorem | Matches the public equation for `realA`: encodes Alice's honest execution view together with Bob's actual output, using unary n as common input. |
| `realB` · 106 | def | Encodes Bob's honest execution view together with Alice's actual output. |
| `realB_eq` · 112 | theorem | Matches the public equation for `realB`: encodes Bob's honest execution view together with Alice's actual output. |
| `idealA` · 119 | def | Runs a simulator on Alice's input and ideal private output, then appends Bob's ideal output. |
| `idealA_eq` · 125 | theorem | Matches the public equation for `idealA`: runs a simulator on Alice's input and ideal private output, then appends Bob's ideal output. |
| `idealB` · 132 | def | Runs a simulator on Bob's input and ideal private output, then appends Alice's ideal output. |
| `idealB_eq` · 138 | theorem | Matches the public equation for `idealB`: runs a simulator on Bob's input and ideal private output, then appends Alice's ideal output. |
| `PolyTime` · 152 | def | Requires two uniform efficient strategies and one polynomial bound on every transmitted honest message for every typed input and tape. |
| `polyTime_iff` · 161 | theorem | Matches: exposes both efficient strategies and the bound over every honest input, tape, and transmitted message. |
| `HBCSecure` · 176 | def | Adds two fixed nonuniform PPT simulators; each distinguisher gets one negligible error bound covering both parties and every input at each n. |
| `hbcSecure_iff` · 184 | theorem | Matches: retains the simulator-before-distinguisher order and one negligible bound before all inputs. |
| `otFunctionality` · 194 | def | Takes two sender bits and one receiver choice; returns the empty vector to the sender and the chosen bit to the receiver. |
| `otFunctionality_inA` · 202 | theorem | Matches: Alice has two input bits. |
| `otFunctionality_inB` · 205 | theorem | Matches: Bob has one choice bit. |
| `otFunctionality_outA` · 208 | theorem | Matches: Alice's output length is zero. |
| `otFunctionality_outB` · 211 | theorem | Matches: Bob's output length is one. |
| `otFunctionality_f` · 214 | theorem | Matches: the output pair is the unique empty vector and the chosen sender bit. |
| `otFunctionality_f_snd` · 219 | theorem | Matches: the receiver's whole output vector is the chosen bit. |
| `otFunctionality_f_snd_apply` · 224 | theorem | Matches: the Fin casts only identify the declared two-bit input and one-bit choice/output spaces. |

### [ObliviousTransfer.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/ObliviousTransfer.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `otMask` · 93 | def | Inverts a received domain element with a fixed all-true inverter tape, evaluates H on the result, and XORs its word with one sender bit. |
| `otMask_eq` · 99 | theorem | Matches the public equation for `otMask`: inverts a received domain element with a fixed all-true inverter tape, evaluates H on the result, and XORs its word with one sender bit. |
| `otSender` · 106 | def | Uses fresh generator coins; sends the index on empty history, both masks after one message, and the empty word thereafter. |
| `otSender_coins` · 119 | theorem | Matches: Alice uses precisely the collection generator's coin polynomial. |
| `otSender_next` · 123 | theorem | Matches the public equation for `otSender`: uses fresh generator coins; sends the index on empty history, both masks after one message, and the empty word thereafter. |
| `otKnown` · 136 | def | Samples a domain element from the first sampler-sized block of Bob's tape. |
| `otKnown_eq` · 140 | theorem | Matches the public equation for `otKnown`: samples a domain element from the first sampler-sized block of Bob's tape. |
| `otRaw` · 144 | def | Samples a domain element using the suffix after that first block. |
| `otRaw_eq` · 148 | theorem | Matches the public equation for `otRaw`: samples a domain element using the suffix after that first block. |
| `otReceiver` · 154 | def | After the index, sends the permuted known sample in the chosen coordinate and the raw sample in the other; sends a filler next and computes the selected plaintext on other history lengths. |
| `otReceiver_coins` · 169 | theorem | Matches: Bob uses the sum of two sampler coin polynomials. |
| `otReceiver_next` · 174 | theorem | Matches the public equation for `otReceiver`: after the index, sends the permuted known sample in the chosen coordinate and the raw sample in the other; sends a filler next and computes the selected plaintext on other history lengths. |
| `otProtocol` · 189 | def | Runs those two strategies for five alternating moves, starting with Alice. |
| `otProtocol_P` · 196 | theorem | Matches: the prover-side field is otSender. |
| `otProtocol_V` · 199 | theorem | Matches: the verifier-side field is otReceiver. |
| `otProtocol_rounds` · 202 | theorem | Matches: the complete protocol has five moves. |
| `otProtocol_verifierFirst` · 205 | theorem | Matches: verifierFirst is false, so Alice starts. |
| `SamplerCanonical` · 211 | theorem | Matches: is a consequence of sample_spec and canonical decoding, rather than an additional premise of OT security. |
| `EnhancedHardCore` · 222 | def | Bounds prediction of the predicate on the inverse of a sampled element, given the generated index and the sampler's exact coins, averaged over generator coins. Attribution qualification: B-03. |
| `enhancedHardCore_iff` · 233 | theorem | Matches the public equation for `EnhancedHardCore`: bounds prediction of the predicate on the inverse of a sampled element, given the generated index and the sampler's exact coins, averaged over generator coins. |
| `otProtocol_outV` · 260 | theorem | Matches: gives the chosen sender bit on every tape from canonical henc; the proof derives its decoder-wide specification through apply_of_decD. |
| `otProtocol_outP` · 336 | theorem | Matches: the fifth move leaves Alice's next-message output empty on every tape. |
| `coinSeg` · 348 | def | Drops p(n) bits and takes q(n) bits from the coins of a decoded NUPPT layout. |
| `coinSeg_eq` · 353 | theorem | Matches the public equation for `coinSeg`: drops p(n) bits and takes q(n) bits from the coins of a decoded NUPPT layout. |
| `polyTimeComputable_coinSeg` · 360 | theorem | Matches: the parameter-controlled drop/take operation is uniformly polynomial-time on the decoded layout. |
| `simIdx` · 370 | def | Uses the generator-designated simulator tape block to produce an index at the decoded parameter, with empty argument and advice. |
| `simIdx_eq` · 376 | theorem | Matches the public equation for `simIdx`: uses the generator-designated simulator tape block to produce an index at the decoded parameter, with empty argument and advice. |
| `polyTimeComputable_simIdx` · 381 | theorem | Matches: generation and projection preserve polynomial time. |
| `simSample` · 391 | def | Samples at the simulated index from the sampler-sized block starting at p(n). |
| `simSample_eq` · 396 | theorem | Matches the public equation for `simSample`: samples at the simulated index from the sampler-sized block starting at p(n). |
| `polyTimeComputable_simSample` · 402 | theorem | Matches: generation, tape slicing, and the uniform sampler compose in polynomial time. |
| `otSimAFun` · 413 | def | Constructs Alice's encoded view from her input, generator tape, two raw samples as Bob's pair, and Bob's empty filler. |
| `otSimAFun_eq` · 422 | theorem | Matches the public equation for `otSimAFun`: constructs Alice's encoded view from her input, generator tape, two raw samples as Bob's pair, and Bob's empty filler. |
| `polyTimeComputable_otSimAFun` · 431 | theorem | Matches: all components of the sender-view serializer are polynomial-time. |
| `otSimA` · 443 | def | Packages that view function as a uniform PPT with generator coins followed by two sampler blocks. |
| `otSimA_coins` · 448 | theorem | Matches: the tape comprises one generator block and two sampler blocks. |
| `otSimA_uniform` · 453 | theorem | Matches: the constructed sender simulator is uniform, which is stronger than its use as a nonuniform simulator. |
| `runAt_otSimA` · 458 | theorem | Matches: identifies its complete runAt result with the explicit view serializer on the standard layout. |
| `otSimZb` · 467 | def | Forms Bob's selected ciphertext bit from the first simulated sample and the ideal selected output supplied to the simulator. |
| `otSimZb_eq` · 473 | theorem | Matches the public equation for `otSimZb`: forms Bob's selected ciphertext bit from the first simulated sample and the ideal selected output supplied to the simulator. |
| `otSimZ` · 479 | def | Places that selected bit in the choice coordinate and one independent random bit in the other coordinate. |
| `otSimZ_eq` · 489 | theorem | Matches the public equation for `otSimZ`: places that selected bit in the choice coordinate and one independent random bit in the other coordinate. |
| `otSimBFun` · 501 | def | Constructs Bob's encoded view from his choice, both sampler tapes, generated index, simulated mask pair, and Alice's empty filler. |
| `otSimBFun_eq` · 508 | theorem | Matches the public equation for `otSimBFun`: constructs Bob's encoded view from his choice, both sampler tapes, generated index, simulated mask pair, and Alice's empty filler. |
| `polyTimeComputable_otSimBFun` · 520 | theorem | Matches: the receiver-view serializer is polynomial-time under hH. |
| `otSimB` · 555 | def | Packages Bob's view function as a uniform PPT, using generator coins, two sampler blocks, and a fresh mask bit. |
| `otSimB_coins` · 560 | theorem | Matches: adds one independent bit to those three blocks. |
| `otSimB_uniform` · 566 | theorem | Matches: the constructed receiver simulator is uniform under hH. |
| `runAt_otSimB` · 572 | theorem | Matches: identifies its complete runAt result with the receiver serializer on that layout. |
| `otProtocol_simulators` · 621 | theorem | Matches the declared strengthened security statement; the short finite-input case count in its sketch needs the clarification in B-05. |
| `otProtocol_polyTime` · 645 | theorem | Matches: the conclusion is efficiency including honest message bounds, assuming the explicit polynomial-time evaluator H; this is admitted. |
| `otProtocol_hbcSecure` · 653 | theorem | Matches: packages the two simulator and efficiency statements and keeps henc, hH, one-wayness, and enhanced hard-core security. |

### [SpecialEncryption.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/SpecialEncryption.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `spEncStr` · 65 | def | Pairs the nonce with the first nonce-length pad bits followed by the message XOR the remaining pad; XOR truncates to the shorter list. |
| `spEncStr_eq` · 70 | theorem | Matches the public equation for `spEncStr`: pairs the nonce with the first nonce-length pad bits followed by the message XOR the remaining pad; XOR truncates to the shorter list. |
| `spDecStr` · 77 | def | Checks key, parsed nonce, and parsed body lengths, then pad-prefix equality; returns the XOR suffix or failure. It does not separately check successful pair parsing. The general malformed-rejection prose needs B-02. |
| `spDecStr_eq` · 86 | theorem | Matches the public equation for `spDecStr`: checks key, parsed nonce, and parsed body lengths, then pad-prefix equality; returns the XOR suffix or failure. It does not separately check successful pair parsing. |
| `zipWith_xor_xor_self` · 96 | private theorem | Matches: double XOR recovers the message when the pad is at least as long as that message. |
| `spDecStr_spEncStr` · 106 | theorem | Matches: exact key, nonce, message, and pad lengths suffice for perfect string-level decryption correctness. |
| `spEncFun` · 126 | def | Extracts key, message, and nonce from a NUPPT layout and applies string encryption. |
| `spEncFun_eq` · 131 | theorem | Matches the public equation for `spEncFun`: extracts key, message, and nonce from a NUPPT layout and applies string encryption. |
| `spDecFun` · 137 | def | Uses parameter length for both n and message length, and converts raw failure to the overlong word consisting of n+1 true bits. |
| `spDecFun_eq` · 143 | theorem | Matches the public equation for `spDecFun`: uses parameter length for both n and message length, and converts raw failure to the overlong word consisting of n+1 true bits. |
| `polyTimeComputable_spEncFun` · 149 | theorem | Matches: the encryption layout adapter is polynomial-time whenever the pad evaluator is. |
| `polyTimeComputable_spDecGuard` · 171 | private theorem | Matches: tests the three required lengths with polynomial-time projections and length comparisons. |
| `polyTimeComputable_spDecFun` · 209 | theorem | Matches: projections, length tests, prefix comparison, XOR, and conditional failure preserve polynomial time. |
| `runAt_spEnc` · 233 | theorem | Matches: the machine activation equals raw encryption on its actual nonce tape. |
| `runAt_spDec` · 243 | theorem | Matches: the machine activation equals raw decryption with the overlong sentinel for failure. |
| `length_spEncStr` · 253 | theorem | Matches: the stated sufficient pad-length assumption gives exactly 3 times the nonce length plus message length plus two bits. |

### [SpecialEncryptionSecurity.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `PRFOut` · 54 | structure | Requires a uniform evaluator on canonical n-bit key/input pairs and oracle pseudorandomness, with a polynomial output-length parameter. |
| `prfOut_var_iff` · 65 | theorem | Matches: ordinary PRF is exactly the n-bit-output instance of the generalized predicate. |
| `specialScheme` · 77 | def | Builds uniform-key generation, n-coin encryption, deterministic decryption, and the perfect-correctness field for n-bit messages. |
| `specialScheme_multiMessageSecure` · 111 | theorem | Matches: claims multi-message secrecy only under the length-doubling PRF assumption; the proof is admitted. |
| `spDecStr_wrongKey` · 125 | theorem | Matches: independently uniform encryption/decryption keys and nonce give a negligible failure-to-reject rate, uniformly in the message. |
| `specialScheme_wrongKey` · 143 | theorem | Matches: translates raw rejection to failure to decode an n-bit plaintext in the machine scheme; it is admitted. |

### [Garbling.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/Garbling.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `runWith_sim` · 89 | theorem | Matches: explicit initial correspondence, lengths, acyclicity, and local gate simulation imply correspondence at every in-range vertex. |
| `MultiEnc` · 125 | structure | An encryption/decryption interface for a list of keys and a plaintext key, with explicit encryption randomness and optional decryption failure. |
| `DecCorrect` · 136 | def | Requires exact decryption of every ciphertext encrypted under zero, one, or two keys, for every plaintext and tape. |
| `decCorrect_iff` · 141 | theorem | Matches the public equation for `DecCorrect`: requires exact decryption of every ciphertext encrypted under zero, one, or two keys, for every plaintext and tape. |
| `WrongKeyBot` · 150 | def | For each pair of distinct assignments to at most two positions, bounds successful decryption under the wrong assignment; the two keys at each position and the row tape are independent uniform samples. |
| `wrongKeyBot_iff` · 159 | theorem | Matches the public equation for `WrongKeyBot`: for each pair of distinct assignments to at most two positions, bounds successful decryption under the wrong assignment; the two keys at each position and the row tape are independent uniform samples. |
| `gateOut` · 172 | def | Renumbers the argument positions consecutively and evaluates the gate kind on a Boolean assignment to those positions. |
| `gateOut_eq_eval` · 177 | theorem | Matches the public equation for `gateOut`: renumbers the argument positions consecutively and evaluates the gate kind on a Boolean assignment to those positions. |
| `map_args_eq_ofFn` · 182 | theorem | Matches: mapping over argument vertices equals enumerating their argument positions. |
| `map_range_getD_ofFn` · 188 | private theorem | Matches: reading the consecutive positions of an ofFn list recovers the assignment. |
| `gateOut_eq` · 197 | theorem | Matches: the assignment induced from the gate's actual arguments gives its original DAGGate evaluation. |
| `GarbleSeed` · 215 | abbrev | Contains two labels per circuit vertex, randomness for each assignment at each gate, and a row permutation for each gate. |
| `GarbleSeed_eq` · 222 | theorem | Matches the public equation for `GarbleSeed`: contains two labels per circuit vertex, randomness for each assignment at each gate, and a row permutation for each gate. |
| `keyAt` · 231 | def | Reads a vertex's selected label within the circuit and otherwise returns the inhabited default. |
| `keyAt_eq` · 235 | theorem | Matches the public equation for `keyAt`: reads a vertex's selected label within the circuit and otherwise returns the inhabited default. |
| `argKeys` · 239 | def | Lists the labels selected by an assignment at the gate's argument vertices, in argument order. |
| `argKeys_eq` · 245 | theorem | Matches the public equation for `argKeys`: lists the labels selected by an assignment at the gate's argument vertices, in argument order. |
| `garbledRow` · 251 | def | Encrypts the correct output label under that assignment's argument labels and its designated row randomness. |
| `garbledRow_eq` · 257 | theorem | Matches the public equation for `garbledRow`: encrypts the correct output label under that assignment's argument labels and its designated row randomness. |
| `garbledTable` · 264 | def | Enumerates assignments in a fixed order and applies the seed's permutation before constructing their encrypted rows. |
| `garbledTable_eq` · 270 | theorem | Matches the public equation for `garbledTable`: enumerates assignments in a fixed order and applies the seed's permutation before constructing their encrypted rows. |
| `tableAt` · 276 | def | Returns the garbled table at a valid gate vertex; returns an empty table at input vertices or outside the circuit. |
| `tableAt_eq` · 281 | theorem | Matches the public equation for `tableAt`: returns the garbled table at a valid gate vertex; returns an empty table at input vertices or outside the circuit. |
| `tableAt_gate` · 286 | theorem | Matches: at vertex n+i with a valid gate index, the table is precisely gate i's table. |
| `evalGate` · 296 | def | Tries the table rows in order using the supplied argument labels, returning the first successful plaintext or the default label. |
| `evalGate_eq` · 301 | theorem | Matches the public equation for `evalGate`: tries the table rows in order using the supplied argument labels, returning the first successful plaintext or the default label. |
| `inputKeys` · 306 | def | Lists the active labels selected by the Boolean input vector. |
| `inputKeys_eq` · 310 | theorem | Matches the public equation for `inputKeys`: lists the active labels selected by the Boolean input vector. |
| `garbledValues` · 315 | def | Runs the abstract DAG evaluator from an initial label list, using its current length as the next gate vertex. |
| `garbledValues_eq` · 320 | theorem | Matches the public equation for `garbledValues`: runs the abstract DAG evaluator from an initial label list, using its current length as the next gate vertex. |
| `garbledOutput` · 325 | def | Reads the circuit output vertex after garbled evaluation from the selected input labels. |
| `garbledOutput_eq_getD` · 330 | theorem | Matches the public equation for `garbledOutput`: reads the circuit output vertex after garbled evaluation from the selected input labels. |
| `Good` · 336 | def | Requires the first successful decryption at every gate, for every argument assignment, to return its correct output label; it does not assert uniqueness. Source-coverage qualification: B-04. |
| `good_iff` · 343 | theorem | Matches the public equation for `Good`: requires the first successful decryption at every gate, for every argument assignment, to return its correct output label; it does not assert uniqueness. |
| `garbledValues_getD` · 359 | theorem | Matches: Good suffices for the label of every Boolean wire value, without a uniqueness hypothesis. |
| `garbledOutput_eq` · 393 | theorem | Matches: specializes the vertex invariant to the circuit's designated output. |
| `uprob_not_good_le` · 415 | theorem | Matches its first-success Good claim and the 12-per-gate union bound; source uniqueness is a separate qualification in B-04. |

### [GarblingSpecial.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/GarblingSpecial.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `innerLen` · 48 | def | The polynomial 4n+2, including the inner ciphertext's pairing overhead. |
| `innerLen_eq` · 51 | theorem | Matches the public equation for `innerLen`: the polynomial 4n+2, including the inner ciphertext's pairing overhead. |
| `nestedSpecial` · 57 | def | With no keys, encodes the plaintext directly; with one key, uses E1; with two, encrypts under the second key using E1 then under the first using E2. Other key-list lengths give empty encryption and failed decryption. |
| `nestedSpecial_decCorrect` · 92 | theorem | Matches: for zero, one, and two keys, exact pad lengths remove the encryption layers and recover the original n-bit label. |

### [GarblingSecurity.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `nestedSpecial_wrongKeyBot` · 66 | theorem | Matches: separate PRF hypotheses suffice for the nested wrong-key rejection bound; no joint-security claim is made here. |
| `garbling_good_whp` · 77 | theorem | Matches: bounds failure of Good under a uniform full GarbleSeed by 12 times the gate count times one negligible function. |

### [Hybrid.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/Hybrid.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `HybridProtocol` · 74 | structure | Stores a message protocol, a polynomial call count, and each party's call inputs as functions of its own original input, main tape, and call index. |
| `answersA` · 90 | def | Concatenates Alice's ideal output vectors in call order. |
| `answersA_eq` · 95 | theorem | Matches the public equation for `answersA`: concatenates Alice's ideal output vectors in call order. |
| `answersB` · 101 | def | Concatenates Bob's ideal output vectors in call order. |
| `answersB_eq` · 106 | theorem | Matches the public equation for `answersB`: concatenates Bob's ideal output vectors in call order. |
| `privA` · 112 | def | Pairs Alice's original input with her concatenated ideal answers. |
| `privA_eq` · 115 | theorem | Matches the public equation for `privA`: pairs Alice's original input with her concatenated ideal answers. |
| `privB` · 119 | def | Pairs Bob's original input with his concatenated ideal answers. |
| `privB_eq` · 122 | theorem | Matches the public equation for `privB`: pairs Bob's original input with his concatenated ideal answers. |
| `pairFstD_privA` · 126 | theorem | Matches: the first decoded component of Alice's augmented input is her original input. |
| `pairSndD_privA` · 131 | theorem | Matches: its second decoded component is her ideal answer vector. |
| `pairFstD_privB` · 136 | theorem | Matches: Bob's first decoded component is his original input. |
| `pairSndD_privB` · 141 | theorem | Matches: his second decoded component is his ideal answer vector. |
| `Coins` · 146 | abbrev | Uses exactly the pair of main-protocol tapes at unary parameter n. |
| `coins_eq` · 149 | theorem | Matches: the hybrid uses the pair of main-protocol execution tapes at unary n. |
| `realA` · 155 | def | Runs main on the augmented inputs and the same tapes used to form the calls, then pairs Alice's view with Bob's output. |
| `realA_eq` · 166 | theorem | Matches the public equation for `realA`: runs main on the augmented inputs and the same tapes used to form the calls, then pairs Alice's view with Bob's output. |
| `realB` · 177 | def | Runs that same augmented execution and pairs Bob's view with Alice's output. |
| `realB_eq` · 188 | theorem | Matches the public equation for `realB`: runs that same augmented execution and pairs Bob's view with Alice's output. |
| `PolyTime` · 206 | def | Requires efficient main strategies, uniform polynomial-time call-input evaluators, and a message bound for every answer vector of the required lengths. |
| `polyTime_iff` · 232 | theorem | Matches: the answer vectors range over all strings of the required lengths, a stronger condition than bounding only ideal executions. |
| `HBCSecure` · 259 | def | Uses the hybrid real samplers, ordinary ideal samplers, hybrid efficiency, and two simulators with errors uniform over typed inputs. |
| `hbcSecure_iff` · 267 | theorem | Matches: changes the real experiment to hybrid execution while preserving the ideal experiment and uniform error quantifiers. |

### [Compose.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/Compose.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `moveMsg` · 94 | def | Computes the current mover's next message on its received history after k standalone moves. |
| `moveMsg_eq` · 100 | theorem | Matches the public equation for `moveMsg`: computes the current mover's next message on its received history after k standalone moves. |
| `exec_eq_map` · 112 | theorem | Matches: the two received histories are exactly the opposite-party move subsequences, in chronological order. |
| `exec_fst_length_pos` · 137 | theorem | Matches: a verifier-first execution gives Alice at least one received message after any positive number of moves. |
| `exec_snd_length_pos` · 146 | theorem | Matches: a prover-first execution gives Bob at least one received message after any positive number of moves. |
| `slotMsgs` · 155 | def | Reads selected entries off+p from a received-message list, defaulting to empty outside the list. |
| `slotMsgs_eq` · 159 | theorem | Matches the public equation for `slotMsgs`: reads selected entries off+p from a received-message list, defaulting to empty outside the list. |
| `slotMsgs_eq_map` · 164 | theorem | Matches: agreement at every selected slot permits replacing the selected-history map by the supplied function. |
| `runTape` · 172 | def | Slices c bits after the initial c0 bits and j preceding c-bit run tapes. |
| `runTape_eq` · 175 | theorem | Matches the public equation for `runTape`: slices c bits after the initial c0 bits and j preceding c-bit run tapes. |
| `length_runTape` · 179 | theorem | Matches: an in-range run index and the exact total tape length imply that this slice has its full prescribed length. |
| `getD_map_range` · 187 | theorem | Matches: the indexed entry of a mapped range is the function's value, provided the index is below the range length. |
| `getD_append_left` · 193 | theorem | Matches: an index below the first list's length is unaffected by appending a second list. |
| `moverIsV_false_two_mul` · 198 | theorem | Matches: the prover is the mover at every even global position when it starts. |
| `moverIsV_false_two_mul_add_one` · 203 | theorem | Matches: the verifier is the mover at every odd global position in that schedule. |
| `lead` · 221 | def | Adds one Alice filler before main precisely when main starts with Bob. |
| `lead_eq` · 224 | theorem | Matches the public equation for `lead`: adds one Alice filler before main precisely when main starts with Bob. |
| `lead_of_true` · 227 | theorem | Matches: verifier-first main inserts exactly one lead filler. |
| `lead_of_false` · 231 | theorem | Matches: prover-first main inserts no lead filler. |
| `runInputA` · 238 | def | Computes Alice's jth call input using her original private input and main-tape prefix; returns empty outside the call range. |
| `runInputA_of_lt` · 244 | theorem | Matches: an in-range Alice call uses the original input and exactly her main-tape prefix. |
| `runInputA_of_ge` · 250 | theorem | Matches: an out-of-range Alice call returns the empty word. |
| `runInputB` · 257 | def | Computes Bob's jth call input using his original private input and main-tape prefix; returns empty outside the call range. |
| `runInputB_of_lt` · 263 | theorem | Matches: an in-range Bob call uses his original input and main-tape prefix. |
| `runInputB_of_ge` · 269 | theorem | Matches: an out-of-range Bob call returns the empty word. |
| `runNextA` · 277 | def | Activates the subprotocol sender with her call input, run-tape block, and the selected Bob messages from this run. |
| `runNextA_eq` · 283 | theorem | Matches the public equation for `runNextA`: activates the subprotocol sender with her call input, run-tape block, and the selected Bob messages from this run. |
| `runNextB` · 293 | def | Activates the subprotocol receiver with his call input, run-tape block, and the selected Alice messages from this run. |
| `runNextB_eq` · 299 | theorem | Matches the public equation for `runNextB`: activates the subprotocol receiver with his call input, run-tape block, and the selected Alice messages from this run. |
| `answersFromA` · 308 | def | Reads Alice's final subprotocol outputs from her received history, pads or truncates each to G's output length, and concatenates them. |
| `answersFromA_eq` · 314 | theorem | Matches the public equation for `answersFromA`: reads Alice's final subprotocol outputs from her received history, pads or truncates each to G's output length, and concatenates them. |
| `answersFromB` · 322 | def | Reads, pads or truncates, and concatenates Bob's final subprotocol outputs. |
| `answersFromB_eq` · 328 | theorem | Matches the public equation for `answersFromB`: reads, pads or truncates, and concatenates Bob's final subprotocol outputs. |
| `composeP` · 344 | def | Uses received-history length as a pair index; performs Alice subprotocol moves or fillers, possibly the lead filler, then main on the original input paired with reconstructed answers. |
| `composeP_next` · 358 | theorem | Matches the public equation for `composeP`: uses received-history length as a pair index; performs Alice subprotocol moves or fillers, possibly the lead filler, then main on the original input paired with reconstructed answers. |
| `composeP_coins` · 371 | theorem | Matches: Alice's coin polynomial is the main polynomial plus calls times rho's sender polynomial. |
| `composeV` · 382 | def | Uses the predecessor of received-history length as a pair index; performs Bob subprotocol moves or fillers, then main after dropping run slots and the lead filler. |
| `composeV_next` · 395 | theorem | Matches the public equation for `composeV`: uses the predecessor of received-history length as a pair index; performs Bob subprotocol moves or fillers, then main after dropping run slots and the lead filler. |
| `composeV_coins` · 407 | theorem | Matches: Bob's coin polynomial is the analogous receiver expression. |
| `compose` · 414 | def | Starts Alice and runs twice the subprotocol move count per call, then the optional lead filler and main; tapes concatenate the main and subprotocol tapes. |
| `compose_P` · 421 | theorem | Matches: the composed prover-side field is composeP. |
| `compose_V` · 424 | theorem | Matches: the composed verifier-side field is composeV. |
| `compose_rounds` · 427 | theorem | Matches: the polynomial expression represents calls*(2*rho.rounds)+lead+main.rounds. |
| `compose_rounds_eval` · 432 | theorem | Matches: evaluates the syntactic move-count expression to 2LR+lead+M. |
| `compose_verifierFirst` · 437 | theorem | Matches: Alice starts the composed protocol. |
| `compose_P_coinLen` · 443 | theorem | Matches: Alice's tape length is the main length plus the call count times the subprotocol length. |
| `compose_V_coinLen` · 463 | theorem | Matches: Bob's tape has the analogous independent block allocation. |

### [ComposePhases.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/ComposePhases.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `runExec` · 70 | def | The standalone received histories after k moves of run j, on its computed inputs and sliced tapes. |
| `runExec_eq` · 76 | theorem | Matches the public equation for `runExec`: the standalone received histories after k moves of run j, on its computed inputs and sliced tapes. |
| `runMsg` · 83 | def | The standalone message at position p of run j. |
| `runMsg_eq` · 89 | theorem | Matches the public equation for `runMsg`: the standalone message at position p of run j. |
| `slotFromB` · 97 | def | The expected Bob message in a run-phase pair: the standalone subprotocol message when Bob moves, and empty otherwise. |
| `slotFromB_eq` · 103 | theorem | Matches the public equation for `slotFromB`: the expected Bob message in a run-phase pair: the standalone subprotocol message when Bob moves, and empty otherwise. |
| `slotFromA` · 111 | def | The corresponding expected Alice run-phase message or filler. |
| `slotFromA_eq` · 116 | theorem | Matches the public equation for `slotFromA`: the corresponding expected Alice run-phase message or filler. |
| `answersRealA` · 124 | def | Concatenates Alice's padded final outputs of independently executed honest subprotocol runs. |
| `answersRealA_eq` · 132 | theorem | Matches the public equation for `answersRealA`: concatenates Alice's padded final outputs of independently executed honest subprotocol runs. |
| `answersRealB` · 142 | def | Concatenates Bob's padded final outputs of those honest runs. |
| `answersRealB_eq` · 150 | theorem | Matches the public equation for `answersRealB`: concatenates Bob's padded final outputs of those honest runs. |
| `mainExec` · 161 | def | Executes main on each original input paired with its real run answers, using the main prefixes of the composed tapes. |
| `mainExec_eq` · 167 | theorem | Matches the public equation for `mainExec`: executes main on each original input paired with its real run answers, using the main prefixes of the composed tapes. |
| `mul_add_div_of_lt` · 177 | private theorem | Matches: quotient of Rj+p is j under p<R, which also implies R>0. |
| `mul_add_mod_of_lt` · 181 | private theorem | Matches: the corresponding remainder is p under the same strict bound. |
| `mul_add_le_of_lt` · 185 | private theorem | Matches: the complete block of an in-range run ends no later than LR, including R=0. |
| `slotFromB_mul_add` · 191 | theorem | Matches: an in-range submove selects the correct Bob slot or its empty filler. |
| `slotFromA_mul_add` · 197 | theorem | Matches: an in-range submove selects the correct Alice slot or its filler. |
| `slotMsgs_runFst` · 205 | theorem | Matches: the stated prefix-slot agreement recovers Alice's isolated run history through p submoves. |
| `slotMsgs_runSnd` · 217 | theorem | Matches: the symmetric selected slots recover Bob's isolated history. |
| `compose_exec_run` · 240 | theorem | Matches: after q pairs within the run phase, both received histories have the exact expected slot layout. |
| `compose_exec_runs` · 298 | theorem | Matches: extracting any in-range run after the full run phase gives its standalone transcript, including zero-move runs. |
| `answersFromA_run` · 321 | theorem | Matches: appending any suffix to the correct run-slot prefix leaves Alice's reconstructed answers equal to the standalone answers. |
| `answersFromB_run` · 334 | theorem | Matches: the same suffix independence holds for Bob's reconstructed answers. |
| `compose_P_next_main` · 353 | theorem | Matches: Alice's next message agrees with main once she is beyond the lead; the verifier-first case explicitly requires a positive main prefix. |
| `compose_V_next_main` · 383 | theorem | Matches: Bob's next message agrees with main once he has received the lead or a first main message. |
| `compose_exec_main` · 427 | theorem | Matches: the complete run prefix, optional lead, and arbitrary main prefix have the stated decomposition, even when that main prefix is empty. |
| `compose_exec_rounds` · 486 | theorem | Matches: substitutes the actual composed move count in that transcript identity. |
| `compose_transcript` · 509 | theorem | Matches: gives the same identity using the typed execution-coin wrapper. |
| `compose_viewP` · 525 | theorem | Matches: Alice's view contains her original input and full tape, followed by Bob's run slots and main messages. |
| `compose_viewV` · 540 | theorem | Matches: Bob's view additionally includes Alice's optional leading filler. |
| `compose_outP` · 560 | theorem | Matches: the positive-main hypothesis makes Alice's D8 output exactly her main output on the reconstructed answers. |
| `compose_outV` · 581 | theorem | Matches: the same positive-main hypothesis moves Bob past the final run filler, giving his main output. |

### [ComposeSecurity.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `exists_ofFn_eq` · 82 | private theorem | Matches: every list with the stated length is an ofFn encoding of a bit vector of that length. |
| `length_answersRealA` · 88 | theorem | Matches: padding every answer makes the concatenation exactly calls times outA bits. |
| `length_answersRealB` · 95 | theorem | Matches: the analogous Bob answer length is exact. |
| `exists_mainExec_eq_transcript` · 111 | theorem | Matches: sufficient main-tape prefixes and fixed answer lengths produce a well-typed honest main transcript. |
| `exists_runExec_eq_transcript` · 145 | theorem | Matches: an in-range run and exact composed tape lengths produce a well-typed honest subprotocol transcript. |
| `runMsg_mem` · 178 | theorem | Matches: every strictly in-range submove belongs to one of the two final received-message lists. |
| `compose_msg_bound` · 202 | theorem | Matches: the sum of the two bounds covers run messages, main messages, and empty fillers for all honest tapes. |
| `composeP_efficient` · 294 | theorem | Matches: the full hypothesis supplies efficient call-input computation and both strategies needed to implement Alice's total activation. |
| `composeV_efficient` · 303 | theorem | Matches: the corresponding total Bob activation has the same polynomial-time closure argument. |
| `polyTime_compose` · 314 | theorem | Matches: combines the two admitted strategy-efficiency claims with the proved honest-message bound. |
| `hbcSecure_compose` · 375 | theorem | Matches the specialized composition theorem, including hM; its source number and sampler-output/view distinction were checked in the official draft. |

### [Yao.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/Yao.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `encodeCircuit` · 123 | def | Pairs a DAG circuit description with an encoded list of unary output-vertex descriptions. |
| `encodeCircuit_eq` · 128 | theorem | Matches the public equation for `encodeCircuit`: pairs a DAG circuit description with an encoded list of unary output-vertex descriptions. |
| `encodeMsgs_inj` · 133 | private theorem | Matches: equal encodings and equal list lengths imply equality of the message lists. |
| `encodeNat_inj` · 145 | private theorem | Matches: equality of unary integer encodings implies equality of the integers. |
| `encodeCircuit_injective` · 154 | theorem | Matches: for fixed input and output arities, the serialized circuit and output list determine both components. |
| `YaoCircuit` · 175 | structure | A uniform polynomial-size family with polynomial input/output lengths, in-range sink output vertices, and well-formed fan-in-at-most-two gates. |
| `output` · 206 | def | Reads the listed output vertices after Boolean evaluation on Alice's input concatenated with Bob's. |
| `output_apply` · 211 | theorem | Matches the public equation for `output`: reads the listed output vertices after Boolean evaluation on Alice's input concatenated with Bob's. |
| `yaoFunctionality` · 221 | def | Gives both parties that same vector of circuit output values. |
| `readBits` · 234 | def | Reads a fixed-length vector at an offset, supplying false beyond the source word. |
| `readBits_apply` · 237 | theorem | Matches the public equation for `readBits`: reads a fixed-length vector at an offset, supplying false beyond the source word. |
| `assignIdx` · 243 | def | Interprets an assignment with its first coordinate as the least significant binary digit. |
| `assignIdx_eq` · 247 | theorem | Matches the public equation for `assignIdx`: interprets an assignment with its first coordinate as the least significant binary digit. |
| `xorShift` · 253 | def | The involutive permutation that XORs every assignment coordinate with its corresponding mask bit. |
| `xorShift_apply` · 259 | theorem | Matches the public equation for `xorShift`: the involutive permutation that XORs every assignment coordinate with its corresponding mask bit. |
| `xorShift_symm_apply` · 263 | theorem | Matches: the inverse permutation uses the same XOR mask because applying that mask twice is identity. |
| `yaoCoins` · 269 | def | Allocates 10 times sizeBound times n bits plus twice sizeBound for row shifts. |
| `yaoCoins_eq` · 273 | theorem | Matches the public equation for `yaoCoins`: allocates 10 times sizeBound times n bits plus twice sizeBound for row shifts. |
| `yaoCoins_eval` · 278 | theorem | Matches: evaluation gives exactly 10*S(n)*n+2*S(n), including reserved unused blocks. |
| `yaoSeed` · 293 | def | Slices labels from the first 2Sn bits, two nonce blocks for each of four reserved rows per gate from the next 8Sn bits, and up to two shift bits per gate from the final 2S bits. |
| `yaoSeed_fst` · 301 | theorem | Matches: label b at vertex v reads n bits at offset (b*S+v)*n. |
| `yaoSeed_snd_fst` · 307 | theorem | Matches: each row reads two consecutive n-bit nonce blocks at its reserved four-row-per-gate position. |
| `yaoSeed_snd_snd` · 314 | theorem | Matches: the row permutation is the XOR shift from the final gate-mask block, not a uniform arbitrary permutation. |
| `keyAt_yaoSeed` · 320 | theorem | Matches: an in-range vertex reads its label from the specified key block, without using the default branch. |
| `decodeMsgs` · 331 | def | Uses the shared word-list decoder, including its total behavior on malformed words. |
| `decodeMsgs_eq` · 338 | theorem | Matches: the total decoder has the stated empty/nonempty recurrence, including its one-empty-message behavior on malformed nonempty words. |
| `decodeMsgs_encodeMsgs` · 349 | theorem | Matches: the shared decoder exactly inverts Strategy.encodeMsgs for arbitrary finite message lists. |
| `decodeMsgs_nil` · 360 | theorem | Matches: empty input decodes to an empty message list. |
| `yaoTables` · 369 | def | Serializes the list of garbled gate tables, serializing each table as a list of rows. |
| `yaoTables_eq` · 374 | theorem | Matches the public equation for `yaoTables`: serializes the list of garbled gate tables, serializing each table as a list of rows. |
| `yaoKeysA` · 382 | def | Serializes the labels for Alice's actual input bits. |
| `yaoKeysA_eq` · 387 | theorem | Matches the public equation for `yaoKeysA`: serializes the labels for Alice's actual input bits. |
| `yaoPairs` · 395 | def | Serializes the ordered zero-label/one-label pair for every output vertex. |
| `yaoPairs_eq` · 401 | theorem | Matches the public equation for `yaoPairs`: serializes the ordered zero-label/one-label pair for every output vertex. |
| `yaoMsg` · 408 | def | Pairs the tables with a nested pair containing Alice's active input labels and the output decoding pairs. |
| `yaoMsg_eq` · 412 | theorem | Matches the public equation for `yaoMsg`: pairs the tables with a nested pair containing Alice's active input labels and the output decoding pairs. |
| `yaoBobTables` · 420 | def | Reads the gate-indexed table from Alice's message, returning an empty table at input vertices and by default beyond the serialized list. |
| `yaoBobTables_eq` · 427 | theorem | Matches the public equation for `yaoBobTables`: reads the gate-indexed table from Alice's message, returning an empty table at input vertices and by default beyond the serialized list. |
| `yaoBobInit` · 435 | def | Builds initial labels from Alice's serialized labels followed by n-bit blocks of Bob's OT answers. |
| `yaoBobInit_eq` · 442 | theorem | Matches the public equation for `yaoBobInit`: builds initial labels from Alice's serialized labels followed by n-bit blocks of Bob's OT answers. |
| `yaoBobValues` · 450 | def | Runs the garbled DAG evaluator on the decoded tables and initial labels. |
| `yaoBobValues_eq` · 455 | theorem | Matches the public equation for `yaoBobValues`: runs the garbled DAG evaluator on the decoded tables and initial labels. |
| `decodeOut` · 464 | def | Returns false for the first label; otherwise returns whether the label equals the second. Equal labels therefore decode as false. |
| `decodeOut_eq` · 469 | theorem | Matches the public equation for `decodeOut`: returns false for the first label; otherwise returns whether the label equals the second. Equal labels therefore decode as false. |
| `decodeOut_fst` · 473 | theorem | Matches: the first label always decodes to false, even if the labels coincide. |
| `decodeOut_snd` · 477 | theorem | Matches: the second label decodes to true only under the explicitly retained inequality of the labels. |
| `yaoBobOut` · 483 | def | Reads each output label from Bob's evaluated values and compares it with the corresponding transmitted decoding pair. |
| `yaoBobOut_eq` · 489 | theorem | Matches the public equation for `yaoBobOut`: reads each output label from Bob's evaluated values and compares it with the corresponding transmitted decoding pair. |
| `yaoAlice` · 500 | def | On empty history sends the garbling for the first part of her augmented input; on nonempty history echoes its first message. |
| `yaoAlice_next_nil` · 507 | theorem | Matches: the empty-history branch sends yaoMsg for the first component of Alice's augmented input. |
| `yaoAlice_next_cons` · 511 | theorem | Matches: every nonempty history returns its first received message. |
| `yaoAlice_coins` · 515 | theorem | Matches: Alice uses exactly the yaoCoins polynomial. |
| `yaoBob` · 520 | def | Deterministically evaluates the first received garbling with the OT answers in the second part of his augmented input. |
| `yaoBob_next` · 525 | theorem | Matches the public equation for `yaoBob`: deterministically evaluates the first received garbling with the OT answers in the second part of his augmented input. |
| `yaoBob_coins` · 530 | theorem | Matches: Bob's strategy has the zero coin polynomial. |
| `yaoMain` · 535 | def | The two-move Alice-then-Bob message protocol using these strategies. |
| `yaoMain_outV` · 544 | theorem | Matches: on any supplied augmented inputs, Bob's final result evaluates Alice's generated message with his answer component. |
| `yaoMain_outP` · 554 | theorem | Matches: after two moves Alice echoes the result Bob transmitted. |
| `yaoCall` · 565 | def | Splits the flattened call index into a Bob-input-wire index and a key-bit index. |
| `yaoCall_eq` · 569 | theorem | Matches the public equation for `yaoCall`: splits the flattened call index into a Bob-input-wire index and a key-bit index. |
| `yaoCall_finProdFinEquiv` · 573 | theorem | Matches: flattening and unflattening the wire/bit index agree in wire-major order i*n+t. |
| `yaoHybrid` · 584 | def | Makes inB(n) times n ideal bit OTs using Alice's label bits and Bob's repeated input choices, then runs yaoMain. |
| `yaoHybrid_callA` · 594 | theorem | Matches: the sender's two input bits are bit t of the zero and one labels on Bob's wire. |
| `yaoHybrid_callB` · 602 | theorem | Matches: every bit OT for a given wire uses Bob's same input choice bit. |
| `getD_ofFn'` · 610 | private theorem | Matches: reading an in-range position of an ofFn list returns the function value independently of the default. |
| `yaoBobTables_yaoMsg` · 616 | theorem | Matches: the nested serialization round trip gives the original tableAt function at all vertices, including out-of-range ones. |
| `yaoBobInit_yaoMsg` · 639 | theorem | Matches: the stated per-bit answer condition and Alice's message recover exactly the active labels for the concatenated input. |
| `yaoBobValues_yaoMsg` · 667 | theorem | Matches: under that same answer condition Bob's entire evaluation is the abstract garbled evaluation. |
| `yaoBobOut_yaoMsg` · 687 | theorem | Matches: correct answer bits, Good, and distinct output labels imply the exact Boolean output vector. |
| `flatten_ofFn_one` · 705 | private theorem | Matches: concatenating the one-bit output vectors preserves their index order. |
| `yaoHybrid_answersB_getD` · 717 | theorem | Matches: the ideal bit calls supply every bit of each selected Bob input label in the required wire-major order. |
| `yaoBobOut_yaoMsg_of_eq` · 739 | private theorem | Matches: transports the conditional Bob-correctness statement along equality of the two parameter lengths. |
| `yaoHybrid_correct` · 764 | theorem | Matches: under Good and output-label distinctness, both protocol outputs equal their respective, identical ideal output vectors. |
| `yaoSeed_good_whp` · 823 | theorem | Matches: the probability is over Alice's actual bit tape and includes both bad evaluation and output-label collisions, rather than assuming uniform full row permutations. |
| `yaoHybrid_polyTime` · 850 | theorem | Matches: assumes efficient E1 and E2, but needs no PRF or evaluator-specification hypothesis merely for runtime. |
| `yaoHybrid_simulators` · 916 | theorem | Matches: assumes joint PRF security in addition to the marginal hypotheses and retains uniform error bounds for all inputs; the security proof is admitted. |
| `yaoHybrid_hbcSecure` · 940 | theorem | Matches: packages hybrid efficiency and simulation for the declared uniform family with sink outputs, retaining joint PRF security. |

### [YaoReal.lean](https://github.com/Shilun-Allan-Li/tcslib/blob/3f6db40e1688c4a0bb922c9575dd3bd2157a650b/TCSlib/Cryptography/SecureComputation/YaoReal.lean)

| Declaration · line | Kind | Independent restatement or statement/docstring assessment |
|---|---|---|
| `yaoProtocol` · 64 | def | Replaces the ideal bit calls of yaoHybrid by the five-move concrete OT protocol through the published composer. |
| `yaoProtocol_P` · 67 | theorem | Matches: real Yao's prover-side strategy is composeP applied to the concrete OT protocol. |
| `yaoProtocol_V` · 72 | theorem | Matches: its verifier-side strategy is the corresponding composeV. |
| `yaoProtocol_rounds` · 77 | theorem | Matches: the concrete move-count expression is exactly the composition expression; for Yao it evaluates to 10*inB(n)*n+2. |
| `yaoProtocol_verifierFirst` · 83 | theorem | Matches: Alice starts real Yao. |
| `yaoProtocol_hbcSecure` · 95 | theorem | Matches: instantiates composition with the two-move main and concrete OT; joint PRF security, hH, canonical henc, one-wayness, and enhanced hard-core security all remain explicit. |

### Generated field contracts

These are the sixteen explicitly requested `simps` reading equations. Their source-generating definitions were inspected above; this is not an independently elaborated declaration census.

| Contract | Assessment |
|---|---|
| `specialScheme_gen` | Matches: uniform generation returns the n coin bits. |
| `specialScheme_enc` | Matches: encryption is the string-encryption machine with n nonce coins. |
| `specialScheme_dec` | Matches: decryption is the deterministic string-decryption machine. |
| `nestedSpecial_enc` | Matches: exposes the zero-, one-, two-, and longer-key encryption cases. |
| `nestedSpecial_dec` | Matches: exposes the corresponding decoding/decryption/failure cases. |
| `yaoFunctionality_inA` | Matches: takes Alice's input length from Y. |
| `yaoFunctionality_inB` | Matches: takes Bob's input length from Y. |
| `yaoFunctionality_outA` | Matches: Alice's output length is Y.outLen. |
| `yaoFunctionality_outB` | Matches: Bob's output has the same length. |
| `yaoFunctionality_f` | Matches: gives both parties Y.output. |
| `yaoMain_P` | Matches: uses yaoAlice. |
| `yaoMain_V` | Matches: uses yaoBob. |
| `yaoMain_rounds` | Matches: has two moves. |
| `yaoMain_verifierFirst` | Matches: Alice starts. |
| `yaoHybrid_main` | Matches: uses yaoMain. |
| `yaoHybrid_calls` | Matches: makes inB(n)*n ideal bit calls. |

The facade imports all thirteen modules. The root export imports the facade. These are source-level export checks only; root-export elaboration is not claimed. The facade's short Contents description of `SpecialEncryption` should also be read together with `GarblingSpecial`, where actual nesting is defined.

## Admissions and closing disposition

There are thirteen explicit admitted proof bodies in the primary modules: `otProtocol_simulators`, `otProtocol_polyTime`, `specialScheme_multiMessageSecure`, `spDecStr_wrongKey`, `specialScheme_wrongKey`, `uprob_not_good_le`, `nestedSpecial_wrongKeyBot`, `composeP_efficient`, `composeV_efficient`, `hbcSecure_compose`, `yaoSeed_good_whp`, `yaoHybrid_polyTime`, and `yaoHybrid_simulators`. The wrappers `otProtocol_hbcSecure`, `garbling_good_whp`, `polyTime_compose`, `yaoHybrid_hbcSecure` and `yaoProtocol_hbcSecure` do not remove these dependencies. This statement gate was commissioned before their fills, so their disclosed admission is not itself a blocker.

The retained correctness repairs were independently verified at the frozen source: five OT messages; derived sampler canonicity; canonical-only henc extended by canonical decoding; enhanced rather than ordinary predicate security; Good over every assignment; explicit efficiency; Yao in the hybrid model followed by the concrete composition; sink outputs; output-label distinctness; actual-bit-tape probability; and joint PRF security.

**Closing count: 0 blockers, 0 majors, 5 minors. Gate 06B's issued statement-audit threshold is met.** The five minors should be recorded and corrected in the normal intake/resolution process. This verdict neither closes sibling gates nor approves merging unfinished security proofs as completed results.

## Notation glossary

- `n`: security parameter and wire-label bit length; `ℓ`: plaintext bit length.
- `m`, `k`, `r`, `p`: plaintext, encryption key, nonce, and evaluated pad in the encryption calculation.
- `p_{≥n}`: the pad suffix after its first n bits; `xor` or `⊕`: coordinatewise Boolean XOR at the stated equal lengths.
- `a_b`: the sender bit chosen by Bob; `h`: the predicate used in OT; `f`: a permutation in the sampler counterexample.
- `x`, `y`: the parties' original inputs; in the local OT cancellation calculation, x is instead the known sampled preimage, as in the source proof.
- `L`, `R`, `M`: number of calls, moves per subprotocol run, and moves of main; `lead`: the optional single leading filler.
- `q`, `j`, `m`: global run-pair index, run index, and main-prefix length in the phase argument; m here is a count rather than a plaintext.
- `S(n)`: the circuit family's sizeBound at n; `δ0(n)`: the negligible nested wrong-key error; `δ(n)`: a resulting negligible failure envelope.
- `x0`, `x1`: the two Alice input bits in the nonsink-output attack.
