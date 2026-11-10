# Pass–shelat Gate 09 — external Codex findings

**Verdict: CLEAR for the scope of this round.**

**Counts:** 0 blockers, 0 majors, 0 minors, 2 notes. The pack's closing threshold is met.

| Pin | Audited value |
|---|---|
| Draft PR | [Shilun-Allan-Li/tcslib #284](https://github.com/Shilun-Allan-Li/tcslib/pull/284) |
| Lean head | `46e9b8b8773e5188c5b0f4732f3fff8d9092fa2d` |
| Lean base | `37e161131e68ff347ed59b59b9ebcd66ffa9ea43` |
| Campaign records | `ecade1097967bca84261be7df2b2af5a77e4a955` |
| Exchange | `0433f8528227a16414f3dc427c033d324b2b8844` |
| Source | `Pass–Shelat.pdf` at the records pin; book page = PDF page − 12 |

This verdict covers the adaptive game, its cap-one correspondence, the collection shift, and the RSA/Rabin width equations. The future adaptive security lifts and n-bit construction endpoints are not proved by this round.

**Verification limit:** I independently checked committed bytes, the source statements and proofs, and the consistency of the supplied native evidence. Lean, Lake, and Elan are absent from this environment; I did not independently rerun the Lean checks, declaration census, or axiom collector. Native execution results below are attributed to the supplied evidence, rather than represented as my own kernel replay. Campaign and exchange branches were left untouched.

## Findings

Paths below are relative to `TCSlib/Cryptography/` unless otherwise stated. Probe references are inside the packaged `verification.zip`.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| N1 | note | `Encryption/PublicKey/OracleSecurity.lean:697–703` · `BitPublicKeyScheme.SingleBitSecure.padded_cpa`; `probes/EndpointContracts.lean:38–48` | The adaptive CPA endpoints still require proofs handling public-key-dependent message choices. The existing fixed-message/fixed-vector security results alone do not discharge this obligation. This is explicitly deferred work, not a regression in this gate. | `padded_cpa` retains exactly its base statement and `sorry`. The proposed endpoints and lifts use `example : Prop := ...`, which constructs propositions, not proofs of them. The two concrete construction probes prove `SingleBitSecure` only. | At the subsequent proof gate, prove the single-bit CPA bridge and the adaptive reduction, then justify the n-bit construction through an adaptive bitwise simulation or an equivalent reduction. Retain the current distinction between proved single-bit compositions and proposed adaptive endpoints. |
| N2 | note | `probes/EndpointContracts.lean:44` · proposed CCA2 endpoint | The displayed CCA2 existential has no hardness premise. It is a well-formed target proposition, not an established unconditional existence theorem or a completed construction contract. | The command is `example : Prop := ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cca2`. The pack expressly leaves the CCA2 construction and its ruling for later. | Before issuing that construction theorem, select and state its actual assumptions and construction. The generic single-to-adaptive CCA2 lift, separately, needs no additional cryptographic assumption beyond `S.INDSecure .cca2`. |

## 1. Package and source integrity

Read the exchange README, gate README, complete bundle, and the six revision-qualified indexed records. Retrieved the four pinned Git commits into a separate local object database and extracted their committed blobs.

All four entries of `SHA256SUMS` pass:

| File | Verified SHA-256 |
|---|---|
| `BUNDLE-FILES.txt` | `f99586e9bc3b8ccd53d27f52fef7c81337b64f7146f43a12289df9f65a87325d` |
| `README.md` | `9960806cad6c9601a84947907fd4803118e4f00b0cc85e93b80a767e340ef59d` |
| `bundle.md` | `678bf8915e6430ad9bc381e7af9fcf03b2fc6aeb3c102e6d1a97ad4064f5214f` |
| `verification.zip` | `b117b044e9e4e63fcd955882bd549d19fe609633f5d4b6b1217686a0446cfcfc` |

- The six bundle section names and their order match `BUNDLE-FILES.txt`. Each section's payload matches its file at the records pin, allowing only the bundle's separator newlines.
- All ten changed Lean files match `SOURCE-SHA256SUMS` at the Lean head.
- Regenerating `git diff --no-ext-diff --abbrev=9 BASE HEAD` reproduces the packaged `pr.diff.txt` byte for byte. Its scope is exactly ten Lean files.
- All 150 source hashes in `verification.zip/plan-r2.json` match committed source at the audited head, including `TCSlib.lean` and campaign `Checks.lean`.
- The source PDF has SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Checked Definition 171.5 and its oracle table on PDF pages 183–184, Definition 56.1 on PDF page 68, and the RSA/Rabin source statements, including Theorems 57.2 and 63.10.

Inputs: [pinned audit directory](https://github.com/Shilun-Allan-Li/tcslib/tree/0433f8528227a16414f3dc427c033d324b2b8844/outbox/gates/09-adaptive-pke-gate), [pinned records](https://github.com/Shilun-Allan-Li/tcslib/tree/ecade1097967bca84261be7df2b2af5a77e4a955/briefs/pass-shelat-ch5-8/gates/09-adaptive-pke), [source PDF](https://github.com/Shilun-Allan-Li/tcslib/blob/ecade1097967bca84261be7df2b2af5a77e4a955/Pass%E2%80%93Shelat.pdf).

## 2. Adaptive game and cap-one agreement

Reviewed `Encryption/PublicKey/AdaptiveSecurity.lean:43–247` and the added typed readers in `OracleSecurity.lean:512–607`.

1. `adaptiveIndGame` independently samples one generator tape and one adversary tape. Key generation is deterministic on its sampled tape; its repeated syntactic occurrences give the same key pair. The public key is supplied to the adversary. Subsequent activations use the same adversary tape and the encoded complete query/answer log. The hidden bit is fixed throughout the game; it selects the first message when false and the second when true.
2. Every challenge below the cap samples a fresh encryption tape and prepends exactly the returned ciphertext. Under generated keys, `enc_length` makes `padFin` a lossless fixed-width reading of the encryption output. A repeated ciphertext is still prepended, so collisions consume distinct fresh challenges. Starting from the empty history, the history contains exactly the freshly issued ciphertexts, newest first; its length never exceeds the cap or the number of oracle calls.
3. Every decryption query equal to any history entry is refused before consulting the old oracle. Thus an earlier challenge remains blocked after a later challenge is issued. Other queries retain the old oracle's availability and decoding rules:

   | Mode | Decryption availability outside the history |
   |---|---|
   | CPA | Always refused |
   | CCA1 | Available exactly while the history is empty |
   | CCA2 | Available throughout |

   Successful decoding returns a true validity bit followed by the message. Failed decoding and refusal return all-false strings of message width plus one. Decryption never changes the history.
4. The total budget counts both oracle kinds, including requests made after challenge-cap exhaustion. The cap separately counts fresh encryptions. At a full nonempty history, a challenge returns the latest ciphertext with no new randomness or history entry. At cap zero from the initial state, it returns the fixed zero ciphertext-width reply. These explicit conventions support the intended game: cap one recovers the old repeat rule, and choosing a cap at least the total budget permits a fresh encryption on every challenge request.
5. Malformed machine outputs terminate with the codec's false final bit; they are not silently padded into valid challenge requests. At total budget zero, an immediate final answer is allowed; a requested oracle call instead produces the false timeout result. At cap zero, decryption availability remains as above and no hidden-bit-dependent encryption occurs.
6. `adaptiveIndImpl_one` covers both oracle indices and both optional old states. `simulate_adaptiveIndImpl_one` inducts over the entire oracle computation, preserving the state relation “optional challenge ↔ its zero- or one-element list.” Consequently `adaptiveIndGame_one` proves equality of the complete probabilistic computations for every machine, budget, bit and parameter. This is stronger than equality of one response. It faithfully extends the existing encoding of Definition 171.5; the source itself has only one challenge.
7. `AdaptiveINDSecure.single` retains the arbitrary total-query polynomial and specializes only the challenge cap to `.const 1`. The resulting bound is exactly the existing `INDSecure` condition.

No defect found in these statements or proofs. The new input/output width readers make the dependent casts explicit instead of requiring the consumer to unfold the foreign specification lengths.

## 3. Constant shift, probability transport, and widths

Reviewed `Asymptotic/CollectionShift.lean:39–271`, the parameter-change contracts in `Complexity/Randomized/Closure.lean:282–347`, and the candidate width proofs.

1. The forward parameter change is the computed polynomial `n ↦ n+c`, so it preserves uniformity. The generator, sampler and inverter each have a tape equivalence preserving `List.ofFn`, and each activation at `n` equals the original activation at `n+c` on that same encoded tape. In particular, the index and trapdoor come from the same transported generator tape. The domains, finite/inhabited instances, encoder, decoder, permutation, function and evaluator are retained. The sampler-membership and trapdoor-inversion laws are transported at the same parameter.
2. `shiftParameter_sampleClose` retains the quantifier over **every generator tape**. For each such tape, it relabels uniform sampler coins by `shiftSampleCoins`. It therefore transports the original closeness bound to `δ(n+c)`, rather than replacing a pointwise generated-index guarantee by an average guarantee.
3. For inversion, fix an attacker `A` against the shifted collection. The constructed original attacker `B` at parameter `m` runs `A` at `m−c` on the initial `A.coinLen(m−c)` bits of its tape. This nonuniform parameter-change contract is applicable because `m−c ≤ m`; original one-wayness quantifies over all nonuniform PPT attackers.
4. At `m=n+c`, subtraction recovers `n`. Put `a=A.coinLen n` and `s=A.coinLen(n+c)−a`. Polynomial monotonicity gives `s≥0` and `B.coinLen(n+c)=a+s`. Under the tape-splitting equivalence, the prefix and suffix are independent uniform tapes. For each fixed generated index and domain element, the success event depends only on the prefix. Its probability is therefore

   \[
   2^{-(a+s)}\sum_{u\in\{0,1\}^{a}}\sum_{v\in\{0,1\}^{s}}
       \mathbf 1[\mathrm{success}(u)]
   =2^{-a}\sum_{u\in\{0,1\}^{a}}\mathbf 1[\mathrm{success}(u)].
   \]

   Relabeling the generator tape and averaging over the same domain gives precisely `shiftParameter_exists_invProbAt`. Zero-length prefixes or suffixes remain nonempty one-point tape spaces, so this argument includes `c=0` and `n=0`.
5. Both sampler error and inversion probability are negligible after composition with `n ↦ n+c`. The moved `Negligible.comp_of_le` uses a threshold at least one, so its reciprocal-power comparison is valid and places no requirement on the initial parameter. Its statement and proof source are exactly retained from the base.
6. The width equations quantify over every generator tape and every element of its generated domain, including fallback tapes. RSA's encoder writes at the width of the generated modulus component, `2 * max n 2`; Blum Rabin's writes at the generated index width, `2 * max n 3`. After shifting, for every natural `n`,

   \[
   2\max(n+2,2)=2(n+2),\qquad
   2\max(n+3,3)=2(n+3).
   \]

   These are the exact syntactic `PolyExpr` evaluations required by the Goldreich–Levin interface, not merely asymptotic bounds. At `n=0` they give widths four and six.

The checked single-bit composition terms preserve the intended assumptions: RSA uses `ArithmeticFP` and `RSAAssumption`; Rabin uses `ArithmeticFP`, `BlumDensity`, and `FactoringAssumption`. No extra cryptographic assumption is introduced by shifting.

## 4. Feasibility of the deferred lifts

Both proposed implications `INDSecure .cpa → AdaptiveINDSecure .cpa` and `INDSecure .cca2 → AdaptiveINDSecure .cca2` have plausible standard hybrid reductions with the current contracts. This is feasibility feedback, not a completed Lean proof.

The reduction must embed one selected fresh challenge, encrypt the other selected message halves locally under the supplied public key with independent coins, and preserve the adversary's adaptive transcript. Adjacent hybrids change the response at one fresh-challenge position, not a predetermined plaintext chosen independently of the public key. If the selected position is never reached, the adjacent experiments coincide and the single-challenge reduction can finish without asking its challenge. A polynomially bounded hybrid index can be carried in nonuniform advice; a polynomial hybrid loss preserves negligibility.

For CCA2, the simulator must maintain the **entire** issued-ciphertext history, including its locally generated ciphertexts. It refuses those queries itself and forwards only ciphertexts outside that history. This also handles collisions with the embedded challenge. A latest-ciphertext-only filter would be insufficient; the present game correctly uses full membership.

The implementation proofs still need polynomial bounds for the encoded history, a counter, local encryption tapes, and oracle calls, together with an exact simulation theorem covering malformed moves and timeout. These are supporting machine contracts, not additional hardness premises. If the existing interactive-handler interface is used, its pending `Games.exists_interactiveHandlerMachine` proof (`Games/Efficiency.lean:510–522`) is also a proof dependency to discharge or explicitly track.

For the candidate n-bit CPA endpoints, a sound route is the single-bit CPA bridge followed by adaptive bitwise simulation, with a polynomial number of inner fresh challenges. The existing `PublicKeyScheme.Secure` and `MultiMessageSecure` quantify over fixed messages/vectors; their presence alone does not prove security for message pairs selected from the observed public key. N1 records this distinction. No bitwise preservation of CCA2 is claimed.

## 5. Policy, admissions, and native evidence

- Both new modules have the required headers, source references, public reading equations, and sketches for the substantive proofs. Their imports reach `TCSlib.lean` through the existing facades. The shift uses existing machine parameter-change constructions and coin-splitting lemmas; it introduces no private runner or duplicated machine host.
- The source diff adds no `sorry`, `admit`, axiom declaration, or global simp attribute. The old `padded_cpa` statement and its `sorry` are byte-identical to the base. The relocation of `Negligible.comp_of_le` preserves its theorem name and source proof.
- The supplied declaration-census program and output report 995 prior declarations with matching types/metadata, 99 additions, and one old body difference for the unchanged admitted `padded_cpa`. I verified the relevant source preservation independently; I did not reproduce the stored-expression comparison. The reported body difference is consistent with the source-position change caused by the inserted readers.
- The supplied axiom collector checks the new modules and selected added/moved declarations, including generated constants. Its log reports 99 selected declarations using only `propext`, `Classical.choice`, and `Quot.sound`. The endpoint probe separately reports those standard axioms for both concrete shifted single-bit compositions.
- The 150-entry replay order and 15-entry final-delta order match their plans and all corresponding `PASS` rows. Their 150 and 15 individual logs are present. This is supplied execution evidence; the independent binding to the audited source is the 150-file hash comparison above.
- All five seal manifests have matching source/probe hashes. Their line maps cover every original source line without changes. The five logs verify installation and end-of-file preservation for 20, 23, 11, 7 and 7 requests respectively: 68 total. The raw shift-evaluator conversion control fails under seal; the unsealed control and published-reader control have the expected successful logs. The harness checks name components, owners, reducibility, instance metadata and preservation of typeclass lookup. `PolyExpr.eval` is explicitly excluded from these seals; I inspected the touched proof uses separately and found the relevant published evaluation equations used.
- Compared the lint diagnostics themselves, not just their totals: all baseline FAIL/WARN entries remain the same except RSA/Rabin file-length numbers. Both runs report 155 existing failures and 103 warnings. No new diagnostic is hidden by an offsetting removal.

**Closing assessment:** CLEAR at the pinned head for this gate's stated scope; N1 and N2 remain subsequent-milestone observations.

**Notation:** `n` is the shifted security parameter; `c` is the fixed nonnegative shift; `m` is the original parameter; `δ` is the original sampler error; `A` and `B` are respectively the shifted and original inversion attackers; `a` and `s` are consumed-prefix and unused-suffix coin lengths; `u` and `v` range over those tapes; `success(u)` is the fixed-index, fixed-domain-element inversion event; `1[·]` is its indicator. Other named interfaces are repository identifiers.
