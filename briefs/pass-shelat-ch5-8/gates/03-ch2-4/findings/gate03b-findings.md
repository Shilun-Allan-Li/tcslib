# Gate 03b findings: [PS10] ch. 2–4, one-wayness and collections

External statement audit of `TCSlib/Cryptography/Asymptotic/{OneWay, Collections, Permutations}.lean`
and `TCSlib/Cryptography/Candidates/Arithmetic.lean` at `a3c5fa8b72e50939822f22364647dc844a3914a0`,
following the brief of pack 03b (and pack 03a's common brief and severity guide). Audit date 2026-11-05.

**Outcome: 1 major, 3 minor, 10 notes. The pack does not close** (it closes at 0 blockers and 0 majors).
The major (#1) is a gap in the collection interface: it constrains the evaluator, the hard-core evaluator
and the trapdoor inverter only up to decoding, not on the strings a collection actually produces. The
`PublicKey.lean` consumer should be checked; if it is affected, #1 becomes a blocker (see #1).

## Limitations of this audit

- **The source PDF was not attached.** Only `gate03b-bundle.md` arrived, and the container cannot reach
  the hosts that serve [PS10]. I checked statements against the source quotations in
  `inventory-ch2.md` (§2, §3), the definitions as `DESIGN.md` reproduces them, and my own knowledge of
  [PS10]. Places where the exact printed wording or numbering matters, and that I could not check, are
  marked **†**. In particular I could not check: the exact parameters printed in the §2.4.3 proof
  (Claim 38.2), whether "Remark 33.2" is a numbered item, and the §-numbers cited in #3. A re-check of
  the † items against pp. 26–29, 33–42 and 55–57 is cheap and recommended.
- I did not build or replay anything. The attestations are checked for internal consistency only
  (section 7).
- Files outside the bundle (`Candidates/Factoring.lean`, `PublicKey.lean`, `Adversary.lean`,
  `OneWayYao.lean`, `CollectionsLemmas.lean`) were not visible. Where a finding depends on them, the
  finding says so.

## 1. Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `Asymptotic/Collections.lean` · `Collection` (`eval_spec`, `sample_spec`), `Collection.HardCore`, `TrapdoorCollection.inv_spec`, `TrapdoorCollection.inv_preimage` | The collection interface pins its string-level algorithms only up to `decD`, which may be lenient (many strings per element) and need not be efficient. `eval` is specified on canonical encodings and on sampled strings, the hard-core evaluator `H` only on canonical encodings, and `Inv` only by "its output *decodes* to `f_i⁻¹(y)`". The sampler's and `Inv`'s outputs need not be canonical. So the definition does not let anyone compute `h_i(x)` from a sampled string, or `f_i`/`h_i` on `Inv`'s output. Every TDP construction needs exactly these: [PS10, Algorithm 104.3] (TDP public-key encryption), signature verification `f_i(Inv(t, ·))`, and oblivious transfer `h_i(f_i⁻¹(y_j))`. Run 3a's P3-1 fixed the evaluator on sampled strings only, and the pack asks whether that is enough; it is not. | **Counterexample (all fields hold, the TDP scheme fails).** Take any trapdoor collection `T₀` with canonical decoding (e.g. domains `{0,1}^ℓ` decoded by `decodeFin`) and a hard-core `h` with evaluator `H₀`. Define `T`: `encD x = false :: encD₀ x`; `decD (b :: w) = decD₀ w`, `decD [] = none`; `f i x = false :: f₀ i x` (`= encD (perm x)`, so `f_perm` holds at every `i`); `eval ⟨i, b :: w⟩ = false :: eval₀ ⟨i, w⟩`; `gen := T₀.gen`; `sample` outputs `true :: (T₀'s sample)`; `Inv(t, false :: u) = false :: Inv₀(t, u)`; `H ⟨i, b :: w⟩ = [(H₀ ⟨i, w⟩).headD false xor b]`. Since `T₀` decodes canonically, `T₀`'s sampler and `Inv₀` output canonical strings, on which `H₀` gives `h`. Then `eval_spec`, `sample_spec` (decodes, and `eval` is right on `true :: w₀`), `inv_spec`, `SampleClose` and hardness all carry over from `T₀`. A `T`-inverter becomes a `T₀`-inverter by dropping its first output bit, with the same success. `HardCore h` holds because `H` agrees with `h` on canonical encodings. Yet Algorithm 104.3 built on `T` encrypts with `H` on the sampled string `true :: w₀`, i.e. with `¬h(x)`, and decrypts with `H` on `Inv`'s output `false :: …`, i.e. with `h(x)`. **Every ciphertext decrypts to the flipped bit.** Variant: let `Inv` emit the prefix `true` and set `eval ⟨i, true :: w⟩ := []` while the sampler emits `false`. Then `eval ⟨i, Inv(t, y)⟩ = [] ≠ y`, although `inv_spec` holds and the sanity lemma `inv_preimage` (decode-level only) still proves. | Make decoding canonical: add `decD_canonical : ∀ i w x, decD i w = some x → w = encD i x`. Then `sample_spec` reduces to membership, `eval_spec` covers every decodable string, and `Inv`'s outputs are canonical. If some instances need lenient decoders, instead strengthen `eval_spec` to `∀ i w x, decD i w = some x → eval ⟨i, w⟩ = f i x`, and `HardCore`'s first clause to `∀ i w x, decD i w = some x → H ⟨i, w⟩ = [h i x]`. Either way, add the string-level sanity lemma `eval ⟨i, Inv(t, encD y)⟩ = encD y` beside `inv_preimage`. **Before closing:** check whether the correctness of `PublicKey.lean`'s `tdpBitScheme` (and `TrapdoorCollection.glPad`) is stated over these fields without an extra hypothesis. If it is, that statement is false and this finding is a **blocker**. |
| 2 | minor | `Asymptotic/OneWay.lean` · `FunFamily`, `FunFamily.ofString` (and `DESIGN.md` D5, module docstring) | D5, the module docstring and `FunFamily`'s docstring present `ofString f p` as "the textbook `f : {0,1}* → {0,1}*`" without conditions. `ofString` truncates to `p(n)` bits and pads with `false` (`getD … false`), which is not injective across output lengths. So it is the textbook function only for length-regular `f`. `ofString`'s own docstring says this ("exact when `LengthRegular f p`"); the other three statements do not. | Take `f` whose output length varies with `x` at fixed `|x|`: the binary product of `f_mult` (Def 29.1), or `⟨M, M(x)⟩` of Algorithm 64.2. `ofString f p` identifies `y` with `y ++ [false]` and truncates outputs longer than `p(n)`. Both create new preimages, so `(ofString f p).StrongOneWay` can fail while `f` is one-way. Conversely, the typed experiment demands a same-length preimage. The library already pads injectively elsewhere: `Collection.owfFamily` uses `padFin (L n) (w ++ [true])`, proved injective by `padFin_append_true_injective`. | State the `LengthRegular` proviso in D5 and in the `FunFamily` and module docstrings, or switch `ofString` to marker padding (`padFin (p n) (f x ++ [true])` with `p` a strict output bound), as `owfFamily` does. |
| 3 | minor | `OneWay.lean` · `OneWayPermutation`; `Collections.lean` · `Collection.HardCore`, module docstring | Attribution defects (policy §2). † `OneWayPermutation` cites "[PS10, §2.12 and Theorem 79.4]", but §2.12 is the Rabin section; one-way permutations are §2.10 (Def 55.1, collection form), as `Collections.lean`'s own header says. `Collection.HardCore` and the module docstring list Theorem 126.4 as a consumer of the *collection* hard-core. `DESIGN.md` §7 item 47 records that Theorem 126.4 uses a single OWP, not Def 55.1's collection. | Compare `Collections.lean` header "[PS10, §2.5, §2.10, §2.11]" and inventory "§2.10–§2.11 Permutations and trapdoors / §2.12 Rabin" with the `OneWayPermutation` docstring. Compare `HardCore`'s docstring "used by Lemma 84.1, Algorithm 104.3, Theorem 126.4" with DESIGN §7.47. | Cite §2.10 / Def 55.1 for `OneWayPermutation`, noting that the single-permutation form (as used in Thms 79.4, 126.4) is the campaign's. Remove Theorem 126.4 from `Collection.HardCore`'s consumers. |
| 4 | minor | `Collections.lean` · `Collection.OneWay.owfFamily_strongOneWay`; `OneWay.lean` · `weak_to_strong` | The two proof sketches describe constructions the code does not perform. Policy §3 ("Synchronization": a sketch of a proof the code no longer performs is worse than none). | **`owfFamily_strongOneWay`:** the *Hard* sketch has the reduction "check that the answer `z` has length `gen.coins(n) + sample.coins(n)` (`lenEq`, `ite`), split it into `(r₁', r₂')`". `collInvRaw` performs no length check and only drops the first `gen.coins(|u|)` bits. The *Easy* sketch builds the padding from `blockMap`/`unaryPoly`/`pairTakePoly L`; `owfFamily_easy` uses `polyTimeComputable_padStr L`. **`weak_to_strong`:** the sketch's advice `⟨A'.advice n, ⟨1^{m n}, ⟨1^{T n}, ⟨1^{k n}, …⟩⟩⟩⟩` and coin layout differ from the machine actually built (`OneWay.exists_yaoReduction`, advice `⟨A'.advice n, 1^{kk}⟩`). Its closing "Implementation" paragraph admits the difference but does not replace the sketch. | Rewrite both sketches to describe the implemented reductions. For `weak_to_strong`, fold the "Implementation" paragraph into the sketch. |
| 5 | note | `Collections.lean` · `PermCollection` (`perm`, `f_perm`) | Stronger than Def 55.1 ("each `f_i`, `i ∈ I`, is a permutation"): `perm` and `f_perm` quantify over **every** string `i`. With `eval_spec`, `eval ⟨i, ·⟩` must therefore permute a finite nonempty set of encodings at every junk index too. Harmless, because any source collection can be re-encoded to meet it. | An evaluator with `eval ⟨i, w⟩ = true :: w` on unparseable `i` has no finite invariant set, so no `PermCollection` exists with that `eval`. Re-encoding fixes it: prefix real encodings with a marker bit and let `eval` fix a reserved string that serves as the junk domain's only element. The existing RSA/Rabin instances compile, so their authors handled this. | Optional: restrict `perm`/`f_perm` to generated indices, or say in the docstring that junk indices need a fixed-point domain. |
| 6 | note | `Collections.lean` · `TrapdoorCollection` (deviation P3-5) | Pack Q4: is the deviation "literal `Inv((i, t), y)` not adopted" benign? **Yes, and the two classes coincide.** The docstring justifies it by the candidates ("the index is recoverable from the trapdoor in every candidate"), which is narrower than needed. | A Def 56.1 TDP becomes one of this shape by replacing `t` with `t' := ⟨i, t⟩`, i.e. `Gen'` outputs `⟨i, ⟨i, t⟩⟩`. This is efficient, and harmless because `t` is never shown to the adversary (`Collection.invProbAt` gives it `⟨i, y⟩` only). Conversely, a formal TDP is a text TDP whose `Inv` ignores `i`. | State the general argument in the deviation line. |
| 7 | note | `Collections.lean` · `TrapdoorCollection.OneWay`, `Collection.HardCore` (forward fitness, ch. 5–8) | The hardness predicates give the adversary `⟨i, f_i(x)⟩` only. Oblivious transfer from TDPs (EGL), if ch. 5–8 formalizes it, needs the receiver to sample `y_{1−b}` itself, so security must hold **given the domain sampler's coins**. This "enhanced TDP" property (Goldreich, *Foundations* vol. 2, App. C.1) cannot be expressed with the current predicates. | This is the standard gap in the textbook OT proof. `SampleClose` plus ideal-`x` hardness says nothing about inverting `Sample(i; s)` when `s` is known. | No change here. The ch. 5–8 planners should state an enhanced-hardness predicate rather than cite `TrapdoorCollection.OneWay` for OT. |
| 8 | note | `OneWay.lean` · `weak_to_strong`, `strong_prod_two`, `claim_38_2`; `Collections.lean` · `Collection.OneWay.exists_strongOneWay` | All four land in the campaign notion `FunFamily.StrongOneWay`: parameter `n`, arbitrary polynomial input length. 42.2 (⇒) gives `inLen = gen.coins + sample.coins`. The adversaries of 35.1/35.2 receive `1^n`, not `1^{n·m(n)}` / `1^{2n}`. This is benign: `N = n·m(n)` is polynomial in `n` and `n ≤ N`, so negligibility in `n` and in `N` coincide, and the unary parameter is computable in both directions (module docstring). However, no lemma relates `FunFamily.StrongOneWay` to the text's single OWF on `{0,1}^n` (the `ofString` form). The parameter-`n` reading of 35.1/35.2 and Claim 38.2's change of `T`/threshold appear only in docstrings, not in DESIGN §5. | DESIGN §5 entry 6 records `m = 2nq(n)` and the rejection-sampled position, but not the parameter-`n` adversary or `T = 2n·m(n)·n^c + 1` in place of `2nm²p(n)`. Those are in `claim_38_2`/`weak_to_strong` docstrings and the module docstring. | Optional bridge lemma: a strong `FunFamily` with strictly increasing `inLen` yields an `ofString`-form OWF (pad, and pass the excess bits in the clear). Add one register line for the parameter-`n` direct products and Claim 38.2's parameters. |
| 9 | note | `OneWay.lean` · `WorstCaseOneWayLit`; DESIGN §5 entry 16 | The headline/literal split and both bridges are right. The literal form's vacuity is wider than the deviation text says ("every length-shrinking family whose output length does not determine `n`"): it also occurs for non-shrinking families. | `inLen = outLen = const 1`, `f n b = b xor [n odd]`. This family is `Easy` and inverted by a `1^n` machine, so `WorstCaseOneWay` is false. Yet `WorstCaseOneWayLit` holds: on input `y ∈ {0,1}` the literal machine is activated at parameter `1` whatever `n` is, so no single machine inverts both parities with probability 1. | Reword: "can be satisfied vacuously by any family whose output length does not determine `n` (constant `outLen`), e.g. …". For `PolyExpr` lengths, "injective" and "non-constant" coincide, so `toParam` covers exactly the non-degenerate families. |
| 10 | note | `Permutations.lean` · module docstring, `permBits` | Pack Q5: **parameters as stated** (`permBits n = Nat.size n`, `permTrials n = 2·n·n`), and **failure ≤ `n·2^{−n}`, which is negligible**. A union bound over `n` positions, each failing with probability `≤ (1 − 1/2^k)^T ≤ (1 − 1/(2n))^{2n²} ≤ 2^{−n}`. One docstring slip: "`n ≤ 2^k ≤ 2n`" is stated unconditionally, but `2^{size 0} = 1 > 0`. | `two_pow_permBits_le` correctly carries `0 < n`. `uprob_permFromCoins_none_le_two_pow` handles `n = 0` separately. Coin use is `n·2n²·size n ≤ 2n⁴`. `permFromCoins_uniform_of_some` (sorried in run 3) is now axiom-clean (evidence `axioms.log`). | Add "for `n ≥ 1`" to the two docstrings. |
| 11 | note | `Candidates/Arithmetic.lean` · `ArithmeticFP` | Pack Q6. **Reasonable stand-in.** All nine fields are true FP facts, so the bundle is satisfiable. None is stronger than the source's claim, and nothing the §2.7–§2.12 candidates need is missing (they are covered or derivable). | Degenerate inputs checked: `xgcdStr` at modulus 0 (`ZMod 0 = ℤ`, inverse `= Int.sign`, `val = natAbs`, computable); `divModStr` at `b = 0` (`a/0 = 0`, `a % 0 = a` truncated to `|b|` bits); `modExpStr` at modulus 0 (`a^x` truncated to `|N|` bits = `a^x mod 2^{|N|}`, polynomial by repeated squaring); empty numerals; leading zeros. Every output length is affine in the input length. Derivable ops: equality (`le` both ways), Bézout's second coefficient (`(g − a·x)/b`), width normalization (FP take/drop). Squaring and roots mod `p ≡ 3 (mod 4)`, CRT, `gcd(x − z, N)`, safe-prime and generator tests all use listed fields. The bundle has no instance, so candidate theorems remain conditional (DESIGN §8 Q1). | None. |
| 12 | note | all four files (policy hygiene) | (a) `@[simp]` without a recorded gate approval (policy §1: "None carries `@[simp]` unless a gate approves it"). (b) Machine-layer API is declared in a crypto file (policy §1 "Helpers"). (c) Disclosed private copies (policy §1 "Duplication": needs a ledger entry). (d) `Collections.lean` is about 975 lines, near the 1000-line cap. | (a) `prod_inLen`, `prod_outLen`, `eval_yaoBlocks`, `eval_yaoRounds`, `PermFamily.toFunFamily_f`, `NUPPT.coins_withIndexParam`, `liftSucc_zero`, `liftSucc_succ`, `length_natToList`, `mulStr_pairEncode`, `addStr_pairEncode`, `subStr_pairEncode`, `length_sizeStr`, `leStr_pairEncode`, `modExpStr_pairEncode`. (b) `NUPPT.withIndexParam`, `NUPPT.length_runAt_le`, `NUPPT.runLenPoly`, `eval_runLenPoly`, `length_runAt_le_runLenPoly` live in `Asymptotic/Collections.lean`. (c) `ptc_comp` ("private copy of the helper of Closure"), `decodeFin_eq_some_iff` ("private copy, cf. `inverter_eq_some_iff`"). | Confirm the approvals or drop the attributes. Move the `NUPPT` lemmas to `Complexity/Randomized/`. Add the two copies to the duplication ledger. Split `Collections.lean` if it grows. |
| 13 | note | `audits/pass-shelat/Checks.lean` (non-vacuity coverage for this pack) | The pack's non-vacuity prints are `not_strongOneWay_id` and `StrongOneWay.weak`. Nothing shows that `WorstCaseOneWay`, `WeakOneWay` or `Collection.OneWay` exclude a trivially invertible instance, and no string-level TDP check exists (see #1). | Missing: `¬ (ofString id var).WorstCaseOneWay`, `¬ (ofString id var).WeakOneWay`, `¬ ((ofString id var).toCollection …).OneWay`. Each is a few lines from the existing `not_strongOneWay_id` machinery. | Add them with their `#print axioms` lines. |
| 14 | note | run-3a repair "canonical default pair" (P3-1, `factoringCollection`) | Not checkable from the bundle: the pack asks for it, but `Candidates/Factoring.lean` is not in the bundle. | `DESIGN.md` §2.10 says `factoringCollection` discharges `sample_spec` "by the canonical default pair". The code is not attached. | Attach `Factoring.lean` (or the relevant excerpt), or move this check to the pack that owns that file. If #1 is fixed by canonical decoding, re-check that the default pair is the canonical encoding. |

## 2. Answers to the specific questions

**Q1. One-wayness (Defs 26.1, 27.3, 28.4).**

- *Strong one-wayness* (`FunFamily.StrongOneWay`).
  - **Yes, this is the source's notion, with one declared difference.** For every `A : NUPPT`
    (non-uniform: advice of polynomial length indexed by `n`; time polynomial in the whole input), the
    probability over uniform `x ∈ {0,1}^{inLen n}` and `A`'s coins at `n` that `A(1^n, f_n(x))` returns
    the `inLen(n)`-bit encoding of a preimage is negligible in `n`.
  - The difference (D5) is that a preimage must have the domain's length; the text's
    `f(A(1^n, y)) = y` accepts any length.
  - For length-regular `f` with non-constant output length the two coincide: the output length then
    determines the input length.
  - With constant output length neither notion can hold: an advice table of polynomial size inverts.
- *Weak one-wayness.* **Same quantifier order** as Def 28.4: `∃ q ∀ A ∃ n₀ ∀ n ≥ n₀, invProbAt ≤ 1 − 1/q(n)`.
  - The guard `∀ n, 0 < q.eval n` is harmless. A text polynomial is eventually positive, and the bound
    is monotone in `q`, so `q` can be enlarged to a positive `PolyExpr`.
  - The guard also prevents the `1 − 1/0 = 1` vacuity.
- *Worst case.* The headline `1^n` form `WorstCaseOneWay`, the literal `WorstCaseOneWayLit` and both
  bridges are right.
  - `toLit` holds always: a literal inverter is a `1^n` inverter re-parametrized by `outLen`.
  - `toParam` holds for injective `outLen`. For `PolyExpr` lengths, injective is the same as
    non-constant, because the coefficients are nonnegative. So `toParam` covers every family where the
    literal form is not degenerate.
  - The literal form's vacuity is broader than the deviation text says (#9).
- *Length-changing functions.*
  - Shrinking and expanding `outLen` are expressible.
  - Output length that varies within one parameter is not: it must be padded, and `ofString`'s padding
    is lossy (#2).
  - Constant output length makes the literal form vacuous (#9) and the `1^n` forms false.
  - Collections avoid the issue: `f_i` returns raw strings, and `owfFamily` pads injectively.

**Q2. Amplification (Thms 35.1, 35.2; Claim 38.2).**

- *Theorem 35.1* (`weak_to_strong : WeakOneWay 𝓕 → ∃ q, StrongOneWay (𝓕.prod q)`) is the source's
  statement, and stronger: it holds for any input length, not only `inLen = n`.
  - The direct product has input length `q(n)·inLen(n)`. For `inLen = var` and the proof's
    `q = yaoBlocks q_w = 2n·q_w(n)` this is `2n²·q_w(n) = n·m(n)`, as in the text.
  - The adversary receives `1^n` rather than `1^{n·m(n)}`. This is benign (#8).
- *Theorem 35.2* (`strong_prod_two`) is `g(x, y) = (f(x), f(y))` as two blocks of input length
  `2·inLen(n)`, at parameter `n`. This is faithful.
- *Claim 38.2* (`claim_38_2`) keeps the text's `m = 2nq(n)`.
  - It uses `T(n) + 1 = 2n·m(n)·n^c + 1` rounds, against † the text's `2nm²p(n)`, and Garg's
    threshold `μ₀/(2m)`, against the text's `1/(2m²p(n))`. Both changes are declared in the docstring.
  - Its conclusion is strengthened by the margin `(T + 1)·2^{−n}`, which pays for the rejection-sampled
    position.
  - The arithmetic checks out. It needs `2e^{−n} < 1/n^c` and `e^{−n} + (T + 1)2^{−n} < 1/(2q(n))`
    eventually; both hold because `T` is polynomial.
  - Not yet in the DESIGN §5 register (#8).

**Q3. Collections (Def 41.1, Thm 42.2).**

- *The three conditions.*
  - (1) `gen` is a uniform `NUPPT` and the index is the first component of `Gen(1^n)`. Faithful.
  - (2) `sample` is a uniform `NUPPT`. Membership is `sample_spec`; uniformity is `SampleClose` with a
    negligible `δ`. The deviation from exact uniformity is declared (D10) and benign. It is checked
    worst-case over the generated indices, which is stronger than average.
  - (3) `eval` is a deterministic FP function correct on canonical encodings and on sampled strings.
    That is weaker than the text's "computes `f_i(x)` for `x ∈ D_i`" whenever `decD` is lenient (#1).
- *`sample_spec`.* It is right as far as it goes: membership for every generated index and every coin
  string, plus `eval` correct on the sampled string. It is enough for 42.2 (⇒), which is now proved and
  axiom-clean. It is **not enough** for the consumers that compute on the strings a collection produces
  (#1).
- *Theorem 42.2* is stated in both directions at existence strength:
  - (⇐) `exists_collection_oneWay`. The explicit form even gives an exact sampler, `δ = 0`.
  - (⇒) `exists_strongOneWay`. Its hypothesis allows an approximate sampler, so it is stronger than the
    text.
  - Together they give `(∃ G, G.OneWay) ↔ (∃ 𝓕, 𝓕.StrongOneWay)`, in the campaign's notion of OWF (#8).

**Q4. One-way and trapdoor permutations (Defs 55.1, 56.1).**

- *Permutation.* `perm i : D i ≃ D i` with `f i = encD i ∘ perm i`, so `R_i = D_i`. This is faithful;
  quantifying over every index string makes it stronger than the text, harmlessly (#5).
- *Trapdoor.* The inverter correctly receives `1^n` and the trapdoor `t = pairSndD (Gen(1^n; r))`.
  - `inv_spec` holds for every generated `(i, t)`, i.e. every `Gen` coin string, for every `y ∈ D_i`,
    and for every `Inv` coin string.
  - But it holds **only up to decoding**, so "inverts" does not reach the string level (#1).
- *P3-5.* Benign, and the classes coincide (#6).

**Q5. `Permutations.lean`.** Yes: the parameters are as stated and the failure probability is
`≤ n·2^{−n}`, which is negligible (#10). The Fisher–Yates bijection and the conditional uniformity are
proved, axiom-clean.

**Q6. `Candidates/Arithmetic.lean`.** A reasonable stand-in for D11 and Remark 33.2 (†). No field is
stronger than the source's claim or false, and no needed operation is missing (#11).

## 3. Adversarial instantiations

1. **A function family one-way for a degenerate reason. Attempted; no defect in the headline notions.**
   - *Empty domain:* impossible. `Fin 0 → Bool` is a singleton, and `D i` is `Inhabited`. Note that
     `uprob` on an empty type would be `0`, so this matters: an empty domain would make any family
     look one-way.
   - *Singleton domain at `inLen n = 0`:* inverted by the machine that outputs the unique (empty)
     string. In general a machine knows the required output length `inLen(n)` because it reads `1^n`.
   - *Outputs that leak the input* (`f_n(x) = x ++ g(x)`): inverted by the prefix machine.
     `not_strongOneWay_id` is this instance.
   - *Constant output length:* inverted non-uniformly by an advice table of size `2^c·inLen(n)`.
   - The only degenerate one-wayness found is in the literal worst-case form, and it is wider than
     declared: `f n b = b xor [n odd]` is `WorstCaseOneWayLit` but not `WorstCaseOneWay` (#9).
2. **A collection whose sampler is not efficient. Cannot be built.** `gen`, `sample` and `inv` are
   uniform `NUPPT`s by type, so the only non-effective fields are `D`, `decD`, `f` and `perm`. I tried
   to exploit them:
   - *A sparse or hard-to-hit decoder* does not make a non-OWF one-way. For constant `f`, the adversary
     runs the public sampler and returns its (decodable) output.
   - *A relabelling decoder* (`encD = π⁻¹` for a one-way permutation `π`) makes the abstract `f` the
     identity, yet the collection is one-way. But the string-level function is `w ↦ π(w)`, which is
     genuinely one-way, so the hardness notion is sound.
   - The abstract/encoding split bites only where consumers compute on strings, which leads to #1.
3. **A trapdoor that does not invert. Defect found (#1).** The prefix-bit collection of #1 satisfies
   every field of `TrapdoorCollection`, including `inv_spec`. Two things still go wrong: `eval` on
   `Inv`'s output need not return `y`, and the hard-core evaluator disagrees between sampled strings
   and `Inv`'s outputs, so TDP encryption always decrypts wrongly.
4. **(Extra) A junk index without a permutation domain.** `eval ⟨i, w⟩ = true :: w` on unparseable `i`
   makes `PermCollection` uninstantiable without re-encoding (#5).

## 4. Run-3a repairs in scope (pack P3)

| Repair | Check | Holds? |
|---|---|---|
| P3-1 `Collection.sample_spec` | The field is present with the stated shape: generated indices, every coin string, decode plus `eval`. `evalSampled` is the field read through `index`. `owfFamily_strongOneWay` has no `hG`. | **Yes.** Sufficient for 42.2 (⇒); insufficient for string-level consumers. #1 is a new gap, not a re-report. |
| P3-1 Theorem 42.2 (⇒) | `Collection.OneWay.exists_strongOneWay` is proved from `owfFamily_strongOneWay`. Both are axiom-clean (`axioms.log`), with no `sorry` in the file. | **Yes.** |
| P3-2 `1^n` form of Def 26.1 | `WorstCaseOneWay` is the `1^n` form, `WorstCaseOneWayLit` the literal one. `toLit` and `toParam (hinj)` are proved and axiom-clean. Deviation 16 is on the docstring. | **Yes.** Deviation wording: #9. |
| P3-1 canonical default pair (`factoringCollection`) | The file is not in the bundle. | **Not checkable** (#14). |
| P3-5 (no index to `Inv`) | Deviation lines are present on `TrapdoorCollection` and in the module docstring. | **Yes, and benign** (#6). |

## 5. Inventory check (`inventory-ch2.md` rows in this pack's files)

| Item | Lean | Faithful? |
|---|---|---|
| Def-26.1 | `WorstCaseOneWay` (headline, `1^n`), `WorstCaseOneWayLit` (literal), `toLit`, `toParam` | Yes, with the declared D5 deviation. Literal-form vacuity is broader than declared (#9). |
| Def-27.3 | `FunFamily.StrongOneWay`, `invProbAt` | Yes (typed preimage, D5). |
| Def-28.4 | `FunFamily.WeakOneWay` | Yes; the quantifier order is the source's. |
| Thm-35.1 | `weak_to_strong`, `FunFamily.prod`, `yaoBlocks` | Yes, more general in `inLen`. Parameter-`n` reading benign (#8). |
| Thm-35.2 | `strong_prod_two` | Yes, at parameter `n` (#8). |
| Claim-38.2 | `claim_38_2`, `yaoRounds` | Yes, with the declared change of `T` and threshold; † the source wording was not verified. |
| Rem-33.2 | `ArithmeticFP.prime` | Yes, as an explicit hypothesis (D11). |
| Def-41.1 | `Collection`, `SampleClose`, `Collection.invProbAt`, `Collection.OneWay` | (1), (2) and (4) yes, with (2) approximate (D10). (3) is only partly faithful (#1). |
| Thm-42.2 | `toCollection_oneWay` / `exists_collection_oneWay` (⇐); `owfFamily_strongOneWay` / `exists_strongOneWay` (⇒) | Yes, at existence strength, in the campaign's OWF notion (#8). |
| Def-55.1 | `PermCollection`, `PermCollection.OneWay` | Yes; stronger at junk indices (#5). |
| Def-56.1 | `TrapdoorCollection`, `TrapdoorCollection.OneWay` | Partly: decode level only (#1). P3-5 is benign (#6). |
| Def-78.3 (collection form; in `Collections.lean`) | `Collection.HardCore` | Hardness yes. The evaluator `H` is constrained only on canonical encodings (#1); attribution (#3). |

## 6. Definitions restated (before reading their docstrings), with any daylight

**`OneWay.lean`**
- `FunFamily`: two polynomial lengths `ℓᵢ, ℓₒ` and, for each `n`, a function `{0,1}^{ℓᵢ(n)} → {0,1}^{ℓₒ(n)}`. No daylight.
- `Easy`: some polynomial-time string function maps `⟨1^n, x⟩` to `f_n(x)`. No daylight; the deterministic evaluator is the declared deviation 3.
- `invProbAt A n`: the probability, over uniform `x` and `A`'s coins at `n`, that `A` on `⟨1^n, f_n(x)⟩` outputs exactly an `ℓᵢ(n)`-bit preimage of `f_n(x)`. No daylight.
- `StrongOneWay` / `WeakOneWay`: easy, and (negligible / eventually `≤ 1 − 1/q(n)` for a fixed positive polynomial `q`) for every `A`. No daylight.
- `WorstCaseOneWay`: easy, and no `A` that for every `n` and `x` returns a preimage with probability 1 on `⟨1^n, f_n(x)⟩`. `WorstCaseOneWayLit`: the same, with `A` activated at parameter `|f_n(x)|` on `f_n(x)` alone. Daylight: the deviation wording (#9).
- `strOutLen f n = |f(0^n)|`; `LengthRegular f p`: `|f(x)| = p(|x|)` for all `x`. No daylight.
- `ofString f p`: input length `n`, output the first `p(n)` bits of `f(x)`, padded with `0`. Daylight with the D5, module and `FunFamily` docstrings (#2); none with `ofString`'s own.
- `blocks q ℓ`: the bijection `{0,1}^{qℓ} ≅ ({0,1}^ℓ)^q`, block `i` at positions `ℓi … ℓi+ℓ−1`. No daylight (consistent with `finProdFinEquiv`).
- `prod 𝓕 q`: lengths `q·ℓᵢ` and `q·ℓₒ`, with `f_n` applied blockwise. No daylight.
- `yaoBlocks q = 2n·q(n)`; `yaoRounds q c = 2n·m(n)·n^c`. No daylight.
- `PermFamily`: a permutation of `{0,1}^n` for each `n`, with no efficiency demanded of the inverse. `toFunFamily` and `OneWayPermutation` (strong one-wayness of that family). No daylight in content; attribution #3.

**`Collections.lean`**
- `Collection`:
  - For each string index, a finite inhabited set with an injective encoding and a left-inverse decoder. The decoder may be lenient and non-effective.
  - An abstract `f_i` to strings.
  - Uniform PPTs `Gen` and `Sample`, and a polynomial-time evaluator correct on canonical encodings.
  - Sampler outputs at generated indices always decode, and the evaluator is right on them.
  - No daylight with the docstring; daylight with the source: #1.
- `index` / `trap`: the components of `Gen(1^n)`. No daylight.
- `SampleClose δ`: at every generated index, the decoded sampler output is within statistical distance `δ(n)` of uniform. No daylight.
- `invProbAt`: average over `Gen`'s coins of `Pr[x ← D_i, coins : A(1^n, ⟨i, f_i(x)⟩)` decodes to a preimage`]`. No daylight.
- `OneWay`: `SampleClose` with negligible `δ`, and negligible `invProbAt` for every `A`. No daylight.
- `HardCore h`: `h_i(x)` is polynomial-time from `⟨i, encD x⟩`, and every `A` predicts it from `⟨i, f_i(x)⟩` with advantage at most negligible over `1/2`. Daylight: "from `⟨i, x⟩`" holds only for canonical encodings (#1).
- `PermCollection`: plus a permutation `perm_i` with `f_i = encD ∘ perm_i`, at every index (#5).
- `TrapdoorCollection`: plus a uniform PPT `Inv` that on `⟨t, encD y⟩` returns, for every coin string, a string decoding to `perm_i⁻¹(y)`. The docstring says "decodes to"; no daylight with it, daylight with the source (#1).
- `PermCollection.OneWay`, `TrapdoorCollection.OneWay`: the underlying `Collection.OneWay`. No daylight.
- `NUPPT.withIndexParam A`: `A` run on `⟨1^n, y⟩` in place of `y`. No daylight.
- `toCollection`: indices `1^n`, domains `{0,1}^{inLen n}` (canonical `decodeFin`), sampler returning its coins, evaluator `F` on `⟨1^{|i|}, x⟩`. No daylight.
- `splitCoins a b`: `{0,1}^{a+b} ≅ {0,1}^a × {0,1}^b`. No daylight.
- `owfRaw`: `⟨i, eval⟨i, Sample(i; r₂)⟩⟩` with `i = Gen(1^n; r₁)`. No daylight.
- `OutLenBound L`: `L(n)` strictly bounds that length. No daylight.
- `EvalSampled`: `sample_spec` read through `index`. No daylight.
- `owfFamily L`: input = the coins of `Gen` and `Sample`; output = `owfRaw ++ [1]`, zero-padded to `L(n)` bits. No daylight.
- `NUPPT.runLenPoly`: a polynomial bounding output length from the time bound. No daylight.

**`Permutations.lean`**
- `fisherYates n c`: the product of transpositions `(i, i + c_i mod (n − i))`. No daylight.
- `permFromCoins n k T`: each position `i` draws its offset in `[0, n − i)` by rejection with `T` trials of `k` bits; `none` if any position fails. No daylight.
- `liftSucc`: a permutation of `Fin n` lifted to `Fin (n+1)` fixing `0`. No daylight.
- `fyOffsets`: the in-range offset tuples. No daylight.
- `permBits n = size n`; `permTrials n = 2n²`. Daylight: the "`≤ 2n`" claim at `n = 0` (#10).

**`Arithmetic.lean`**
- `natToBits k N` / `natToList k N`: the `k` low-order binary digits of `N`, most significant bit first. No daylight.
- `mulStr`, `addStr`, `subStr`, `divModStr`, `xgcdStr`, `modExpStr`, `leStr`, `sizeStr`, `primeStr`: the named arithmetic on `listToNat`-read numerals at the stated widths. No daylight.
- `ArithmeticFP`: each of the nine is polynomial-time. No daylight.

## 7. Theorems: is each statement what its docstring claims?

**`OneWay.lean`.**
- `invProbAt_nonneg`, `invProbAt_le_one`, `invProbAt_eq_uprob`: yes (the last is the experiment unfolded to `runAt … = List.ofFn x'`).
- `WorstCaseOneWay.toLit`: yes, always.
- `WorstCaseOneWayLit.toParam`: yes, under `Function.Injective outLen.eval`, as claimed.
- `ofFn_ofString_f`: yes, under `LengthRegular`.
- `ofString_id_f`, `blocks_symm_apply`, `ofFn_blocks_symm`, `prod_inLen`, `prod_outLen`, `prod_f`: yes.
- `invProbAt_prod_eq`: yes (the bridge to the concrete `prodFun`).
- `Easy.prod`: yes.
- `eval_yaoBlocks`, `eval_yaoRounds`, `yaoBlocks_pos` (needs `n ≥ 1` and positive `q`, as stated): yes.
- `OneWay.invProb_prodFun_le_yaoTry`: yes (fixed position, `[Nonempty α]`).
- `claim_38_2`: yes. Strict inequality with the margin; for all `n ≥ n₀` and all `f`, `B` at `Type`.
- `weak_to_strong`: yes. The polynomial is existential, and the docstring says the proof's choice is `2nq(n)`.
- `strong_prod_two`: yes.
- `StrongOneWay.weak`: yes, with `q = 2`.
- `not_strongOneWay_id`: yes.
- `PermFamily.toFunFamily_f`: yes.

**`Collections.lean`.**
- `encD_injective`, `invProbAt_nonneg`, `invProbAt_le_one`, `PermCollection.f_injective`: yes.
- `TrapdoorCollection.inv_preimage`: yes as stated. It is decode-level only, so "wins the inversion game" is true for the game as defined but not at the string level (#1).
- `coins_withIndexParam`, `withIndexParam_runAt`: yes.
- `toCollection_index`, `toCollection_sample`, `toCollection_sampleClose` (`δ = 0`), `toCollection_invProbAt`: yes.
- `StrongOneWay.toCollection_oneWay`, `exists_collection_oneWay`: yes.
- `ofFn_splitCoins_fst`, `ofFn_splitCoins_snd`, `ofFn_splitCoins_symm`, `evalSampled`, `ofFn_padFin_of_le`, `padFin_append_true_injective` (strings shorter than `ℓ`): yes.
- `NUPPT.length_runAt_le`: yes. Raw-input length `8n + 14 + 4|y| + 2|α| + |r|` checked from `|⟨a, b⟩| = 2|a| + 2 + |b|`.
- `eval_runLenPoly`, `length_runAt_le_runLenPoly`, `exists_outLenBound`: yes.
- `OneWay.owfFamily_strongOneWay`: the statement is yes; the sketch has drifted (#4).
- `OneWay.exists_strongOneWay`: yes.

**`Permutations.lean`.**
- `permFromCoins_eq_none_iff`, the `liftSucc` lemmas, `decomposeFin_symm_eq`, `foldr_swap_succ`: yes.
- `fisherYates_succ` (in-range offsets), `fisherYates_injOn`, `mem_fyOffsets`, `prod_sub_eq_factorial`, `card_fyOffsets`, `exists_fyOffsets`: yes.
- `uprob_pi_forall_dep`, `permFromCoins_eq_some_iff`: yes.
- `permFromCoins_uniform_of_some` (`n ≤ 2^k`): yes.
- `uprob_permFromCoins_none_le` (`n(1 − 1/2^k)^T`; the corrected frozen bound, declared): yes.
- `statClose_permFromCoins`, `le_two_pow_permBits`, `permBits_le`: yes.
- `two_pow_permBits_le` (`0 < n`): yes.
- `uprob_permFromCoins_none_le_two_pow`, `statClose_permFromCoins_two_pow`: yes.

**`Arithmetic.lean`.** All yes:
- `length_natToList`, `natToList_zero`, `natToBits_succ_castSucc`, `natToBits_succ_last`;
- `listToNat_natToList_eq_mod`, `listToNat_natToList`, `bitsToNat_natToBits`, `natToBits_bitsToNat`, `natToBits_injOn`, `natToList_injOn`, `listToNat_lt_two_pow`;
- the `*_pairEncode` unfoldings, `mulStr_natToList`, `length_sizeStr`;
- `listToNat_add_lt_two_pow` (both-empty case `0 < 1` included), `listToNat_addStr`, `listToNat_subStr`;
- `primeStr_eq`, `val_units_pow` (`[NeZero M]`), `mul_lt_two_pow_add`.

## 8. Attestations (consistency check, not re-executed)

- **Replay.** `replay.log` lists 65 modules, all `rc=0 errors=0`. The `sorry=` counts total 17, as attested, and all of them are outside the four audited files: `ClassP/TimeConstructible` 2, `Build/Loop` 5, `TuringMachine/Build/Primitives` 3, `Build/Wrappers` 2, `Composition` 3, `Encoding` 1, `Simulation` 1. The four files print `sorry=0`, which agrees with `admissions.txt` being empty.
- **Axioms.** `axioms.log` has 21 prints, all `propext, Classical.choice, Quot.sound`. They include `weak_to_strong`, `strong_prod_two`, `claim_38_2`, both directions of 42.2, `toLit`/`toParam` and `permFromCoins_uniform_of_some` (sorried in run 3, now filled). None of the 17 closure sorries is therefore reachable from these headlines.
- **Lint.** `lint.log` reports 0 findings in 4 files. Mechanical presence checks do not cover the hygiene points of #12.
