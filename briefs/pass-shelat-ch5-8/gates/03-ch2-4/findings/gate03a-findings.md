# Gate 03a: external statement audit findings

**Pack:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` ([PS10] ch. 2–4, machines and probability)
**Commit audited:** `a3c5fa8b72e50939822f22364647dc844a3914a0` (as reproduced in the bundle)
**Files under audit:** `Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `Cryptography/Asymptotic/{Adversary, Sampling, Ensembles, SamplingFinDist}.lean`; context: `Cryptography/Foundations/Negligible.lean`
**Auditor:** external, statement gate. I read the trusted surface (definitions, statements, docstrings, proof sketches) and did not review tactic scripts.

## Source access

`Pass–Shelat.pdf` was not in the upload: only the bundle arrived. The session's network policy also blocks the Cornell host that serves the notes. I therefore compared the code against the source text as quoted in `inventory-ch2.md` and `inventory-ch3.md` (built from `blueprint/src/references/pass-shelat-2010-ch{2,3}.raw.md`) and in the docstrings, and checked those quotations against my own knowledge of [PS10] §2.1, Def 27.2 and §3.1. No finding below depends on wording that is quoted nowhere in the bundle. Where a point depends on exact source wording, the row says so. The maintainer should re-check rows marked **(src)** against the PDF.

## Verdict

**0 blockers · 0 majors · 13 minors · 13 notes.** By the pack's closing rule (0 blockers, 0 majors) the pack may close. This is not a blanket approval:

- Fix minors 1–4 before ch. 5–8 statements are frozen against this interface.
- Minor 1 needs a downstream check that this pack cannot perform. If any ch. 5–8 statement uses `NUPPT.Computes` without `Uniform` to mean "efficiently computable", that statement is wrong, and it is a blocker in the pack that owns it.

The run-3a repairs that touch these files (P2-1, P2-2, and D11's `iterateFind`) hold. Details are at the end.

---

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `PPT.lean` · `NUPPT.Computes` (and the module docstring, D3) | The docstrings equate `Computes` with [PS10, Def 24.6], which is about randomized (uniform) algorithms. Nothing requires `A.Uniform`, so `∃ A : NUPPT, A.Computes f` does not mean "a PPT computes `f`". It holds for uncomputable `f`. The pack lists `NUPPT.Computes` as cited by ch. 5–8. | Let `h : ℕ → Bool` be arbitrary, for example the halting set, and let `f w := [h \|pairFstD w\|]`. Take `A := ofPolyTime polyTimeComputable_inAdvice (.const 0) (.const 1) (fun n => [h n]) _`. Then `A.runAt n y r = inAdvice (layout 1^n y [h n] r) = [h n] = f ⟨1^n, y⟩` for every `n, y, r`, so `A.Computes f`. The file's own converse `Computes.polyTimeComputable` correctly needs `hA : A.Uniform`. | (a) Add a docstring sentence: "for [PS10, Def 24.6] proper, `A` must be `Uniform`; on a non-uniform `A` this is the advice analogue." (b) Add `PPT.Computes` (or `NUPPT.ComputesUniformly := Uniform ∧ Computes`) as the citable form. (c) Grep ch. 5–8 for `.Computes`. Any occurrence not paired with `Uniform` is a blocker in that pack. |
| 2 | minor | `Ensembles.lean` · `Ensemble.Indist.copies` | The hypotheses `hX : X.Samplable` and `hY : Y.Samplable` are not needed against non-uniform distinguishers. Because `Samplable` demands an exact dyadic law, the lemma cannot be applied to non-dyadic ensembles, although the `Ensemble` type admits them and the conclusion holds for them. The pack's Q4 asks whether any hypothesis is stronger than the uses can meet; this one is. | The `Ensemble` type allows any finite seed type: `σ n := Fin 3` with `X n i := enc₂ i` has probabilities 1/3, so `¬ X.Samplable`, since `padFin ∘ S` on `2^{s(n)}` seeds has dyadic laws. Every ideal law of D6/D10 (uniform on `Z_q`, `Π_n`, `S_n`) is likewise excluded. **Non-uniform hybrid (no sampling):** pick the hybrid index `k` with gap `≥ ε/t`. The gap is `\|E_w a(w)\| ≤ max_w \|a(w)\|` over the other `t−1` coordinates `w`, so some fixed `w*` keeps it. Hard-wire `(k, w*)` as advice, of length `≤ t(n)·ℓ(n)+O(t(n))`, using `exists_withAdvice` and a splice. | Prove `Indist.copies` without `hX hY` via the advice hybrid, or add `Indist.copies'` without them. Keep the samplable version only if a uniform reduction is needed somewhere; state that in its docstring. |
| 3 | minor | `Closure.lean` · `NUPPT.exists_comp` (catalogue scope) | Claim-26.3(a)/(b) closure is only partly expressed. `pre` sees only `y` and `post` sees only `A`'s output; neither sees `1^n`. So n-dependent pre- and post-processing (pad or cut to `ℓ'(n)`, slice `p(n)` bits, plant at an n-dependent position) is not in the catalogue. Every such reduction must be rebuilt from `ofPolyTime` on the raw layout. | The run-3 note cited in `Indist.push`'s sketch ("P2-4: `NUPPT.exists_comp` sees only `y`") hit exactly this. Lemma 71.5's reduction had to be a private `EnsembleLemmas.exists_pushRed` (outside the pack) instead of a catalogue instance. Ch. 5–8 reductions that pad or cut at `p(n)` will repeat the work. | Add `exists_compParam : ∃ B, B.coins = A.coins ∧ B.advice = A.advice ∧ ∀ n y r, B.runAtL n y r = post ⟨1^n, A.runAtL n (pre ⟨1^n, y⟩) r⟩`, built from `polyTimeComputable_layout` and `inParam`. |
| 4 | minor | `Repetition.lean` · `polyTimeComputable_stateFind` (private); `polyTimeComputable_iterate` | The form a reduction actually needs for "q(n) fresh-coin calls, first success" is private. The public lemmas are deficient in two ways. (i) `horbit` must hold for **every** string `x`, so a step that stores outputs needs a length guard. (ii) Rounds are counted in `\|x\|`, the whole input word, not in the parameter `n`, so exactly `T(n)` rounds needs a counter threaded through the state. Policy §1, "Hosts come first", forbids a private host variant. | `stateFind` packages exactly (i) and (ii): `gstep`, a retained input, and a first round `N x ≤ R\|x\|`. All six derived lemmas use it. A ch. 5–8 consumer must re-derive it, which is the third private variant the policy warns against. | Make `polyTimeComputable_stateFind` public, in the shared `Build/StateLoop` layer per the host registry, with a docstring. Optionally add a corollary that reads the round count from an embedded `1^n`. |
| 5 | minor | `NonUniform.lean` · `NUPPT.polyTimeComputable_runAtL` (and module docstring) | Wrong strength. The docstring concludes "i.e. each `A_n` is a polynomial-size machine" (Def 26.8, sequence form, `\|A_i\| < d(i)`). The statement is `∀ n, PolyTimeComputable (…)`, where the machine and the constants may depend on `n`. It bounds neither description size nor a time polynomial that is uniform in `n`. | The statement holds for any family of per-`n` functions that are each polynomial-time computable on their own. The proof composes with `polyTimeComputable_const (A.advice n)`, whose machine grows with `n`. It would hold equally if the advice were `2^n` bits long. | Weaken the docstring to "each activation is a polynomial-time function of `(y, r)`; constants may depend on `n`". Or state a uniform version: `∃ C c, ∀ n, …` with a size bound `≤ C(n+1)^c`. |
| 6 | minor **(src)** | `Ensembles.lean` · `pairwise_sampling_ineq` | The declared deviation does not state its cost. For bits with mean `p > √3/2`, the formal bound `1/(4ε²m)` is weaker than the text's `(1−p²)/(mε²)`. Bits satisfy the text's hypothesis `\|X_i\| ≤ 1`, so the text's bound applies to them. | At `p = 1` the text bounds the event by `0` and the formal statement by `1/(4ε²m)`. In general `1/4 > 1 − p²` iff `p > √3/2`. The source wording is as quoted in the deviation note. | State the cost in the deviation note, or prove the variance form `p(1−p)/(mε²)`, which implies both bounds. |
| 7 | minor | `Ensembles.lean` · `Ensemble` (structure docstring) | The deviation is misstated. The docstring says "every distribution is dyadic (a pushforward of uniform seeds)". Seeds range over arbitrary finite nonempty types, so laws are rational, not necessarily dyadic. Only `Samplable` ensembles are dyadic, as the module docstring and DESIGN D6/§5.5 say correctly. | Take `σ n := Fin 3`: the law has mass 1/3. This also matters for minor 2. | Reword: "a pushforward of the uniform distribution on a finite nonempty seed set (rational probabilities); efficiently samplable ensembles are dyadic". |
| 8 | minor | `Adversary.lean` · private `forall_of_uprob_eq_one`; `Ensembles.lean` · private `Ensemble.blocks` | Duplicated material (policy §1, Duplication). The first copy is unforced: the original `HardcoreBit.forall_of_uprob_eq_one` is public, and `HardcoreBit/Basic.lean` is already imported by `Sampling.lean` in this pack. `Ensemble.blocks` copies `FunFamily.blocks`. A third copy, `EnsembleLemmas.blocks`, lives in a file outside the pack, and `Indist.copies` uses it interchangeably by definitional equality. | Both docstrings disclose the copy. The bundle shows no duplication-ledger entry or human approval for them; the only ledger item mentioned is DL-4. Policy: "every instance of duplicated proved material must be human-approved"; undisclosed duplication is a freeze violation. | Delete the `forall_of_uprob_eq_one` copy and import the original. For `blocks`, keep one public copy in a shared low-level file and use it from `OneWay`, `Ensembles` and `EnsemblesLemmas`, or ledger the copies with explicit human acceptance. |
| 9 | minor | `Closure.lean` · `exists_reparam`, `exists_withAdvice`, `exists_split`, `exists_seq` | Attribution (policy §2). The brackets `[Claim-26.3, implicit]`, `[Claim-26.3 (d)]` and so on read as a [PS10] item number, but Claim-26.3 is an inventory id. The book has no Claim 26.3; in §2.2 the third item is Def 27.3. The inventory's own convention for unnumbered items would be `Claim-26.a`. | `Primitives.lean` does it right: "[PS10, §2.1, implicit; inventory Claim-26.3(c)]". | Use "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" throughout. Optionally rename the inventory id to `Claim-26.a`. |
| 10 | minor | `Sampling.lean` · `StatClose` | Attribution. `StatClose` is the source's statistical distance (ε-closeness), but its docstring cites only §2.4.2 and §4.3. The definition itself is [PS10, Def 181.1], which `SamplingFinDist.lean` cites for the same notion. | See the docstrings of `StatClose` and `statClose_iff_epsClose_map`. | Add "[PS10, Def 181.1], sup-over-test-sets form" to `StatClose`. |
| 11 | minor | `PPT.lean` `coins_/adv_/advice_ofPolyTime`, `coins_ofPolyTimeUniform`; `Closure.lean` `in{Param,Arg,Advice,Coins}_layout`, `pair{Fst,Snd}D_combineAdvice`; `Sampling.lean` `bitsEquiv_val` | Policy §1 (user, 2026-10-16): no lemma carries `@[simp]` unless a gate approves it. The frozen design approves `@[simp]` only for `PolyExpr.eval_{const,var,add,mul,pow}`. These eleven attributes have no recorded approval. | DESIGN §2.1 lists `@[simp]` only on `eval_*`; §2.2 and §2.5 list none. | Approve them at this gate explicitly, or drop the attributes. |
| 12 | minor | `Ensembles.lean` · imports; `negligible_zero` | Policy §1. The file imports the facade `TCSlib.Complexity.Randomized`, which pulls 65 unrelated randomized-complexity modules (BPL, UPath, ZPP, and others) into the crypto closure. The pack's closure of 323 modules includes them. Separately, the general helper `negligible_zero` is defined here instead of in `Foundations/Negligible.lean` (policy §1, Helpers). | The replay log lists `TCSlib/Complexity/Randomized` plus `Adleman`, `BPLInP*`, `UPath*`, `ZPP*` and others in the pack closure. The other pack files import precise modules. | Import `Randomized.{PPT, Closure, Repetition}` precisely. Move `negligible_zero` to `Negligible.lean`, after checking that no copy already exists in the Garg layer. |
| 13 | minor | `SamplingFinDist.lean` · file header | Two of these were reported by lint and are already scheduled: the missing `set_option maxHeartbeats 0` and the missing `## Main definitions`. Lint does not check the third: the copyright block has no `Authors:` line, unlike every other file in the pack (policy §1 asks for a Mathlib-style block). | See `evidence/a/lint.log` and the file header. | Add all three. For `## Main definitions`, write "None", as `Primitives.lean` does. |
| 14 | note | `Ensembles.lean` · `Ensemble.IndistLit.toIndist` | The injectivity hypothesis `hℓ` can be dropped. A `PolyExpr` evaluation is either constant or strictly increasing, since all coefficients are natural numbers. For constant `ℓ ≡ L`, `IndistLit ⇒ Indist` holds too: the `2^L` point tests `t ↦ [t = t₀]` are advice-free literal distinguishers. Their negligibility makes `TV(X_n, Y_n) ≤ Σ_{t₀} \|X_n(t₀) − Y_n(t₀)\|` negligible, and that bounds every distinguisher. So D5's "`D` receives `1^n`" costs nothing for ensembles. | — | Optionally drop `hℓ`, or say in the docstring that the two forms coincide for every `PolyExpr ℓ`. |
| 15 | note | `Adversary.lean` · `NUPPT.inverter`, `invProbOpt` (D5: a wrong-length output counts as failure) | The deviation is benign for typed families, and for string functions whose output length determines `n`: length-regular functions with injective `outLen`. With constant `outLen`, neither notion is satisfiable, since a random guess succeeds with probability at least `2^{-c}`. Otherwise the typed experiment is strictly weaker than [PS10, Def 27.3], which accepts preimages of any length. The cost is not stated anywhere. | Let `g` be a length-preserving OWF. Define `f(0^k‖w) := w` for `\|w\| = k`, and `f(x) := g(x)` otherwise. Typed inversion at length `L` succeeds with probability at most `Adv_g + 2^{-L/2}`, because a special preimage has the wrong length. [PS10]'s `A(1^n, y) := 0^{\|y\|}‖y` inverts with probability 1, because every nonempty `y` has the special preimage `0^{\|y\|}‖y`. | State the cost where string functions enter the typed world, at `FunFamily.ofString` in `OneWay.lean` (outside this pack), and point to it from the `inverter` docstring. |
| 16 | note | `Ensembles.lean` · `hybrid_lemma` | All hybrids must share one seed type `σ` (`X : ℕ → σ → γ`). Consumers with hybrids of different seed shapes must first embed them into a common product seed. This is harmless and stronger than the text's bound (`ε/m` over `m` steps). | — | Optionally mention this in the docstring. |
| 17 | note | `PolyExpr.lean` · `PolyExpr` | The cost of D9 is not stated. A `PolyExpr` is a polynomial with natural coefficients, so `Ensemble`, `FunFamily` and coin lengths cannot be `n − 1`, `⌊n/2⌋`, `C(n,2)` or `⌈log n⌉`. Consumers must pad or reparametrize, using `exists_reparam_advice` as the escape hatch (run-3 P4-1's `glHalf` is an example). No current statement is wrong. | — | Add one sentence on the cost to the `PolyExpr` docstring. |
| 18 | note | `Ensembles.lean` · `Ensemble`, `Ensemble.push` | Ensembles have fixed length (as the text's Def 69.4 requires), so variable-length distributions such as ciphertexts, views and transcripts cannot be ensembles. `push` pads with `false` and truncates, which is lossy for variable-length `M`: `[1]` and `[1,0]` both pad to `[1,0,…]`. Later experiments restate indistinguishability inline over `List Bool` (`distinguisherL`) and lose `trans`, `push`, `copies` and `prediction_lemma`. | See DESIGN §2.13 and the inline `SingleMessageSecure` and `Secure` forms. | Say in the `push` docstring that padding is lossy. Consider an `EnsembleL` (samplers into `List Bool`) carrying the same lemma suite before ch. 5–8 re-derive it. |
| 19 | note | evidence/attestations | Interface lemmas lack axiom prints. The 41 prints omit `statClose_iff_epsClose_map` (the new DL-4 bridge), `computes_iff_uprob`, `Computes.polyTimeComputable`, `exists_uniform_computes`, `uniform_samplable`, `indist_iff_exists_negligible`, `invProbOpt_le_invProb`, `invProbOpt_some`, `statClose_firstHit`, `pushesUniform_of_card_fiber` and `pairwise_sampling_ineq`. The closure carries 22 `sorry` warnings outside the pack: TimeConstructible 2, Build/Loop 5, Build/Primitives 3, RecordTable 4, Wrappers 2, Composition 3, Encoding 1, Simulation 1. The 40 clean prints show those sorries do not reach the printed headlines; the unprinted lemmas are unverified. | See `axioms.log` and `replay.log`. | Append these prints to `Checks.lean` and attach the log. |
| 20 | note | `NonUniform.lean` · `NUPPT.decides_of_decidesWithAdviceInTime` (sorry) | The statement is true: clock `M` (via `timed_universal`, or a product counter) and use `α` as advice at parameter `\|x\|` with zero coins. It is correctly labelled optional, and no printed headline depends on it. Two loose ends: (i) D11's named admissions list `NUPPT.ofPartial`, which does not exist, while the `sorry` sits in this bridge; (ii) DESIGN §8 Q5 (optional modules out of the core) is still listed as open, and no ruling is recorded. | See DESIGN D11 and §8 Q5, and `admissions.txt`. | Record the ruling on Q5 and name this declaration in D11's admission list. Alternatively, move the `sorry` into a stated `NUPPT.ofPartial`. |
| 21 | note | `Ensembles.lean`, `PPT.lean` · non-vacuity | Only the "class not empty" sanity checks exist (`NUPPT.nonempty`, `PPT.nonempty`, `Indist.refl`, `uniform_samplable`). Nothing shows `Indist` can fail. If the distinguisher semantics were broken so that every advantage was 0, `refl` would not catch it. | — | Add `¬ (uniform ℓ).Indist (zeros ℓ)` for non-constant `ℓ` (distinguisher: output `[t₀ = false]` on the first bit) to `Checks.lean`. |
| 22 | note | scope · `Asymptotic/EnsemblesLemmas.lean` | `Ensembles.lean` imports this file, which holds public declarations: `exists_pushRed`, `exists_copiesRed`, `exists_negRed`, `coinsEquiv`, `blocks` and `acceptProb_*`. It is neither under audit nor listed as context. That is fine while these are used only inside proofs. Any ch. 5–8 citation of them would be unaudited trusted surface. | — | List the file as context in the pack. Either make its contents `private` or internal, or audit any declaration a later chapter cites. |
| 23 | note | inventories; pack Q1 | Several "Formal" sketches in the inventories are superseded by DESIGN D3–D6. The pack's Q1 repeats the stale description ("advice length `Cα(n+1)^cα`, runs on `⟨⟨x, α\|x\|⟩, r⟩`"). The code has `\|advice n\| ≤ adv.eval n` and the layout `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. | The stale sketches are inventory-ch2 Def-23.4 (coins `Cr(\|x\|+1)^cr`, run on `⟨x, r⟩`) and Def-26.8, and inventory-ch3 Machine-NUPPT, Def-69.3 (`seedLen`/`outLen : ℕ → ℕ`) and Def-69.4 (no `1^n`). | Add a "superseded by DESIGN D3–D6" banner to those rows. |
| 24 | note | docstring precision | (a) The interdefinability paragraph of the `PPT.lean` module docstring, item (i), says "see `exists_reparam_advice` … with `φ := length`". That is ill-typed (`φ : ℕ → ℕ`) and unnecessary, since (i) holds by definition (`runLit`). (b) `Indist.push`'s sketch cites "run-3 audit note P2-4", which `run3-audit-summary.md` does not contain; its P2 section lists P2-1 and P2-2 only. | — | Fix (a). Point (b) at the record that holds P2-4, or drop the reference. |
| 25 | note | process | The source PDF was not received, so rows marked **(src)** and the "source fidelity" verdicts below rely on the inventories' quotations. | — | Re-check minor 6 against PDF p. 189. Spot-check Defs 23.5, 24.6, 26.8, 69.4 and Lemmas 71.5, 71.6, 73.8 against book pp. 23–26 and 69–73. |
| 26 | note | `Sampling.lean` · `StatClose` on an empty seed type | `uprob` is 0 on an empty type, so the "law" of an empty-seeded sampler is the zero measure. `StatClose X Y 0` then fails whenever `Y` has seeds. The docstring is silent on this. It is harmless: every use has nonempty seeds, `Ensemble.nonempty` holds, and `SamplingFinDist` assumes `[Nonempty σ]`. | — | Optionally add a sentence to the docstring. |

---

## Answers to the pack's specific questions

**Q1. The machine model.**
- **Defs 23.4, 23.5 and 26.8.** `NUPPT` and `PPT` capture them with the declared D3/D4 deviations:
  - coins are an explicit input of `coins.eval n` bits;
  - time is measured over every input, including every coin string, which is the worst-case reading of 23.5, and is total;
  - advice satisfies `|advice n| ≤ adv.eval n`.
  The pack's description ("length `Cα(n+1)^cα`, layout `⟨⟨x, α|x|⟩, r⟩`") is stale; see note 23.
- **What the time bound is polynomial in.** The length of the raw machine input `⟨⟨⟨1^n, y⟩, α⟩, r⟩`, which is `8n + 4|y| + 2|α| + |r| + 14`. Since `|α| ≤ adv(n)` and `|r| = coins(n)`, the bound is polynomial in `n + |y|`.
- **`NUPPT.Uniform`.** Yes, it is the uniform class: `advice n = []` for every `n` leaves a single machine on `⟨1^n, y⟩` with `coins(n)` coins.
- **Whether the D4 reading loses anything.** It uses the text's own "alternatively" formulation. The machine-sequence equivalence (Rem-26.2) is deferred and declared. Indexing by `1^n` instead of `|x|` costs nothing:
  - where the text itself gives `1^n` (Def 27.3, 28.4, 75.2, 78.3), the two coincide;
  - for ensembles the two forms coincide for every `PolyExpr ℓ` (note 14).
  The one overstatement in this area is the "polynomial-size `A_n`" sanity lemma (minor 5).

**Q2. Computing with probability 1 (Def 24.6).** Yes, `Computes` requires the same output `f⟨1^n, y⟩` for every coin string at every `n` and `y`. `computes_iff_uprob` proves that this equals probability one over the finite coin space (inventory C7). That is the source's notion for a uniform `A`. With advice it is the non-uniform analogue, so the uniformity caveat is required (minor 1).

**Q3. Polynomials.** `PolyExpr` covers every bound the pack's statements need. Non-polynomial lengths go through `exists_reparam_advice`, with a `PolyExpr` majorant, or through padding; the cost is unstated (note 17). I found no statement that says "for some polynomial" where the source quantifies differently:
- `Ensemble ℓ` and `Indist` fix `ℓ` as a parameter, as Def 69.4 does;
- `Samplable` and `not_negligible_iff_exists_polyExpr` use `∃` where the text does;
- `Indist.copies` uses `∀ t`.

**Q4. The closure calculus.**
- **Pairing, hard-wiring and fresh coin segments.** `exists_withAdvice`, `exists_split`, `exists_seq` and `exists_reparam_advice` state exactly what those reductions need, and preserve uniformity where they claim to.
- **Pre- and post-composition.** `exists_comp` is n-blind (minor 3).
- **Polynomially many calls with fresh coins.** This exists only at the FP level (`iterateFind`, `iterate`, `iterateEmit`, plus `pairTakePoly` and `pairDropPoly`), and the convenient guarded state-loop form is private (minor 4).
- **Hypotheses the uses cannot meet.** `Indist.copies`' samplability (minor 2). Also `horbit` over all strings, which is meetable only with a guard (minor 4).

**Q5. Statistical closeness.**
- **Is `StatClose` the source's notion?** `StatClose X Y δ` says that the sup over all test predicates of `|Pr[T(X)] − Pr[T(Y)]|` is at most `δ`. For nonempty seeds that is total-variation distance at most `δ`, which is the source's statistical distance.
- **Preservation.** It is preserved by `map` (data processing), `prod` (with `δ + δ'`), `trans`, `symm`, `mono`, seed bijections and `PushesUniform` precomposition. It bounds `distAdv` and any experiment with auxiliary coins. All of these are proved.
- **The bridge.** `statClose_iff_epsClose_map` makes it exactly `EpsClose` on a finite sample space (`Fintype γ`, `DecidableEq γ`, nonempty seeds). `EpsClose` is not in the bundle. From the proof term it must unfold to "every Boolean test has advantage at most `δ`", which is the test form of Def 181.1.
- **Caveat.** For `γ = List Bool` (views, ciphertexts) only `StatClose` applies, so a consumer must map into a finite type before using the bridge.

**Q6. Ensembles and indistinguishability.**
- **Quantifier order.** `Indist` is `∀ D, Negligible(adv)`. `indist_iff_exists_negligible` proves it equivalent to the text's `∀ D ∃ ε negligible ∀ n, adv < ε(n)`, so the order is the source's.
- **Advice.** Advice is per parameter `n`, not per `|t|`. This is equivalent for every `PolyExpr ℓ` (note 14).
- **Lemma 71.6.** The hybrid lemma is at least as strong as the text's: `ε/m` over `m` steps.
- **Lemma 71.5.** `Indist.push` is at the right strength for all non-uniform `M` and all `ℓ'`, including an `M` that receives `1^n`, which makes the statement stronger. Padding is lossy for variable-length `M` (note 18).
- **Lemma 73.8.** `prediction_lemma` has a strict, infinitely-often conclusion, which is stronger than the text's `≥`.

**Q7. Adversaries.** The interface matches how [PS10] quantifies:
- `inverter` is `A(1^n, y)` (Defs 27.3, 28.4);
- `inverterLit` is `A_{|y|}(y)` (Def 26.1);
- `distinguisher` and `predictor` test for the verdict `[true]` (Defs 69.4, 75.2, 78.3);
- `invProbOpt` is the Def 27.3 experiment.

The one semantic deviation is D5's wrong-length-is-failure, which is benign under the conditions in note 15.

**Q8. The one admission.** `decides_of_decidesWithAdviceInTime` is true as stated: clock `M`, then use `α` as advice at `|x|` with zero coins. It is labelled optional, and none of the 40 printed headlines depends on it. Its bookkeeping in D11 and §8 Q5 needs tidying (note 20).

---

## Inventory rows located in this pack's files

| Inventory row | Formal declaration(s) | Faithful? |
|---|---|---|
| ch2 Def-23.4 (PPT) | `NUPPT`, `NUPPT.Uniform`, `PPT` | Yes, with declared D3 deviations (coins as an input of length `coins(n)`, totality, `1^n` indexing). The inventory's "Formal" sketch is stale (note 23). |
| ch2 Def-23.5 (worst-case time) | `NUPPT.halts`, `timeBound` | Yes. The bound holds for every input, including every coin string, and is measured in the raw input length. |
| ch2 Def-24.6 (computes w.p. 1) | `NUPPT.Computes`, `computes_iff_uprob`, `Computes.polyTimeComputable`, `exists_uniform_computes` | Yes for uniform `A`. A caveat is needed for non-uniform `A` (minor 1). |
| ch2 Rem-24.2 (majority amplification; deferred) | — | Absent, consistent with "deferred". (`polyTimeComputable_majority` is the machine part only.) |
| ch2 Def-26.8 (nuPPT) | `NUPPT` (advice form), `runLit`, `NonUniform.lean` lemmas | Yes for the advice form. The sequence form is not formalized (declared). The sanity lemma overstates (minor 5). |
| ch2 Rem-26.2 (equivalence of forms; deferred) | — | Absent, consistent. |
| ch2 Claim-26.3 (closure calculus) | `Closure.lean` catalogue, `Primitives.lean`, `Repetition.lean` | Faithful as stated. Coverage gaps are in minors 3 and 4. |
| ch2 Def-192.12 (BPP; deferred) | — | Absent, consistent. |
| ch2 C4 (first hit uniform; now `Sampling.lean`) | `firstHit_uniform_of_some`, `uprob_firstHit_none`, `statClose_firstHit`, `rejectionSample_*`, `statClose_getD_of_uniform_of_some` | Yes. |
| ch2 C5 (equal fibres; now `Sampling.lean`) | `pushesUniform_of_card_fiber`, `card_fiber_eq_of_le`, `pushesUniform_of_card_fiber_le` | Yes. |
| ch2 C7 (`uprob = 1 ↔ ∀`; now `Adversary.lean`) | `computes_iff_uprob` (private helper copy, minor 8) | Yes. |
| ch2 C10 (statistical switch; now `Sampling.lean`) | `StatClose.abs_uprob_sub_le_prod`, `distAdv_le_of_statClose` | Yes. |
| ch2 Def-27.2 (negligible; context) | `Negligible`, `not_negligible_iff` | Equivalent on `[0,1]`-valued functions (shift `c` for strict `<` and `n ≥ n₀`). Not audited here. |
| ch3 Def-69.3 (ensemble) | `Ensemble` | Yes: nonempty finite seeds, rational laws. The docstring misstates "dyadic" (minor 7). |
| ch3 Def-69.4 (≈) | `Ensemble.Indist`, `IndistLit`, `Distinguishes`, `DistinguishesWith`, `indist_iff_exists_negligible` | Yes. The two forms are equivalent for every `PolyExpr ℓ` (note 14). |
| ch3 Lem-71.5 (closure) | `Ensemble.push`, `Indist.push` | Yes, and stronger (`M` gets `1^n`). Padding is lossy (note 18). |
| ch3 Lem-71.6 (hybrid) | `hybrid_lemma`, `Indist.trans` | Yes, at least as strong as the text. |
| ch3 Rem-72.7 (pseudometric; optional) | — | Not formalized as a named lemma. `Indist.trans` covers the asymptotic triangle. Consistent with "optional". |
| ch3 Claim-72.a (long chain; optional) | — | Absent, consistent. |
| ch3 Ex-72.b (`x⊕y`; optional) | — | Absent, consistent. It would follow from `Indist.push` plus `Samplable Y`. |
| ch3 Claim-73.a (predicting ⇒ distinguishing) | `predict_eq` | Yes: the exact identity in both directions. |
| ch3 Lem-73.8 (prediction lemma) | `prediction_lemma` | Yes: pigeonhole route, no advice, strict conclusion. |
| ch3 Claim-73.b (infinitely often ⇔ non-negligible) | `not_negligible_iff_exists_polyExpr` | Yes, with `p : PolyExpr`, `p > 0`. |
| ch3 Def-74.1 (pseudorandom; inventory said `Pseudorandom.lean`) | `Ensemble.Pseudorandom` | Yes. |
| ch3 Ineq-189.a (pairwise sampling; inventory said "exists") | `pairwise_sampling_ineq` | Faithful for bits only, and weaker than the text for `p > √3/2` (minor 6, **(src)**). |
| ch3 labels Machine-PPT, Machine-NUPPT, Machine-Closure, Machine-Repetition, Machine-Loop, Machine-Primitives, Ensemble-D6 | as above | Covered, except "inner product mod 2" of Machine-Primitives, which is not in this pack's files. |

---

## Definitions: my restatement, and any difference from the docstring

| Declaration | Restatement (from the Lean body) | Difference from docstring |
|---|---|---|
| `PolyExpr`, `eval`, `subst`, `normal` | Syntax trees over ℕ-constants, one variable, `+`, `×` and ℕ-powers; structural evaluation; substitution of an expression for the variable; `C·(n+1)^c`. | None. The cost is unstated (note 17). |
| `NUPPT` | A finite binary TM that halts on every input `z` within `Ct(\|z\|+1)^ct` steps, plus a coin-count polynomial, an advice-bound polynomial, and any advice function `ℕ → {0,1}*` within that bound. | None in the code. The pack's description is stale (note 23). |
| `timeBound`, `coinLen`, `adviceLen` | The evident projections. | None. |
| `output z` | Run `M` from `z` for exactly `timeBound \|z\|` steps and read the output tape. | None. |
| `advInput n y`, `Coins n` | `⟨1^n, y⟩`; `{0,1}^{coins(n)}`. | None. |
| `runAt`, `runAtL`, `runLit` | `output ⟨⟨⟨1^n, y⟩, α(n)⟩, r⟩`, with typed coins, with list coins of any length, and at `n = \|y\|` respectively. | `runAtL` accepts coins of any length, not only "the right length". This is harmless and the closure lemmas use it. |
| `Uniform`, `PPT` | Advice is empty at every `n`; `PPT` is the subtype of such machines. | None. |
| `Computes f` | `∀ n y r, runAt n y r = f⟨1^n, y⟩`. | Minor 1: the docstring identifies it with Def 24.6 without the uniformity caveat. |
| `ofPolyTime`, `ofPolyTimeUniform` | The machine chosen from a `PolyTimeComputable f` witness, with the given coins and advice (empty advice and `adv = 0` for the uniform version). | None. |
| `layout`, `inParam`, `inArg`, `inAdvice`, `inCoins` | `⟨⟨⟨u, y⟩, α⟩, r⟩` and its total projections. | None. |
| `combineAdvice a b` | `[]` if both are empty, otherwise `⟨a, b⟩`. | None. |
| `guardedStep`, `LoopInv` | Advance the orbit point only if the new point has length at most `P\|x\|`; the state carries `x` and a short orbit point. | None. |
| `PPT.toNUPPT`, `PPT.ofPolyTime` | Subtype API. | None. |
| `decodeFin`, `padFin` | Exact-length decode, failing otherwise; pad with `false` or truncate. | None. |
| `inverter`, `inverterLit` | `decodeFin ℓ (A(1^n, y))`; the same at parameter `m = \|y\|`. | None. The cost of D5 is in note 15. |
| `distinguisher`, `distinguisherL`, `predictor` | Accept iff the output is exactly `[true]`; untyped sample; predictor equals distinguisher. | None. |
| `invProbOpt` | `Pr_{x,r}[A(f x, r) = some x' with f x' = f x]`. | None. |
| `StatClose` | For every predicate `T`, `\|Pr_s T(X s) − Pr_t T(Y t)\| ≤ δ`. | Silent on empty seed types (note 26). The source tag is missing (minor 10). |
| `bitsToNat`, `bitsEquiv` | MSB-first binary value, and the bijection to `Fin 2^k`. | None. |
| `uniformFromBits`, `rejectionSample`, `firstHit` | One trial accepted iff below `m`; the first accepted trial out of `T`; the first draw satisfying `E`. | None. |
| `Ensemble`, `uniform` | For each `n`, a finite nonempty seed type and a map to `{0,1}^{ℓ(n)}`; the uniform ensemble is the identity on `{0,1}^{ℓ(n)}`. | "Dyadic" is wrong; the laws are rational (minor 7). |
| `Samplable` | A PTC `S` such that `padFin ℓ(n) (S⟨1^n, r⟩)` for `r` uniform on `{0,1}^{s(n)}` has exactly the law of `X_n`. | None. |
| `Indist`, `IndistLit`, `Pseudorandom` | Every `NUPPT` has negligible advantage at parameter `n` (respectively at parameter `ℓ(n)`); indistinguishable from uniform. | None. |
| `push`, `copies` | Seeds are `X`'s seeds × `M`'s coins, and the output is padded or truncated to `ℓ'(n)`; `t(n)` independent seeds, concatenated. | None in the code. Padding is lossy (note 18). |
| `Distinguishes`, `DistinguishesWith` | `ε < distAdv`; the same for all `n`. | None. Whether the inequality is strict should be checked against p. 70 **(src)**. |
| `mixEnsemble` | `(b, X^b_n(seed_b))`, drawing both seeds. | None. |

---

## Theorems: does each statement match its docstring?

Unless a row says otherwise, the statement says what the docstring claims.

- **PolyExpr.**
  - The equation lemmas `eval_const`, `eval_var`, `eval_add`, `eval_mul`, `eval_pow` and `eval_normal` are `rfl` facts. `eval_subst`, `subst_var` and `eval_mono` match their docstrings.
  - `eval_le`, `polyBound_eval` and `exists_normal_ge` give a normal-form majorant.
  - `polyTimeComputable_unaryNormal` restates `polyUnary`.
- **PPT.**
  - `output_spec`, `computesFunInTime`, `polyTimeComputable_output`, `output_eq_of_computesInTime` (determinism) and `output_length_le` match.
  - `length_advInput` (`2n+2+|y|`) and the `runAt_eq` and `Computes.runAt_eq` unfoldings match.
  - The `ofPolyTime` and `ofPolyTimeUniform` equation, coin, advice and output lemmas match.
  - `exists_uniform_computes` is the non-vacuity of Def 24.6. `NUPPT.nonempty` and `PPT.nonempty` hold, but they are trivial non-vacuity (note 21).
- **Primitives.**
  - `computesFunInTime_pairSplitAt` gives `⟨u,b⟩ ↦ ⟨b.take|u|, b.drop|u|⟩` in time `c(n+1)`, with `[]` on malformed input.
  - `computesFunInTime_unaryMul` gives `⟨u,v⟩ ↦ 1^{|u||v|}` in time `c(n+1)^2`.
  - `polyTimeComputable_unaryPoly` gives `x ↦ 1^{p(|x|)}` for every `p`.
  - `pairTakePoly` and `pairDropPoly` match.
- **Closure.**
  - The projection-of-layout lemmas, `runAtL_eq_output_layout`, the PTC projection and assembly lemmas, and the `combineAdvice` decoding, `nil` and length lemmas match.
  - `exists_comp`, `exists_reparam` (uniformity preserved), `exists_reparam_advice` (extra coins unread), `exists_withAdvice`, `exists_split` and `exists_seq` (uniform if both are) each state exactly the functional identity and coin or advice equations in their docstrings. The scope gap is minor 3.
  - `Computes.polyTimeComputable` correctly assumes `Uniform`.
- **Repetition.**
  - `loopInv_init`, `loopInv_guardedStep`, `iterate_guardedStep_eq` and `acc_guardedStep_eq` match.
  - `polyTimeComputable_iterateFind` returns `out` of the first accepted `g^[i] x`, for `i ≤ R|x|` (that is, `R|x|+1` attempts including `i = 0`), and `[]` otherwise.
  - `iterate` gives exactly `R|x|` rounds, counted in `|x|` (minor 4).
  - `iterateEmit` makes `R|x|+1` emissions, with `emit x` first.
  - `majority` is a strict majority, so ties give `false`. `pairXor` truncates to the shorter component. `pairEq` is exact equality. `blockMap` makes `⌊|snd|/b⌋` blocks, and none when `b = 0`.
- **NonUniform.**
  - `runLit_eq_runAt` and `runLit_eq_runAtL` match.
  - The `Uniform.*` lemmas, `ofPolyTime_uniform`, `uniform_iff`, `runLit_ofPolyTimeUniform`, `PPT.uniform` and `PPT.toNUPPT_ofPolyTime` match.
  - `polyTimeComputable_runAtL` is weaker than its docstring claims (minor 5).
  - `decides_of_decidesWithAdviceInTime` is true but sorried, and optional (note 20).
- **Adversary.**
  - `decodeFin_ofFn`, `length_eq_of_decodeFin_eq_some`, `padFin_ofFn`, `inverterLit_eq`, `distinguisher_eq`, `predictor_eq` and `inverter_eq_some_iff` match.
  - `invProbOpt_le_invProb` holds: a default only helps.
  - `invProbOpt_some`, `invProbOpt_nonneg`, `invProbOpt_le_one` and `computes_iff_uprob` match.
- **Sampling.**
  - The `StatClose` API matches: `abs_uprob_sub_le`, `uprob_le_add`, `nonneg`, `refl`, `symm`, `mono`, `trans`, `map`, `comp_equiv_left` and `comp_equiv_right`, `statClose_of_pushesUniform`, `comp_pushesUniform`, `abs_uprob_sub_le_prod`, `distAdv_le_of_statClose` and `prod` (`δ+δ'`).
  - The fibre lemmas `pushesUniform_of_card_fiber`, `card_fiber_eq_of_le`, `_le` and `uprob_comp_eq_sum_fiber` match.
  - The bit lemmas `bitsToNat_lt`, `bitsToNat_injective`, `bitsEquiv_val`, `uprob_bitsToNat_lt` (`m/2^k`), `uniformFromBits_eq_*` and `uprob_uniformFromBits_*` (`1/2^k` and `1 − m/2^k`) match.
  - The first-hit lemmas `firstHit_eq_none_iff`, `firstHit_eq_some_imp`, `uprob_firstHit_none` (`(1−Pr E)^T`), `firstHit_uniform_of_some` and `statClose_firstHit` match.
  - The rejection lemmas `rejectionSample_eq_none_iff`, `map_rejectionSample_eq_firstHit`, `rejectionSample_uniform_of_some`, `uprob_rejectionSample_none`, `uprob_rejectionSample_none_le_half_pow` (assuming `2^k ≤ 2m`) and `statClose_rejectionSample` match.
  - `one_sub_inv_pow_le_half` (`m ≥ 1`) and `statClose_getD_of_uniform_of_some` match.
  - The `hm : 0 < m` hypotheses of `rejectionSample_uniform_of_some` and `uprob_rejectionSample_none` are unused. Both statements hold at `m = 0`, so they are merely weaker than necessary; this is harmless.
- **Ensembles.**
  - `copies_X` gives bit `i` as bit `i mod ℓ` of copy `i / ℓ`. `uniform_samplable` and `negligible_zero` match.
  - `indist_iff_exists_negligible` and `not_negligible_iff_exists_polyExpr` match.
  - `Indist.refl`, `symm`, `trans`, `toLit` and `push` match.
  - `IndistLit.toIndist` matches but is stronger than needed (note 14). `hybrid_lemma` (note 16) and `Indist.copies` (minor 2) match.
  - `predict_eq` (with nonempty instances) and `prediction_lemma` match. `pairwise_sampling_ineq` matches, with the deviation cost in minor 6.
- **SamplingFinDist.** `uprob_comp_eq_probTrue_map` and `statClose_iff_epsClose_map` match (see Q5).

---

## Adversarial instantiations attempted

1. **A degenerate machine with advice.** `ofPolyTime inAdvice` with advice `[h n]` for an arbitrary `h` satisfies `Computes` for an uncomputable function. That is acceptable for a non-uniform class, but it shows that the existential use as "efficiently computable" is wrong (minor 1).

   With the same advice idea, `polyTimeComputable_runAtL` would still hold if the advice were exponentially long, so it does not express the polynomial-size half of Def 26.8 (minor 5).

   Two further degenerate machines are harmless:
   - `Ct = 0` gives a machine that halts at once with output `[]`. Its advantage is always 0 and `decodeFin` succeeds only at `ℓ = 0`.
   - `coins = const 0` gives a singleton coin type. `uprob` and `computes_iff_uprob` remain correct there.
2. **Degenerate ensembles.**
   - `ℓ = const 0`: everything is indistinguishable, which is correct.
   - An empty seed type is excluded by `Ensemble.nonempty`, which is the run-3 P2-2 repair, and that repair holds.
   - A non-dyadic seed type, `σ n = Fin 3`, is admitted by `Ensemble` but is never `Samplable`. That makes the docstring's "dyadic" wrong (minor 7) and blocks `Indist.copies` where it should apply (minor 2).
   - At `t(n) = 0`, `Indist.copies` is handled correctly: both products are one-point distributions.
3. **A distinguisher exploiting the advice indexing.** For constant `ℓ`, a `1^n`-indexed distinguisher can change its advice with `n` while the sample length stays fixed. `IndistLit` and `Indist` still coincide, because both are equivalent to "total-variation distance is negligible" (note 14), so the `1^n` advice buys nothing for ensembles.

   Buying running time by declaring more coins is still polynomial (`coins : PolyExpr`).
4. **An inverter exploiting typed lengths.** For a string function whose output length does not determine `n`, an inverter that outputs a preimage of another length succeeds in [PS10]'s experiment but fails in the typed one (note 15). This is benign for length-regular `f` with injective or constant `outLen`.
5. **Boundary parameters.**
   - `n = 0`: `advInput 0 y = ⟨[], y⟩`, and negligibility ignores finitely many `n`.
   - The empty coin string `Fin 0 → Bool` is a singleton; `uprob` is well defined on it.
   - Length-0 advice is uniform, and `combineAdvice [] [] = []`.
   - `T = 0` trials gives `statClose_firstHit` with `δ = 1`, which is trivial and correct.
   - `k = 0` bits forces `m ≤ 1`.
   - `b(n) = 0` gives `blockMap = []`.
   - `R = 0` gives a single test of `x` in `iterateFind`.
   - `hybrid_lemma` correctly excludes `m = 0`.
   - `not_negligible_iff_exists_polyExpr` requires `p > 0` everywhere.

   No statement fails at any of these boundaries.
6. **A loop step that grows its state.** A repetition step that stores each adversary output makes `|g^[i] x|` grow without bound (`poly^R`) on arbitrary strings. So `horbit`, which quantifies over every string, can be met only by a length guard. That guard exists only in the private `stateFind` (minor 4).

---

## Run-3a repairs that touch this pack

- **P2-1 (permutation sampler moved out; general lemmas added to `Sampling.lean`): holds.**
  - `statClose_getD_of_uniform_of_some`, `StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` are present.
  - Their statements match DESIGN §2.7, and their prints are clean.
  - `Sampling.lean` has 0 `sorry`.
- **P2-2 (`Ensemble.nonempty`; `prediction_lemma` and `predict_eq` shapes): holds.**
  - The field is present and registered as an instance.
  - `prediction_lemma` has exactly the frozen shape of DESIGN §2.11, without `h₀ h₁`.
  - `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁] [Nonempty ρ]`, and the counterexample those instances guard against is real: on an empty type the left side is 0 and the right side is ½.
- **D11 (`polyTimeComputable_iterateFind` closed): holds.**
  - Its print and those of the six derived lemmas are clean.
  - Its statement matches DESIGN §2.6, including the length-guard repair, which moved into the proof and left the statement unchanged.

Nothing that run 3a resolved is re-reported here. The "P2-4" reference in `Indist.push` cannot be traced to the summary (note 24).

## Attestations checked against `evidence/a/`

- **Elaboration: consistent.** 323 modules, all `rc=0`. The sorry warnings total 22, all outside the pack except `NonUniform` (1).
- **Axioms: consistent.** There are 41 prints, 40 of them clean; the only `sorryAx` is `decides_of_decidesWithAdviceInTime`. Coverage gaps are in note 19.
- **Admissions: consistent.** There is 1 admission, `NonUniform.lean:153`.
- **Lint: consistent.** There are 2 findings, both in `SamplingFinDist.lean`. The missing `Authors:` line is a third defect that lint does not check (minor 13).
