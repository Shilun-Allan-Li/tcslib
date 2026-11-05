## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack-r2.md =====

# Gate 03a ([PS10] ch. 2–4, probabilistic machines, closure, ensembles: the interface), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e28773ef3bda6f7b4b112ec1657427bfef01e374` (the branch after #201 and #203 merged; its Lean files are #203's head `f29be161`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 0 majors, 13 minors and 13 notes**; after the review, 2 majors (#4 and #8 raised: duplication rooted in private helpers) (`gate03a-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03a repair commit (G3-7 (a): `negligible_zero` moved; precise imports; minors and notes), merged in #201; gate 03 clean-up part 1, #203 (item H: `NUPPT.exists_compParam`, the fix for #3 that #201 missed; item D: `polyTimeComputable_stateFind` public; item G: `Repetition.lean`'s construction prose). The full delta is `evidence-r2/03a/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03a-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03a-review.md` (in the bundle).
- **The deliverable:** **`gate03a-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Context** (#22): `Asymptotic/EnsemblesLemmas.lean` is context for this pack; pack 03i audits it.
- **Q1** (#23): the stale question is answered by the inventory banners ("superseded by DESIGN
  D3–D6", `inventory-ch2.md`, `inventory-ch3.md`).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03a-r1.md` (the
   findings, grouped as the review grouped them, and the review's missed items `M1`, …) say
   whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR (clean-up part 2,
     after #195), and the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03a/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement, rename and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** No public statement of this pack changes (statement-text comparison against round 1). `negligible_zero` moved from `Ensembles.lean` to `Negligible.lean` (both in this pack), name and statement unchanged. `Repetition.lean`'s proofs were re-pointed to `Build/`'s new reading lemmas (#203); its 03l-related prose is re-audited in gate 03l round 2 as well.
- **New public declarations:**
- `NUPPT.exists_compParam` (`Closure.lean`): closure under polynomial-time pre- and
  post-processing that see `1^n`; `exists_comp` is re-derived as its special case;
- `polyTimeComputable_stateFind` (`Repetition.lean`): made public (statement unchanged).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03a-findings.md`, `review/gate03a-review.md`, `resolutions-03a-r1.md`, `evidence-r2/03a/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles, SamplingFinDist}.lean`, `TCSlib/Cryptography/Foundations/Negligible.lean` |
| Context | `03a-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; clean-up part 2 (after #195) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/a2/` in the bundle)

### Attestation results at `e28773ef3bda6f7b4b112ec1657427bfef01e374` (evidence under `evidence/a2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 64 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   18 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 164 prints of every public theorem and lemma in this pack's files:
   163 use only the standard axioms, and 1 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 11 files.

The one `sorryAx` print and the one admission are the same declaration,
`NUPPT.decides_of_decidesWithAdviceInTime` (`NonUniform.lean:160`): the optional admission recorded
in DESIGN D11 (round 1, note 20).

The replay is the 416-module replay at `af91d53a`, overlaid by the re-check at #201's head
(`evidence-repairs/03ac/replay.log`) and by #203's builds and re-check
(`evidence-repairs/03l-cleanup1/`); each line of `replay.log` is the newest check of its module,
and the Lean files at the pin equal #203's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row (or row group): `<row>: fixed / recorded / scheduled / not resolved —
<reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03a-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03a-review.md =====

# Gate 03a: review of the external auditor's findings

## Summary

- **Verdicts on the 26 items:** 23 true, 3 partly true (#2, #20, #22), 0 false. Two true items are understated: #4 and #8 are wider than the auditor saw, and #12 is too (see "Missed").
- **Severity changes:** four.
  - #4 (private state-loop host) goes from minor to **major**.
  - #8 (duplication) goes from minor to **major**. Policy §1 makes accumulated duplication a major until the user ledgers it, and the copies rooted in 03a's `private` helpers number about twenty: `ptc_comp` ×6, the `blocks` bijection ×6 plus one inverse, `stateFind` ×4, and `abs_uexp_sub_le`, `negligible_zero` and `forall_of_uprob_eq_one` ×2 each.
  - #2 goes from minor to note: the cited source assumes samplability, and the lemma has no consumer.
  - #6 goes from minor to note: the cost is benign and the lemma has no consumer.
  - New tally: **0 blockers, 2 majors, 9 minors, 15 notes.**
- **Closing the gate.** The pack does not close as filed. It closes once #4 and #8 are fixed, or once the user ledgers them (ruling R2). Every other fix is a docstring edit, an import or header edit, or additive API.
- **Fixes that need a ruling:** three.
  - **R1:** the unapproved `@[simp]` attributes. One cross-pack ruling would also settle 03b #12a, 03c #11 and 03e #17.
  - **R2:** the duplication ledger, and when the cleanup happens.
  - **R3:** where `negligible_zero` lives. DESIGN D2 freezes the Garg files.
- **Downstream check for #1: clean.** The auditor asked for this check. No ch. 5–8 file uses `NUPPT.Computes` (0 hits in the five worktrees). In ch. 2–4 it appears only in an `iff` (`computes_iff_uprob`) and in two statements that also assume `Uniform`.
- **Ripple:**
  - **Statements.** No recommended fix changes the meaning of any statement, in ch. 2–4 or ch. 5–8.
  - **Ch. 5–8.** No statement uses an affected declaration: `Ensemble`, `Indist`, `Samplable`, `StatClose` and `Computes` all have 0 uses. The only ch. 5–8 text to touch is two proof sketches in `wt-s2b/.../Games/Efficiency.lean` that cite `GGMRed.stateLoopFun`, which R2-A would re-point. If R1 went the other way (drop the attributes), 62 non-`only` `simp` calls in ch. 5–8 would need a replay.
- **Dispatch:**
  - **Now:** 03f1, 03f2 and 03l are unaffected. 03g can go now with a one-line erratum.
  - **Wait, under R2-A:** 03h, 03i and 03k. Their public statements name copies that the dedup PR deletes or renames.
  - **Under R2-B:** 03h, 03i and 03k go now, with an erratum.
  - **Still held by F-1, as before:** 03d and 03j. Neither depends on 03a's fixes for its meaning.

## What was checked

- **The code.** Worktree `wt-g03` at `a3c5fa8b72e50939822f22364647dc844a3914a0`, clean. I read all eleven files of the pack in full, and parts of `EnsemblesLemmas`, `GGMReduction`, `Repetition`'s neighbours, the copies named below, and the `03b`, `03c` and `03e` findings.
- **The source.** The pdftotext extracts in `blueprint/src/references/pass-shelat-2010-{ch2,ch3,appendix}.raw.md`, plus book p. 181 from `scratchpad/srctext/p178.txt`. The PDF itself is in the repository root (`Pass–Shelat.pdf`). So the auditor's (src) rows are now checked: see #6 and #25.
- **The records.** `DESIGN.md`, the plan's decision log (`PassShelatChapter2-4Plan.md`, lines 362–374; the bundle did not carry it), `policy.md`, `duplication-ledger.md`, `run3-audit-summary.md` and the evidence under `evidence/a/`.
- **Ch. 5–8.** Five worktrees, all clean: `wt-s2b` `afe5982f`, `wt-prong-a` `2d7b5441`, `wt-prong-b` `1cf007d1`, `wt-prong-c` `aa71d0e7`, `wt-prong-d` `6ea900ae`. I grepped the five ch. 5–8 directories.
- **The ripple script.** `gate03-review/scripts/ripple03a.py` greps each pending pack's file list (`gate03/packs.json`) for the affected identifiers.
- **No Lean was run.**

Line numbers are at `a3c5fa8b`. Paths are under `TCSlib/` unless written out.

## Findings

Types of fix used below:
- **D**: docstring or design record only.
- **S**: statement change.
- **A**: new API (additive).
- **P**: proof-level or refactor; no statement changes meaning.

### #1 (minor, agree): `NUPPT.Computes` presented as Def 24.6 without `Uniform`

- **Verdict: true.**
  - `Complexity/Randomized/PPT.lean:224–229` says "`A` computes `f` with probability one [PS10, Definition 24.6]". The module docstring (:36–39) and DESIGN D3 say the same. Nothing in the definition requires `A.Uniform`.
  - The source's notion is for "a randomized algorithm", which Def 23.4 defines as a PPT, a uniform Turing machine (ch2 raw :129–132, :95–99).
  - The auditor's machine checks out: `ofPolyTime polyTimeComputable_inAdvice (.const 0) (.const 1) (fun n => [h n]) _` has `runAt n y r = [h n] = f ⟨1^n, y⟩`, for an arbitrary `h`.
  - The file's own converse needs uniformity: `Closure.lean:381`, `Computes.polyTimeComputable (hA : A.Uniform)`.
- **Downstream check (the auditor's point (c)): clean.**
  - Ch. 5–8: 0 uses of `Computes` in the five directories.
  - Ch. 2–4 statements: `Adversary.lean:208` (`computes_iff_uprob`, an equivalence with no efficiency claim), `Closure.lean:381` and `PPT.lean:314`. The last two both assume `Uniform`.
  - Prose: `OneWay.lean:103`, `Pseudorandom.lean:39,126` and `PRF.lean:328` say "equivalent by `Computes` + `ofPolyTimeUniform`". That is the uniform direction, so it is correct.
- **Fix (D).** Add one sentence to `Computes`, to the module docstring and to DESIGN D3: "[PS10, Def 24.6] proper is the case `A.Uniform`. For a non-uniform `A`, `Computes` is the advice analogue and holds for uncomputable `f` (advice `[h n]`)." The auditor's option (b), a `PPT.Computes` wrapper, has no consumer, so skip it.
- **Ripple:** none. `Computes` is on the S1 interface list, so tell Seyoon about the docstring change; nothing needs re-sync.
- **Ruling:** no.

### #2 (minor → note): `Indist.copies` requires `Samplable X`, `Samplable Y`

- **Verdict: partly true.**
- **True:**
  - Against non-uniform distinguishers the hypotheses are unnecessary. Use the advice hybrid: fix `k` and the other `t − 1` coordinates `w*` that keep the gap, and hard-wire them with `exists_withAdvice`.
  - An `Ensemble` with `σ n = Fin 3` is never `Samplable`. `Samplable` (`Ensembles.lean:149–152`) demands an exact law over `2^{s(n)}` seeds, so the law is dyadic.
- **Not true:** "stronger than the uses can meet".
  - There are no uses: 0 in ch. 2–4 statements and 0 in ch. 5–8. The one intended use, PRG outputs, gets `Samplable` from `Easy.samplable` (`Pseudorandom.lean:60,167,169`).
  - The hypothesis is faithful to the cited source. [Gar26, Lemma 3.3]'s reduction samples the other copies; `Pseudorandom/Indistinguishability.lean:193–197` says "this is where efficient samplability of X and Y is used".
  - It is also the frozen design: D6, "`Indist.copies` takes `Samplable X`, `Samplable Y`".
- **Severity:** note. No statement builds on it, and nothing in it misleads.
- **Fix (D).** Add to the docstring at `Ensembles.lean:437–440`: "The samplability hypotheses are [Gar26, Lemma 3.3]'s uniform reduction (D6). Against non-uniform distinguishers they can be dropped by hard-wiring the hybrid index and the other copies. That form is not proved, since no consumer needs copies of a non-samplable ensemble." A samplability-free `Indist.copies'` (A, with its reduction in `EnsemblesLemmas`, 03i) can go to the backlog.
- **Ripple:** none.
- **Ruling:** no. D6 stays as frozen.

### #3 (minor, agree): `exists_comp` is blind to `n`

- **Verdict: true.** In `Closure.lean:200–203`, `pre` sees only `y` and `post` sees only `A`'s output.
- **One correction.** `EnsembleLemmas.exists_pushRed` is public in `EnsemblesLemmas.lean` (03i's scope), not private, as the auditor's own note 22 says.
- **Evidence that the gap costs work.** Ch. 5–8 build their n-aware reductions from the raw layout: `NUPPT.inParam` occurs 55 times and `NUPPT.inArg` 57 times across 7 files in prongs A, B and C.
- **Fix (A).** Add to `Closure.lean`:
  ```lean
  theorem NUPPT.exists_compParam (A : NUPPT) {pre post : List Bool → List Bool}
      (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
      ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
        ∀ n y r, B.runAtL n y r =
          post (pairEncode (List.replicate n true) (A.runAtL n (pre (advInput n y)) r))
  ```
  - The raw function is `z ↦ post ⟨inParam z, A.output (layout (inParam z) (pre ⟨inParam z, inArg z⟩) (inAdvice z) (inCoins z))⟩`.
  - The proof is the same as `exists_comp`'s.
  - `exists_comp` becomes the special case.
- **Ripple:**
  - Additive.
  - Optionally, `EnsembleLemmas.exists_pushRed` (03i) could be re-derived from it.
  - Ch. 5–8: none. `ObliviousTransfer.lean:392`'s sketch cites `exists_comp` and keeps working. The closure calculus is on the S1 list, so announce the addition.
- **Ruling:** no.

### #4 (minor → major): the state-loop host is private

- **Verdict: true, and understated.**
  - `Repetition.lean:264` has `private theorem polyTimeComputable_stateFind`. It is a host in the sense of policy §1, "Hosts come first", which is binding (user, 2026-10-12): "A host is never built `private` … A private host already in the tree is harvested into the shared layer before a second consumer is briefed against it."
  - The trigger has fired three times. There are three public copies:
    - `GI.stateFind` (`ZeroKnowledge/GraphIsomorphism/Efficiency.lean:83–100`: "copy of `polyTimeComputable_stateFind` …, which is private there"), used by `EfficiencyRep.lean:206,405` (03k);
    - `EncodingMachines.polyTimeComputable_stateFind` (`ZeroKnowledge/EncodingMachines.lean:470–490`, 03k), used by `ThreeColoring/Machines.lean:126` (03g);
    - `GGMRed.stateLoopFun` with `stateLoopFun_poly` and `stateLoopFun_eval` (`Asymptotic/GGMReduction.lean:258–300`: "the function form of the private …"; 03j). Ch. 5–8 cites this one: `wt-s2b/.../Games/Efficiency.lean:124–126,214` (proof sketches).
  - There is also a fixed-round variant, `polyTimeComputable_stateIterate` (`HardCoreLoops.lean:62–70`, 03i).
- **On the auditor's two "deficiencies" of the public lemmas.** Both are correct.
  - (i) `horbit` quantifies over every word. Once the loop is pre-composed with `x ↦ ⟨x, start x⟩`, a guard is needed.
  - (ii) Rounds are counted in `|x|`.
  - Re-deriving the form takes about 20 lines from public pieces (`StateLoop.gstep_poly`, `length_gstep_iterate_le`, `gstep_iterate_eq`, `find?_range_eq_some`). That is why it was copied.
- **Severity:** major. A binding rule is broken and the debt has spread. It needs the fix, or the user's explicit acceptance (pack scale: "debt that needs explicit human acknowledgment").
- **Fix (P/A).**
  - Drop `private` and keep the full name `Complexity.polyTimeComputable_stateFind` in `Repetition.lean`. Do not move it to `Build/StateLoop`, which sits below `iterateFind`. Register it in the host registry.
  - Delete the two 03k copies and re-point their users.
  - For `GGMRed.stateLoopFun`, either derive `_poly` and `_eval` in one line each from the public lemma, or move the function form next to the lemma (for example `Complexity.StateLoop.loopFun`) and re-point `GGMReductionEval.lean:610,635` and the two wt-s2b sketches.
  - The deletion must be atomic. Inside `namespace TCSlib.Cryptography.EncodingMachines` with `open Complexity`, two `polyTimeComputable_stateFind`s would collide.
  - Update the prose that calls it private: `Repetition.lean:40–46`, `Build/StringLoops.lean:36–38` (03l) and `HardCoreLoops.lean:68`.
- **Ripple:**
  - Packs: 03g (`Machines.lean`), 03j (`GGMReduction`, `GGMReductionEval`), 03k (`Efficiency`, `EfficiencyRep`, `EncodingMachines`), 03l (prose only), 03i (prose only).
  - Ch. 5–8: the two wt-s2b sketches.
  - No statement changes meaning.
- **Ruling:** R2 (when). The fix itself is not a design choice.

### #5 (minor, agree): `polyTimeComputable_runAtL` overclaims "polynomial-size `A_n`"

- **Verdict: true.**
  - `NonUniform.lean:127–128` proves `PolyTimeComputable` at each fixed `n` only. The machine and the constants may depend on `n`, through `polyTimeComputable_const (A.advice n)` at :130–131.
  - The proof never uses `advice_length`, so the statement would hold with `2^n` bits of advice.
  - The docstrings at :118–121, :31–33 and :57–59 say "each `A_n` is a polynomial-size machine".
- **Consumers:** none (grep).
- **Fix (D).** Reword: "at each fixed `n` the activation is a polynomial-time function of `⟨y, r⟩` (the machine hard-wires `1^n` and `advice n`, so its size and constants depend on `n`). The polynomial size of `A_n` in Def 26.8 comes from `|advice n| ≤ adv(n)`, not from this lemma."
- **Ripple:** none.
- **Ruling:** no.

### #6 (minor (src) → note): `pairwise_sampling_ineq` does not state its cost

- **Verdict: true, now checked against the source.** The appendix (raw :100–108, p. 189) reads: "`E(X_i) = µ` and `|X_i| ≤ 1` … `Pr[|∑X_i/n − µ| ≥ e] ≤ (1 − µ²)/(ne²)`". For bits, `1/4 > 1 − p²` exactly when `p > √3/2`. The deviation note at `Ensembles.lean:671–673` gives the `p(1−p) ≤ 1/4` bound but not this comparison.
- **Severity:** note. The deviation is declared and benign:
  - the lemma has no consumer (grep: 0 outside `Ensembles.lean`);
  - the campaign's samplers (Goldreich–Levin) work near `p = ½`.
- **Fix (D).** Add to the deviation clause: "weaker than the text's `(1 − p²)/(mε²)` when `p > √3/2`; the variance form `p(1−p)/(mε²)` implies both."
- **Ripple:** none.
- **Ruling:** no.

### #7 (minor, agree): `Ensemble` says "every distribution is dyadic"

- **Verdict: true.** `Ensembles.lean:112` says "every distribution is dyadic (a pushforward of uniform seeds)". But `σ n` is any finite nonempty type (:125–129), so the laws are rational. Only `Samplable` laws are dyadic. The module docstring (:46), D6 and register #5 get this right.
- **Also missed:** the same deviation note does not mention the fixed length. Def 69.3 (ch3 raw :93–95) allows "a probability distribution over `{0,1}*`". The formal ensemble lives on `{0,1}^{ℓ(n)}`, which is what Def 69.4 requires.
- **Fix (D).** "Deviation: each `X_n` is the pushforward of the uniform distribution on a finite nonempty seed set (rational probabilities; samplable ensembles are dyadic, D6), on strings of the fixed length `ℓ(n)` that Def 69.4 requires (Def 69.3 allows `{0,1}*`)."
- **Ripple:** none.
- **Ruling:** no.

### #8 (minor → major): duplicated material without ledger entries

- **Verdict: true, and much wider than reported.** Policy §1, Duplication: "every instance of duplicated proved material must be human-approved … the audit template treats accumulated duplication as a major finding that a gate cannot close over without the human maintainer explicitly accepting the debt". None of the following is in `duplication-ledger.md`, which holds DL-1 to DL-8. The copies are disclosed in docstrings, so they are debt, not a freeze violation. Five of the six families are rooted in a `private` declaration in this pack's files:

  | Family | Copies (pack) |
  |---|---|
  | block bijection `{0,1}^{qℓ} ≃ ({0,1}^ℓ)^q` | `FunFamily.blocks` (`OneWay.lean:201`, 03b; 56 qualified uses in 14 files); private `Ensemble.blocks` (`Ensembles.lean:186`, 03a); `EnsembleLemmas.blocks` (`EnsemblesLemmas.lean:365`, 03i); `blocksEquiv` (`HardCoreLoops.lean:93`, 03i); `OneWay.blocksE` (`OneWayYao.lean:62`, 03h); `blocksEquivX` (`HardCoreGL.lean:767`, 03i, any codomain); the inverse `GI.blocksEquiv` (`GraphIsomorphism/SoundnessRep.lean:230`, 03k). Most copies carry their own `_apply`, `_symm_apply` and `ofFn_…_symm` lemmas. |
  | applied-form composition `ptc_comp` | private in `Closure.lean:148` (03a); private copies in `UniversalLemmas.lean:66`, `Universal.lean:337` (03h), `Collections.lean:642` (03b) and `EnsemblesLemmas.lean:174` (03i); public in `ThreeColoring/Machines.lean:87` (03g) |
  | state loop | see #4: private original plus three public copies |
  | `abs_uexp_sub_le` | private in `Sampling.lean:188` (03a); public copy `PublicKeyLemmas.lean:823` (03j: "copy of the private lemma of … Sampling") |
  | `forall_of_uprob_eq_one` | private copy in `Adversary.lean:190`. The original `HardcoreBit/Basic.lean:107` is public and importable; "lives in a frozen file" forbids editing it, not importing it. |
  | `negligible_zero` | `Ensembles.lean:231`; copy `negligible_const_zero` in `ZeroKnowledge/Defs.lean:197` (03e) |

- **Fix (P), to be done atomically per family, since the public names collide once the `private`s go:**
  - Adversary: `import TCSlib.Cryptography.HardcoreBit.Basic`, delete :188–201, use `HardcoreBit.forall_of_uprob_eq_one` at :217.
  - `blocks`: move `FunFamily.blocks` and its two lemmas (`blocks_symm_apply`, `ofFn_blocks_symm`) down into a file every user imports. `Adversary.lean`, beside `decodeFin` and `padFin`, works. Keep the full name `TCSlib.Cryptography.FunFamily.blocks`, so its 56 qualified uses don't change. Then delete the other five copies and their lemma copies, and turn the inverse into `(FunFamily.blocks m c).symm`. `blocksEquivX` may stay as the general-codomain form if 03i wants it, or become the canonical form.
  - `ptc_comp`: publish one applied-form lemma in `Closure.lean` and delete the five copies, or inline `hg.comp hf`.
  - `abs_uexp_sub_le`: make `Sampling`'s public and delete the 03j copy.
  - `negligible_zero`: see R3.
  - `stateFind`: see #4.
- **Ripple:**
  - Pack files touched: 03a; 03b (`OneWay.lean` loses `blocks` to a lower file, `Collections.lean`); 03e (`ZK/Defs`); 03g; 03h (`OneWayYao`, `Universal*`); 03i (`HardCoreLoops`, `HardCoreGL`, `EnsemblesLemmas`); 03j (`PublicKeyLemmas`, `GGMReduction`); 03k (`SoundnessRep`, `Efficiency`, `EncodingMachines`).
  - No statement changes meaning, but public statements in 03h, 03i and 03k name `blocksE`, `blocksEquiv` and `GI.stateFind`, so their text changes.
  - Ch. 5–8: none. The `blocks` hits there are prose.
- **Ruling:** R2 (ledger, and when to clean up) and R3 (`negligible_zero`).

### #9 (minor, agree): the `Claim-26.3` tags read as [PS10] item numbers

- **Verdict: true.** The bare tags are at `Closure.lean:211` (`[Claim-26.3, implicit]`), :275 (`(d)`), :305 (`(c)`) and :328 (`(b), (c), (e)`). :191 has `[PS10, §2.1, implicit; Claim-26.3 …]` without the word "inventory".
  - The book has no item 26.3. §2.1 has 23.4, 23.5, 24.6, 24.7 and 26.8; §2.2 has 26.1, 27.2, 27.3 and 28.4.
  - `Claim-26.3` is an inventory id (`inventory-ch2.md:104,269`), and it breaks ch3's own synthetic-id convention, `<Kind>-<page>.<letter>`.
- **Also missed:** `exists_reparam_advice` (:236) has no tag at all.
- **Fix (D).** Use "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" throughout and add it to `exists_reparam_advice`. Do not rename the inventory id: it is cited elsewhere.
- **Ripple:** none.
- **Ruling:** no.

### #10 (minor, agree): `StatClose` lacks its defining tag

- **Verdict: true.** `Sampling.lean:103–108` cites §2.4.2 and §4.3, where the notion is used. [PS10] defines it only at Def 181.1 (book p. 181): "Two distributions X and Y are ε-close … if for every (deterministic) distinguisher D (with no time bound), `|Pr[D(x)=1] − Pr[D(y)=1]| ≤ ε`". The ch. 2–4 and appendix extracts contain no definition. `EpsClose` (`InformationTheory/Extractors.lean:65–69`) and `SamplingFinDist.lean:30–32` already cite Def 181.1.
- **Fix (D).** Add "[PS10, Definition 181.1], in its sup-over-test-sets form" to the docstring, and Def 181.1 to the module `## References` (:90–92).
- **Ripple:** none.
- **Ruling:** no.

### #11 (minor, agree): eleven `@[simp]` attributes without recorded approval

- **Verdict: true.** The eleven are at:
  - `PPT.lean:261, 266, 271, 298`;
  - `Closure.lean:104, 108, 112, 116, 161, 169`;
  - `Sampling.lean:354`.

  DESIGN §2.1 (:190) shows `@[simp]` only on `eval_*`. Policy §1 (user, 2026-10-16): "None carries `@[simp]` unless a gate approves it."
- **Same question in other packs:** 03b #12a (15 lemmas), 03c #11 (1) and 03e #17 (15).
- **Fix:**
  - Approve, with no change (recommended); or
  - drop the attributes (P). That is a replay of everything downstream. Ch. 5–8 has 62 non-`only` `simp` calls, and 10 of its files use `layout` or `ofPolyTime*`. Prong A's `Lamport.lean:429–430` names the lemmas explicitly and is unaffected either way.
- **Ruling:** R1.

### #12 (minor, agree; understated): facade import, and `negligible_zero` out of place

- **Verdict: true.**
  - **The facade.** `Ensembles.lean:6` imports `TCSlib.Complexity.Randomized`, a facade of 71 modules, 65 of them unrelated to the campaign (`Randomized.lean`). It puts 77 `Complexity/Randomized/*` modules into the replay closure (`evidence/a/replay.log`); the auditor's count of 65 is right.
  - **Missed: two more files import the facade.** `EnsemblesLemmas.lean:6` (03i) and `Candidates/DiscreteLog.lean:6` (03f1).
  - **Missed: `negligible_zero` (`Ensembles.lean:231`) has a second copy:** `negligible_const_zero` (`ZeroKnowledge/Defs.lean:197`, 03e).
  - **The auditor's fix conflicts with D2.** Moving the lemma into `Foundations/Negligible.lean` runs against "never into the frozen Garg files".
- **Fix (P).**
  - Use precise imports, `Randomized.{Closure, Repetition}` or whatever the file actually uses, in all three files.
  - Move `negligible_zero` per R3. `Negligible.lean` is in `namespace TCSlib.Cryptography` (:51), so the full name, and its four users (`Ensembles:308`, `PRF:270`, `NextBit:740`, `ZK/Encryption:102`), stay unchanged.
- **Ripple:**
  - Elaboration only: anything that relied on the facade transitively must be found by a replay.
  - Ch. 5–8 prong D uses `Randomized.InBPP`. It reaches `Randomized/Classes` through `BPPBridge` independently (checked), so the cleanup does not break it.
  - Packs: 03f1 and 03i (an import line each); 03e (under R3-A).
- **Ruling:** R3, for the `negligible_zero` part only.

### #13 (minor, agree): the `SamplingFinDist.lean` header

- **Verdict: true.** Lines 1–9 have no `Authors:` line and no `set_option maxHeartbeats 0`, and the module docstring has no `## Main definitions` section. Lint found the last two.
- **Fix:** the header (D).
- **Ripple:** none.
- **Ruling:** no.

### Notes #14–#26

| # | Verdict | Severity | Evidence / correction | Fix · ripple · ruling |
|---|---|---|---|---|
| 14 | true | note | Checked. `PolyExpr` has ℕ coefficients and no subtraction, so `eval` is either constant or strictly increasing, and `hℓ` fails only for constant `ℓ ≡ L`. In that case `IndistLit` makes each of the `2^L` point tests negligible. Then `TV(X_n, Y_n) ≤ ½Σ_{t₀}|X_n(t₀) − Y_n(t₀)|` is negligible and bounds every distinguisher (`distAdv_le_of_statClose`). | D: one sentence on `IndistLit.toIndist` (`Ensembles.lean:340–342`), and in D5 and register #5 change "injective" to "every `PolyExpr ℓ` (the constant case by point tests, not formalized)". Dropping `hℓ` would be an S change; there is no consumer. No ruling. |
| 15 | true | note | Checked. Under [PS10]'s experiment, `f(0^{|y|}‖y) = y` succeeds with probability 1. Under the typed one a special preimage has the wrong length, so success is at most `Adv_g + 2^{-L/2}`. This is the same daylight as 03b #2 (`ofString` without `LengthRegular`). | D, routed to 03b #2's resolution: state the proviso at `FunFamily.ofString`, and add a pointer from `inverter` (`Adversary.lean:99–100`). No ruling. |
| 16 | true | note | `hybrid_lemma` (`Ensembles.lean:415–417`) takes `X : ℕ → σ → γ`, one seed type. Harmless. | D (optional). No ripple. |
| 17 | true | note | The `PolyExpr` docstrings (`PolyExpr.lean:12–24, 63–68`) do not say that `n − 1`, `⌊n/2⌋` and `⌈log n⌉` are not expressible. `exists_reparam_advice` is the escape hatch (D9). | D, one sentence. No ripple. |
| 18 | true | note | `push` (`Ensembles.lean:176–182`) pads with `padFin`, which loses information for variable-length `M`. It is lossless when `M` has the fixed output length `ℓ'(n)`, the only case Def 69.4 can type. Ch. 5–8 uses no `Ensemble` (0 hits); it works over the games framework and `OracleEnsemble`. | D: one sentence in `push`. Do not build `EnsembleL` now, since no consumer asks for it. No ruling. |
| 19 | true | note | `axioms.log` has 41 entries, and the eleven named lemmas are not among them. The replay shows 22 `sorry` warnings: TimeConstructible 2, NonUniform 1, Build/Loop 5, Build/Primitives 3, RecordTable 4, Wrappers 2, Composition 3, Encoding 1, Simulation 1. | Add the prints to `audits/pass-shelat/Checks.lean` and re-run with the repair. Not Lean statements. |
| 20 | **partly true** | note | **(i) True.** D11 (`DESIGN.md:155–157`) names `NUPPT.ofPartial`, which does not exist. The `sorry` is in `decides_of_decidesWithAdviceInTime` (`NonUniform.lean:153–158`), whose sketch does `ofPartial`'s clocking inline. **(ii) False.** The Q5 ruling exists: `PassShelatChapter2-4Plan.md:366` (2026-10-27, "Open question 5 … outside the mandatory core"), and :371 (2026-10-28) names this bridge as "the only remaining machine-layer sorry". The bundle did not carry the plan. I agree that the statement is true: clock `M`, use `α` as advice at `|x|`, no coins. | D: annotate D11 and §8 Q5 with the decision-log entries and the actual admission. No ruling: it is already ruled. |
| 21 | true | note | Only "nonempty" checks exist (`PPT.lean:329–335`, `Indist.refl`, `uniform_samplable`). | Add a `Checks.lean` entry with a constant-zero ensemble and `¬ (uniform .var).Indist zeros` (first-bit distinguisher). It needs a small `def` in `Checks.lean` or in `Ensembles`. No ripple. |
| 22 | **partly true** | note | `EnsemblesLemmas.lean` is not in 03a, but it **is** audited: it is in 03i's scope (`PLAN.md` 03i row; `03i-pack.md:34`). Ch. 5–8 cites none of its declarations (0 hits for `EnsembleLemmas`, `exists_pushRed`, `coinsEquiv` and `acceptProb_*`). | Pack erratum: list it as context for 03a, audited in 03i. No ruling. |
| 23 | true | note | `inventory-ch2.md:265` (Def-26.8 "run on `pairEncode (pairEncode x (α \|x\|)) r`", `Ca·(n+1)^ca`) and the pack's Q1 are stale against D3 and D4. | Add "superseded by DESIGN D3–D6" banners to the inventory rows, and an erratum to the pack. Not Lean. |
| 24 | true | note | (a) `PPT.lean:62–66`, "with `φ := length`": `φ : ℕ → ℕ`, and (i) holds by `runLit`'s definition. (b) `Ensembles.lean:390` cites "run-3 audit note P2-4". `run3-audit-summary.md` has only P2-1 and P2-2 (:91–101), and nothing under `briefs/` or `audits/` mentions P2-4. | D: fix (a); for (b), cite "`exists_comp` sees only `y` (gate 03a #3)" instead. No ruling. |
| 25 | true then; **resolved** | note | The source is in the tree. I checked #6 against p. 189 (confirmed), and read Defs 23.4, 23.5, 24.6, 26.8, 69.3, 69.4 and Lemmas 71.5, 71.6, 73.8 (ch2 raw :95–216, ch3 raw :93–300). No new daylight: `Distinguishes` is strict, like p. 70's "> e" (`Ensembles.lean:218–222`), and `prediction_lemma`'s strict conclusion is stronger than the text's `≥`. | Close the note. |
| 26 | true | note | `uprob` on an empty type is 0 (Def at `Sampling.lean:109`). Every use has nonempty seeds (`Ensemble.nonempty`, `SamplingFinDist`'s `[Nonempty σ]`). | D, optional. No ripple. |

## Rulings for the user

**R1. Unapproved `@[simp]` attributes.** This covers 03a #11, and the same question in 03b #12a, 03c #11 and 03e #17.
- **(A) Recommended.** Approve, in one gate-03 ruling, every `@[simp]` that the four findings list, and record the list in the resolutions. 03a's eleven are simp-normal forms: the field equations of `ofPolyTime` and `ofPolyTimeUniform`, the projections of `layout`, the decoding of `combineAdvice`, and `bitsEquiv_val`. **Cost:** none; no file changes.
- **(B)** Approve 03a's eleven now, and decide the other packs' lists one by one. **Cost:** a replay for each pack whose attributes are dropped.
- **(C)** Drop every unapproved attribute. **Cost:** a full replay of ch. 2–4 (about 93 files) and of the five ch. 5–8 worktrees, with unknown breakage. Ch. 5–8 alone has 62 non-`only` `simp` calls, and the ch. 2–4 proofs were written against these simp sets.

**R2. Duplication rooted in 03a's `private` helpers** (#4, #8 and the copies listed there).
- **(A) Recommended.** Ledger the six families as DL-9 to DL-14 under "Inherited with ch. 2–4", and clean them up in the gate-03 repair PR:
  - make `polyTimeComputable_stateFind`, `ptc_comp` and `abs_uexp_sub_le` public;
  - import `HardcoreBit.Basic` in `Adversary.lean`;
  - keep one `FunFamily.blocks` in a low file;
  - delete the copies;
  - re-point the wt-s2b sketches.

  **Cost:** one proof-level PR over about 15 files in 03a, 03b, 03e, 03g, 03h, 03i, 03j, 03k and 03l, plus a replay. 03h, 03i and 03k wait for it, because their public statements name copies that it renames.
- **(B)** Ledger now, with "paid back at the `main` landing". Fix only the parts inside 03a's files now (drop the three `private`s, delete `Adversary`'s copy), keeping the downstream copies under different names. **Cost:** the gate closes on recorded debt; the copies stay on the trusted surface; 03g to 03k audit them as they are, with an erratum; ch. 5–8 keeps citing `GGMRed.stateLoopFun`.
- **(C)** Accept the copies permanently ("accepted, no payback"). **Cost:** it leaves a standing breach of the binding "Hosts come first" rule. Not recommended.

**R3. Where `negligible_zero` lives** (#12; its copy `negligible_const_zero` is in `ZK/Defs`, 03e).
- **(A) Recommended.** Move it to `Foundations/Negligible.lean`, as policy §1 "Helpers" asks. Its full name stays the same, so its four users don't change. Delete `negligible_const_zero` (2 uses). **Cost:** one 5-line lemma added to a Garg-audited file, overriding D2's "never into the frozen Garg files" for this one case.
- **(B)** Keep it in `Ensembles.lean`, and have `ZK/Defs` import `Ensembles`. **Cost:** `ZK/Defs` pulls in Ensembles' heavy closure (`EnsemblesLemmas`, `Indistinguishability`, `GeneratorFromPermutation`, `PairwiseIndependence`) for 5 lines.
- **(C)** Put it in a new campaign-owned helper file (for example `Asymptotic/NegligibleLemmas.lean`) that both import. **Cost:** one more small file; respects D2.

## What the auditor missed

1. **Duplication is wider than reported** (folded into #4 and #8).
   - The `blocks` bijection has 6 copies plus an inverse, most with their own lemma copies.
   - `ptc_comp` has 6 copies.
   - The state loop has 4, plus the variant `stateIterate`.
   - `abs_uexp_sub_le` and `negligible_zero` have 2 each.
   - The root cause is the same throughout: helpers that are `private` in this pack's files.
2. **The facade import also sits in** `EnsemblesLemmas.lean:6` (03i) and `Candidates/DiscreteLog.lean:6` (03f1) (#12).
3. **`exists_reparam_advice` has no source tag** (`Closure.lean:236`) (#9).
4. **`Ensemble.Samplable` misattributes** (`Ensembles.lean:147–148`). It cites "[PS10, … Lemma 71.6's multicopy corollary]", and [PS10] has no such corollary: the multicopy lemma is [Gar26, Lemma 3.3]. p. 72's Example ("efficiently sample") is the right tag. Minor, docstring only.
5. **`Ensemble`'s deviation note omits the fixed-length restriction** relative to Def 69.3 (#7).
6. **Prose calls `stateFind` private** in `Build/StringLoops.lean:36–38` (03l) and `HardCoreLoops.lean:68` (03i). Update it with #4.
7. **Cross-pack:** 03b #12b proposes moving `NUPPT.withIndexParam`, `length_runAt_le` and `runLenPoly` from `Collections.lean` into `Complexity/Randomized/`, which is 03a's directory. Ch. 5–8 cites `NUPPT.runLenPoly` and `length_runAt_le_runLenPoly` (`ObliviousTransfer.lean:417`, `Composability/PublicKey.lean:276–293`). Keep the full names `Complexity.NUPPT.*` when moving them; 03a's closing diff should then include them.
8. **The auditor's downstream check for #1 is clean** (see #1). Nothing in ch. 5–8 is a blocker on that account.

## Pending packs: which can go now

The criterion: does an 03a fix change a statement a pack audits or cites, or rename or delete a declaration on its surface? With the recommended options, **no fix changes any statement's meaning**. Only the dedup renames or deletes copies.

| Pack | Touched by 03a's fixes | Dispatch |
|---|---|---|
| 03d | No. It uses `negligible_zero` and `FunFamily.blocks` under unchanged names. | Unaffected by 03a; still held by F-1 (`PLAN.md`) |
| 03f1 | Only `DiscreteLog.lean:6`'s import line, if the facade cleanup is extended to it | **Now** |
| 03f2 | No | **Now** |
| 03g | `Machines.lean`: its public `ptc_comp` copy (:87) is deleted, and `stateFind` at :126 is re-pointed (proof) | **Now**, with a one-line erratum |
| 03h | `OneWayYao.blocksE` and its lemmas (public statements) are replaced by `FunFamily.blocks`; private `ptc_comp` in `Universal*` | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03i | `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks` and `ptc_comp` (public statements), the facade import, the `stateFind` prose | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03j | `GGMRed.stateLoopFun*`, `PublicKeyLemmas.abs_uexp_sub_le` | Held by F-1 anyway; under R2-A, re-pin after both land |
| 03k | `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `SoundnessRep.blocksEquiv` (public) | Under R2-A, after the dedup PR; under R2-B, now with an erratum |
| 03l | Only `StringLoops.lean:36–38` prose ("private") | **Now** |

Under R1-C, every pack's *proofs* would change, but no statement would. That would add a replay, not a reason to hold any statement pack.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03a-r1.md =====

# Gate 03a (machines and probability): round 1 resolutions

- **Round 1:** findings `findings/gate03a-findings.md`, verbatim, SHA-256
  `9dd9195111dfc8aca6748405f2730ca98c8f61f3ae51b2858b2fe87e8cfa5f92`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 0 majors, 13 minors, 13 notes.**
- **Review:** `review/gate03a-review.md`: 23 true, 3 partly true (#2, #20, #22), none false. Four
  severity changes: #4 and #8 minor → **major**; #2 and #6 minor → note. New tally **0 blockers,
  2 majors, 9 minors, 15 notes**. Eight items missed by the auditor (M1–M8 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`, decision log rows "Gate 03 rulings G3-5 to
  G3-8"**):** G3-5 (A), ledger the duplicates as DL-9 onward and clean them up in the gate 03
  clean-up PR (#4, #8); G3-6 (A), approve every listed `@[simp]` (#11); G3-7 (a), move
  `negligible_zero` to `Foundations/Negligible.lean`, overriding D2 for one lemma (#12). R-03l-1
  (gate 03l) widens the same clean-up PR; its part 1 also carries DL-11's first half (#4).
- **Repair:** commit `e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820` (on #198's head
  `c10ed6ace0b991146c0be769313fbbe52d36e25a`), merged with the ch. 2–4 head as
  `956c595f2584532899aac1fb6fbe3d0aab9fa370`, in PR #201 with 03c's
  `bc2aab59333e27729c9fbac3052cd650bf62c3aa`. #201's head is
  `0c348ff94cacf24d96d99078c9dd9e328530c8d2`, merged by `02951926d9c9cea1d3596afa71c252176ca9de1d`.
  Gate 03 clean-up part 1 is PR #203 (head `f29be161cd86cfc3a9c38bd203bfa095b4974086`, merged by
  `8ec28f130eaca5f7d7dc756953bde0807d41b7df`; evidence `evidence-repairs/03l-cleanup1/`). Evidence `evidence-repairs/03ac/` (replay of the 97 downstream modules
  plus `Checks`, the full `Checks` axiom print at #201's head, lint 0). Line numbers are at #201's
  head unless a row says otherwise; Lean paths are under `TCSlib/`.
- **Scheduled work** goes to the gate 03 clean-up: part 1 is merged (#203);
  part 2 follows #195 (`duplication-ledger.md` DL-9 to DL-15; `QUEUE.md:147`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | minor | **Fixed.** `NUPPT.Computes` (`Complexity/Randomized/PPT.lean:229–241`), the module docstring (:40–48, :89–90) and DESIGN D3 (`briefs/pass-shelat/DESIGN.md:64–67`) say that Def 24.6 proper is `A.Uniform ∧ A.Computes f` and that the non-uniform form holds for uncomputable `f`. No `PPT.Computes` wrapper (no consumer); the downstream check is clean (review: 0 uses in ch. 5–8). |
| 2 | note (was minor) | **Fixed** (docstring). `Ensemble.Indist.copies` (`Cryptography/Asymptotic/Ensembles.lean:456–460`) says the samplability hypotheses are [Gar26, Lemma 3.3]'s uniform reduction and can be dropped against non-uniform distinguishers (not proved, no consumer). D6 unchanged; the optional `Indist.copies'` is not added. |
| 3 | minor | **Fixed** (#203, item H; found missing while drafting these resolutions). `NUPPT.exists_compParam` (`Complexity/Randomized/Closure.lean:209`, at #203's head): closure under polynomial-time pre- and post-processing that see `1^n`, with the review's statement. `exists_comp` is re-derived as its special case (statement unchanged), and its Scope paragraph points to the new theorem; `Checks.lean` prints it (standard axioms). Its proof, like `exists_comp`'s, reads `PPT.lean`'s `runAtL` and `advInput` by `simp`; the equation lemmas `runAtL_eq` and `advInput_eq` are **scheduled** for part 2. |
| 4 | major (was minor) | **Fixed** in its first half (#203, item D): `Complexity.polyTimeComputable_stateFind` is public (`Complexity/Randomized/Repetition.lean:241`, at #203's head), with its statement unchanged, and the prose calling it private is fixed (`Repetition.lean`, `Build/StringLoops.lean`, `Asymptotic/HardCoreLoops.lean:68`). **Scheduled:** part 2 re-points the copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun` and the variant `stateIterate`, and their "private" docstrings (DL-11). Meanwhile `ThreeColoring/Machines.lean:126` names the `EncodingMachines` copy explicitly, since the public name made the call ambiguous. |
| 5 | minor | **Fixed.** `polyTimeComputable_runAtL` (`Complexity/Randomized/NonUniform.lean:122–128`), the module docstring (:33–37) and its main-results line (:61–62) say the machine's size and constants depend on `n`, and that Def 26.8's polynomial size comes from `advice_length`. |
| 6 | note (was minor, src) | **Fixed.** `pairwise_sampling_ineq`'s deviation (`Ensembles.lean:691–696`) states that `1/4 > 1 − p²` exactly when `p > √3/2`, and that the variance form implies both bounds. The review checked the source (p. 189). |
| 7 | minor | **Fixed.** `Ensemble`'s deviation (`Ensembles.lean:119–125`): rational laws (seeds `Fin 3` give mass `1/3`; the samplable ensembles are the dyadic ones, D6) on strings of the fixed length `ℓ(n)` (missed item M5). |
| 8 | major (was minor) | **Scheduled** (G3-5). Ledgered as DL-9 (`blocks`), DL-10 (`ptc_comp`), DL-11 (state loop), DL-12 (`abs_uexp_sub_le`), DL-13 (`negligible_const_zero`), DL-14 (`forall_of_uprob_eq_one`), all "accepted; scheduled"; clean-up part 2, except DL-11's first half (part 1). The copies are still in the tree, e.g. `Asymptotic/Adversary.lean:198`, `Ensembles.lean:199`, `Closure.lean:149`, `Asymptotic/Sampling.lean:198`, `ZeroKnowledge/Defs.lean:248`. |
| 9 | minor | **Fixed.** The catalogue tags read "[PS10, §2.1, implicit; inventory Claim-26.3(x)]" (`Closure.lean:192, 219, 245, 283, 313, 338`); `exists_reparam_advice` gains its tag (:245, missed item M3); the inventory id is not renamed. |
| 10 | minor | **Fixed.** `StatClose` (`Asymptotic/Sampling.lean:104–114`) cites [PS10, Definition 181.1] in its sup-over-test-sets form; the module References list it (:91). |
| 11 | minor | **Recorded** (G3-6, `QUEUE.md:125`): the eleven attributes are approved and unchanged: `coins_ofPolyTime`, `adv_ofPolyTime`, `advice_ofPolyTime`, `coins_ofPolyTimeUniform` (`PPT.lean:275, 280, 285, 312`); `inParam_layout`, `inArg_layout`, `inAdvice_layout`, `inCoins_layout`, `pairFstD_combineAdvice`, `pairSndD_combineAdvice` (`Closure.lean:105, 109, 113, 117, 162, 170`); `bitsEquiv_val` (`Sampling.lean:364`). |
| 12 | minor | **Fixed**, with two items **Scheduled.** Precise imports replace the facade in `Ensembles.lean:6–11`, `Asymptotic/EnsemblesLemmas.lean:6–7` and `Candidates/DiscreteLog.lean:6–8` (missed item M2); `negligible_zero` is in `Cryptography/Foundations/Negligible.lean:164` under its full name (G3-7 (a); D2's exception at `DESIGN.md:47–51`). Scheduled: `ThreeColoring/SimulatorMachine` is to import `NonUniform` itself so that `Ensembles` can drop it (`QUEUE.md:147`), and the copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean:248`) goes as DL-13 (part 2). |
| 13 | minor | **Fixed.** `Asymptotic/SamplingFinDist.lean:4` (`Authors:`), :9 (`maxHeartbeats 0`), :23–25 (`## Main definitions`: None). |
| 14 | note | **Fixed** (docstring). `IndistLit.toIndist` (`Ensembles.lean:349–354`), the module docstring (:41–42, :52–54), DESIGN D5 (`DESIGN.md:96–98`) and register item 5 (:1003–1004) say the two forms coincide for every `PolyExpr ℓ` (constant case by point tests, not formalized). `hℓ` is kept (no consumer). |
| 15 | note | **Fixed.** The wrong-length cost is stated on `NUPPT.inverter` (`Asymptotic/Adversary.lean:102–108`) and on `FunFamily.ofString` (`Asymptotic/OneWay.lean:198–206`), as routed with 03b #2. |
| 16 | note | **Fixed.** `hybrid_lemma` (`Ensembles.lean:426–428`): one seed type; other shapes embed into a product seed. |
| 17 | note | **Fixed.** `PolyExpr` (`Complexity/Randomized/PolyExpr.lean:68–72`): `n − 1`, `⌊n/2⌋`, `n(n−1)/2`, `⌈log₂ n⌉` not expressible; pad or use `exists_reparam_advice`. |
| 18 | note | **Fixed.** `Ensemble.push` (`Ensembles.lean:189–192`): padding is lossless only for exact `ℓ'(n)`-bit outputs. No `EnsembleL` (no consumer). |
| 19 | note | **Fixed.** The eleven prints and `negligible_zero`'s are in `audits/pass-shelat/Checks.lean:454–467`; all twelve print `[propext, Classical.choice, Quot.sound]` at #201's head (`evidence-repairs/03ac/checks-axioms.log:471–482`). |
| 20 | note (partly true) | **Fixed.** DESIGN D11 (`DESIGN.md:172–177`) names the real admission, `NUPPT.decides_of_decidesWithAdviceInTime`, and says `ofPartial` was never written; §8 Q5 (:1283–1285) cites the ruling of 2026-10-27. |
| 21 | note | **Fixed.** `PassShelatChecks.zeros` and `not_indist_uniform_zeros` (first-bit distinguisher) in `audits/pass-shelat/Checks.lean:475, 507`; its print is standard (`checks-axioms.log:483`). |
| 22 | note (partly true) | **Fixed in the closing-round pack** (pack erratum): `EnsemblesLemmas.lean` is context for 03a and audited in 03i. |
| 23 | note | **Fixed.** Banners "superseded by DESIGN D3–D6" on `inventory-ch2.md:255, 265` (Def-23.4, Def-26.8) and `inventory-ch3.md:38, 195, 204` (Machine-NUPPT, Def-69.3, Def-69.4); the erratum to the pack's stale Q1 is in the closing-round pack. |
| 24 | note | **Fixed.** (a) `PPT.lean:68–70`: (i) holds by `runLit`'s definition, no ill-typed `φ := length`. (b) `Indist.push`'s sketch cites gate 03a finding 3, not "P2-4" (`Ensembles.lean:402`). |
| 25 | note | **No change.** Resolved by the review: the source is in the tree; #6 checked against p. 189; Defs 23.4, 23.5, 24.6, 26.8, 69.3, 69.4 and Lemmas 71.5, 71.6, 73.8 read, no new daylight. |
| 26 | note | **Fixed.** `StatClose` (`Sampling.lean:115–118`): on an empty seed type the law is the zero measure; every use has nonempty seeds. |
| M1 | (review) duplication wider | **Scheduled** with #4 and #8 (DL-9 to DL-14). |
| M2 | (review) facade imports elsewhere | **Fixed** with #12 (`EnsemblesLemmas.lean:6–7`, `DiscreteLog.lean:6–8`). |
| M3 | (review) `exists_reparam_advice` untagged | **Fixed** (`Closure.lean:245`). |
| M4 | (review) `Samplable` misattributed | **Fixed.** `Ensemble.Samplable` (`Ensembles.lean:157–158`) cites [PS10, p. 72, Example] and [Gar26, Lemma 3.3] for the multicopy lemma. |
| M5 | (review) fixed length not declared | **Fixed** with #7 (`Ensembles.lean:122–123`). |
| M6 | (review) prose calls `stateFind` private | **Fixed** (#203, item D); see #4. |
| M7 | (review) 03b #12b's `NUPPT` helpers | **Fixed** in #198: moved to `Cryptography/Asymptotic/CollectionsHelpers.lean:58–115` (not 03a's directory) with the full names `Complexity.NUPPT.*` unchanged, so 03a's closing diff does not include them. |
| M8 | (review) downstream check for #1 | **No change:** clean (no ch. 5–8 use of `NUPPT.Computes`). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-r2/03a/repair.diff.txt =====

# Gate 03a, round 2: the repair diff
#
# Section A: every change to this pack's Lean files between the round 1 head a3c5fa8b72e50939822f22364647dc844a3914a0 and the round 2 pin e28773ef3bda6f7b4b112ec1657427bfef01e374, whichever repair made it (03a's commit, #201, #203).
# Section B: the 03a repair commit e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820 and #203's item H commit 43e8fe2c27c54c2c50e01541024995e95c6bf6fa: their changes outside this pack's files.

### --- A: this pack's files, a3c5fa8b72e50939822f22364647dc844a3914a0..e28773ef3bda6f7b4b112ec1657427bfef01e374 ---
diff --git a/TCSlib/Complexity/Randomized/Closure.lean b/TCSlib/Complexity/Randomized/Closure.lean
index df05331c..468cb1ed 100644
--- a/TCSlib/Complexity/Randomized/Closure.lean
+++ b/TCSlib/Complexity/Randomized/Closure.lean
@@ -31,7 +31,8 @@ The supplier table (DESIGN.md §2.5):
 
 | Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
 | --- | --- | --- |
-| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | projections, `pairEncode`, `comp` |
+| `exists_compParam` | `pre ⟨1^n, y⟩`, then `A.output`, then `post ⟨1^n, ·⟩` | projections, `comp` |
+| `exists_comp` | `exists_compParam` with `pre`, `post` ignoring `1^n` | `exists_compParam` |
 | `exists_reparam p` | advice `A.advice (p n)`; replace `1^n` by `1^{p n}` (`unaryPoly p`) | `unaryPoly` |
 | `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩`; cut `A.coins (φ n)` coins | `pairTakePoly`, `eval_mono` |
 | `exists_withAdvice` | advice `⟨A.advice n, β n⟩`; re-pair `y` with `β n` | pairing calculus |
@@ -53,7 +54,10 @@ Not in this file (they are FP-level facts the campaign uses directly): negation
 
 ## Main results
 
-* `Complexity.NUPPT.exists_comp` — closure under polynomial-time pre- and post-processing.
+* `Complexity.NUPPT.exists_compParam` — closure under polynomial-time pre- and post-processing
+  that reads the parameter (`pre` sees `⟨1^n, y⟩`, `post` sees `⟨1^n, output⟩`).
+* `Complexity.NUPPT.exists_comp` — its case that does not read the parameter (`pre` sees only
+  `y`, `post` only the output).
 * `Complexity.NUPPT.exists_reparam` — parameter change `n ↦ p(n)` (uniformity preserved).
 * `Complexity.NUPPT.exists_reparam_advice` — parameter change along a polynomially bounded
   `φ : ℕ → ℕ`, hard-wiring `1^{φ n}` and the advice at `φ n`; extra coins unread.
@@ -187,31 +191,63 @@ theorem length_combineAdvice_le (a b : List Bool) :
 
 /-! ### The closure catalogue -/
 
-/-- **Closure under polynomial-time pre- and post-processing** [PS10, §2.1, implicit;
-Claim-26.3 (a), (b)]: for an `NUPPT` `A` and polynomial-time `pre`, `post` there is an
-`NUPPT` `B` with the same coins and advice that computes `post (A(1^n, pre y; r))`.
+/-- **Closure under parameter-aware pre- and post-processing** [PS10, §2.1, implicit;
+inventory Claim-26.3(a), (b)] (gate 03a, finding 3): for an `NUPPT` `A` and polynomial-time
+`pre`, `post` there is an `NUPPT` `B` with the same coins and advice that, at parameter `n` on
+argument `y` with coins `r`, computes `post ⟨1^n, A(1^n, pre ⟨1^n, y⟩; r)⟩`: `pre` sees the
+adversary input `⟨1^n, y⟩` (`advInput n y`), and `post` sees the parameter `1^n` paired with
+`A`'s output. `exists_comp` is the case where `pre` and `post` ignore `1^n`.
 
 **Proof sketch.** The raw function is
-`z ↦ post (A.output (layout (inParam z) (pre (inArg z)) (inAdvice z) (inCoins z)))`, polynomial-time
-by `polyTimeComputable_layout`, `PolyTimeComputable.comp`, `NUPPT.polyTimeComputable_output`,
+`z ↦ post ⟨inParam z, A.output (layout (inParam z) (pre ⟨inParam z, inArg z⟩) (inAdvice z)
+(inCoins z))⟩`, polynomial-time by `polyTimeComputable_layout`,
+`PolyTimeComputable.pairEncode`, `PolyTimeComputable.comp`, `NUPPT.polyTimeComputable_output`,
 `hpre`, `hpost`; `B := ofPolyTime` of it with `A`'s coins and advice. On the layout
 `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` the projections return the slots (`runAtL_ofPolyTime`, the
-`pairFstD_pairEncode`/`pairSndD_pairEncode` identities), giving `post (A.runAtL n (pre y) r)`. -/
-theorem exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
+`pairFstD_pairEncode`/`pairSndD_pairEncode` identities), so `⟨inParam z, inArg z⟩` is
+`⟨1^n, y⟩ = advInput n y` and the value is `post ⟨1^n, A.runAtL n (pre (advInput n y)) r⟩`. -/
+theorem exists_compParam (A : NUPPT) {pre post : List Bool → List Bool}
     (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
     ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
-      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
-  have hF := ptc_comp hpost (ptc_comp A.polyTimeComputable_output
-    (polyTimeComputable_layout polyTimeComputable_inParam (ptc_comp hpre polyTimeComputable_inArg)
-      polyTimeComputable_inAdvice polyTimeComputable_inCoins))
+      ∀ n y r, B.runAtL n y r =
+        post (pairEncode (List.replicate n true) (A.runAtL n (pre (advInput n y)) r)) := by
+  have hF := ptc_comp hpost (polyTimeComputable_inParam.pairEncode
+    (ptc_comp A.polyTimeComputable_output (polyTimeComputable_layout polyTimeComputable_inParam
+      (ptc_comp hpre (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
+      polyTimeComputable_inAdvice polyTimeComputable_inCoins)))
   refine ⟨ofPolyTime hF A.coins A.adv A.advice A.advice_length, rfl, rfl, rfl, fun n y r => ?_⟩
   rw [runAtL_ofPolyTime]
   simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
 
-/-- **Parameter change `n ↦ p(n)`** [Claim-26.3, implicit]: for an `NUPPT` `A` and a syntactic
-polynomial `p` there is an `NUPPT` `B` with coins `A.coins.subst p` that at parameter `n`
-behaves as `A` at parameter `p(n)`; `B` is uniform when `A` is (the prefix `1^{p(n)}` is
-computed, not hard-wired).
+/-- **Closure under polynomial-time pre- and post-processing** [PS10, §2.1, implicit;
+inventory Claim-26.3(a), (b)]: for an `NUPPT` `A` and polynomial-time `pre`, `post` there is an
+`NUPPT` `B` with the same coins and advice that computes `post (A(1^n, pre y; r))`.
+
+**Scope** (gate 03a, finding 3): `pre` sees only the argument `y` and `post` only `A`'s output;
+neither sees `1^n`. Pre- and post-processing that depends on the parameter (padding or cutting
+to `ℓ'(n)` bits, slicing `p(n)` bits, planting at a position that depends on `n`) is the
+parameter-aware form `exists_compParam`, where `pre` sees `⟨1^n, y⟩` and `post` sees `1^n`
+paired with the output. Reductions that also read the advice or the coins are built as
+`ofPolyTime` of a raw function of the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`,
+`polyTimeComputable_layout`), as `EnsembleLemmas.exists_pushRed` does for [PS10, Lemma 71.5].
+
+**Proof sketch.** `exists_compParam` with `pre ∘ snd` and `post ∘ snd`: the second component of
+`advInput n y = ⟨1^n, y⟩` is `y`, and that of `⟨1^n, A.runAtL n (pre y) r⟩` is `A`'s output
+(`pairSndD_pairEncode`). -/
+theorem exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
+    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
+    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
+      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
+  obtain ⟨B, hc, ha, hα, hB⟩ := exists_compParam A (ptc_comp hpre polyTimeComputable_pairSndD)
+    (ptc_comp hpost polyTimeComputable_pairSndD)
+  refine ⟨B, hc, ha, hα, fun n y r => ?_⟩
+  rw [hB, pairSndD_pairEncode]
+  simp [advInput]
+
+/-- **Parameter change `n ↦ p(n)`** [PS10, §2.1, implicit; inventory Claim-26.3]: for an
+`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `A.coins.subst p`
+that at parameter `n` behaves as `A` at parameter `p(n)`; `B` is uniform when `A` is (the
+prefix `1^{p(n)}` is computed, not hard-wired).
 
 **Proof sketch.** Advice `A.advice (p n)` of length `≤ (A.adv.subst p).eval n`
 (`PolyExpr.eval_subst`); the raw function replaces the parameter slot `1^n` by
@@ -233,13 +269,13 @@ theorem exists_reparam (A : NUPPT) (p : PolyExpr) :
   rw [runAtL_ofPolyTime]
   simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
 
-/-- **Parameter change along an arbitrary polynomially bounded `φ : ℕ → ℕ`** (non-uniform):
-for an `NUPPT` `A`, `φ` with `φ n ≤ p n`, there is an `NUPPT` `B` with coins
-`A.coins.subst p` that at parameter `n` behaves as `A` at parameter `φ n` on the first
-`A.coins (φ n)` coins (extra coins are unread). This is the one place an abstract `ℕ → ℕ`
-appears (as a hypothesis with a `PolyExpr` majorant, D9); it serves Lemma 64.3's
-`m(n) = n − ⌊log₂ n⌋`, the literal/`1^n` bridges of Definitions 26.1 and 69.4, and the
-interdefinability argument of D3/D4.
+/-- **Parameter change along an arbitrary polynomially bounded `φ : ℕ → ℕ`** (non-uniform)
+[PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`, `φ` with `φ n ≤ p n`,
+there is an `NUPPT` `B` with coins `A.coins.subst p` that at parameter `n` behaves as `A` at
+parameter `φ n` on the first `A.coins (φ n)` coins (extra coins are unread). This is the one
+place an abstract `ℕ → ℕ` appears (as a hypothesis with a `PolyExpr` majorant, D9); it serves
+Lemma 64.3's `m(n) = n − ⌊log₂ n⌋`, the literal/`1^n` bridges of Definitions 26.1 and 69.4, and
+the interdefinability argument of D3/D4.
 
 **Proof sketch.** Advice `⟨1^{φ n}, A.advice (φ n)⟩`, of length
 `2 φ n + 2 + |A.advice (φ n)| ≤ 2 p n + 2 + A.adv (p n)` by `hφ`, `advice_length` and
@@ -272,10 +308,10 @@ theorem exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
   rw [runAtL_ofPolyTime]
   simp [runAtL, advInput, coinLen, layout, inArg, inAdvice, inCoins]
 
-/-- **Hard-wiring advice** [Claim-26.3 (d)]: for an `NUPPT` `A` and a polynomially bounded
-family `β n` there is an `NUPPT` `B` with the same coins that computes
-`A(1^n, ⟨y, β n⟩; r)` (the reductions of chapters 2–4 hard-wire hybrid indices, worst-case
-inputs and the given adversary's advice this way).
+/-- **Hard-wiring advice** [PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`
+and a polynomially bounded family `β n` there is an `NUPPT` `B` with the same coins that
+computes `A(1^n, ⟨y, β n⟩; r)` (the reductions of chapters 2–4 hard-wire hybrid indices,
+worst-case inputs and the given adversary's advice this way).
 
 **Proof sketch.** Advice `⟨A.advice n, β n⟩` of length `2 A.adv n + 2 + b n`
 (`length_pairEncode`); the raw function re-pairs the argument slot with the second half of
@@ -302,10 +338,11 @@ theorem exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
   rw [runAtL_ofPolyTime]
   simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
 
-/-- **Extra coins passed as data** [Claim-26.3 (c)]: for an `NUPPT` `A` and a syntactic
-polynomial `p` there is an `NUPPT` `B` with coins `p + A.coins` and `A`'s advice such that
-`B(1^n, y; r) = A(1^n, ⟨y, r.take (p n)⟩; r.drop (p n))`: the first `p n` coins become part of
-the input (a uniformly random string of length `p n`), the rest are `A`'s coins.
+/-- **Extra coins passed as data** [PS10, §2.1, implicit; inventory Claim-26.3(c)]: for an
+`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `p + A.coins`
+and `A`'s advice such that `B(1^n, y; r) = A(1^n, ⟨y, r.take (p n)⟩; r.drop (p n))`: the first
+`p n` coins become part of the input (a uniformly random string of length `p n`), the rest are
+`A`'s coins.
 
 **Proof sketch.** The raw function cuts the coin slot at `p(|1^n|)` with
 `polyTimeComputable_pairTakePoly p`/`pairDropPoly p` on `⟨inParam z, inCoins z⟩`, re-pairs the
@@ -325,9 +362,9 @@ theorem exists_split (A : NUPPT) (p : PolyExpr) :
   rw [runAtL_ofPolyTime]
   simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
 
-/-- **Sequential composition with input pass-through and fresh coins** [Claim-26.3 (b), (c),
-(e) with one call]: for `NUPPT`s `A`, `B` there is an `NUPPT` `C` with coins
-`A.coins + B.coins`, uniform when both are, computing
+/-- **Sequential composition with input pass-through and fresh coins** [PS10, §2.1, implicit;
+inventory Claim-26.3(b), (c), (e) with one call]: for `NUPPT`s `A`, `B` there is an `NUPPT`
+`C` with coins `A.coins + B.coins`, uniform when both are, computing
 `B(1^n, ⟨y, A(1^n, y; r₁)⟩; r₂)` where `r = r₁ ++ r₂` is cut at `A.coins n`. This is the
 machine-level form of the "sunglass" reduction `D' := D ∘ (sampler)` of [Gar26] used by
 Lemma 71.5 (`Indist.push`) and every two-stage reduction.
diff --git a/TCSlib/Complexity/Randomized/NonUniform.lean b/TCSlib/Complexity/Randomized/NonUniform.lean
index fd1140fb..6c186659 100644
--- a/TCSlib/Complexity/Randomized/NonUniform.lean
+++ b/TCSlib/Complexity/Randomized/NonUniform.lean
@@ -30,7 +30,11 @@ no information — and it is the layout of the literal forms of Definition 26.1
 (`WorstCaseOneWay`, `inverterLit`) and Definition 69.4 (`Ensemble.IndistLit`). The
 machine-sequence form is reflected only as a sanity statement here: at every parameter `n`
 the activation is a deterministic polynomial-time function of `(y, r)`
-(`NUPPT.polyTimeComputable_runAtL`), i.e. each "`A_n`" is a polynomial-size machine.
+(`NUPPT.polyTimeComputable_runAtL`). The machine of that statement hard-wires `1^n` and
+`advice n`, so its size and its time constants depend on `n`: the lemma bounds neither the
+size of "`A_n`" nor its running time uniformly in `n` (it would hold equally with
+exponentially long advice). The polynomial size of Definition 26.8's `A_n` comes from
+`|advice n| ≤ adv.eval n` (the field `NUPPT.advice_length`), not from this lemma.
 
 **Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
 (optional module). The equivalence of the two forms (`NUPPTSeq`, `nuppt_seq_iff_advice`, with
@@ -55,8 +59,8 @@ construction `NUPPT.ofPartial` and is off every critical path).
 * `Complexity.NUPPT.Uniform.advice_eq`, `NUPPT.Uniform.runAtL_eq`, `NUPPT.Uniform.runAt_eq`,
   `NUPPT.ofPolyTime_uniform` — uniform machines run on `⟨⟨⟨1^n, y⟩, []⟩, r⟩`.
 * `Complexity.NUPPT.polyTimeComputable_runAtL` — at a fixed parameter the activation is a
-  deterministic polynomial-time function of `(y, r)` (the "`A_n`" of the machine-sequence
-  form).
+  deterministic polynomial-time function of `(y, r)`, with constants that depend on `n` (not a
+  uniform size bound on the "`A_n`" of the machine-sequence form).
 * `Complexity.NUPPT.decides_of_decidesWithAdviceInTime` — (optional, sorried) a language
   decided with polynomial advice in polynomial time [AB09, Definition 6.16] is decided by an
   `NUPPT` at the input length.
@@ -115,10 +119,13 @@ theorem runLit_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeCom
       f (pairEncode (pairEncode (advInput y.length y) []) (List.ofFn r)) := by
   rw [runLit_eq_runAtL, runAtL_ofPolyTimeUniform]
 
-/-- **The machine-sequence view, sanity direction.** At a fixed parameter `n`, the activation
-of `A` is a deterministic polynomial-time function of the pair `⟨y, r⟩`: the "`A_n`" of
-[PS10, Definition 26.8]'s first formulation is a polynomial-size machine (the advice `advice n`
-and the prefix `1^n` are hard-wired constants).
+/-- **The machine-sequence view, sanity direction.** At each fixed parameter `n`, the
+activation of `A` is a deterministic polynomial-time function of the pair `⟨y, r⟩`
+[PS10, Definition 26.8, first formulation, the "`A_n`"]. The machine hard-wires `1^n` and
+`advice n`, so its size and its time constants depend on `n`: the statement is per `n` and
+would hold equally with exponentially long advice. It is **not** the polynomial-size half of
+Definition 26.8; that half comes from `|advice n| ≤ adv.eval n` (`NUPPT.advice_length`), not
+from this lemma.
 
 **Proof sketch.** The raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` is assembled from `⟨y, r⟩` by
 `PolyTimeComputable.pairEncode` with the constant strings `1^n` and `advice n`
diff --git a/TCSlib/Complexity/Randomized/PPT.lean b/TCSlib/Complexity/Randomized/PPT.lean
index e33b9fcd..2fdfe96c 100644
--- a/TCSlib/Complexity/Randomized/PPT.lean
+++ b/TCSlib/Complexity/Randomized/PPT.lean
@@ -37,9 +37,15 @@ convention of [PS10, Definition 23.5]; "`A` computes `f` with probability 1"
 [PS10, Definition 24.6] is `NUPPT.Computes`: equality for every coin string (on the finite
 uniform coin space, probability one is the same as every coin string, see
 `TCSlib.Cryptography.Asymptotic.Adversary`). A PPT [PS10, Definition 23.4] is an `NUPPT` with
-empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. The input-length-indexed
-activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the lemmas about it
-and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.
+empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does not require
+`Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
+`A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
+for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
+So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`; efficient computation is
+`∃ A, A.Uniform ∧ A.Computes f` (`NUPPT.exists_uniform_computes`, and conversely
+`NUPPT.Computes.polyTimeComputable` of `TCSlib.Complexity.Randomized.Closure`). The
+input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
+lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.
 
 ## Deviations (DESIGN.md §5, items 1–2)
 
@@ -60,10 +66,8 @@ the machine input" coincide.
 text indexes advice and coins by the input length (`A_{|x|}(x)`), while `NUPPT` indexes
 them by the parameter `n` read from the unary prefix `1^n`. The two are interdefinable in
 every experiment of the text: (i) an `NUPPT` run at `n := |y|` is exactly the text's
-`A_{|y|}(y)` (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information, so the
-input-length-indexed machine is obtained by ignoring it, see
-`Complexity.NUPPT.exists_reparam_advice` in `TCSlib.Complexity.Randomized.Closure` with
-`φ := length`); (ii) conversely, every experiment of the text hands the adversary strings
+`A_{|y|}(y)`, by definition (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information);
+(ii) conversely, every experiment of the text hands the adversary strings
 whose length is a fixed polynomial `ℓ(n)` of the parameter, and an input-length-indexed
 machine at length `ℓ(n)` becomes a `1^n`-indexed one by hard-wiring its advice at `ℓ(n)` and
 evaluating its coin polynomial at `ℓ(n)` (`exists_reparam_advice` with `φ := ℓ.eval`); for
@@ -82,7 +86,8 @@ one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unifie
 * `Complexity.NUPPT.advInput` — the adversary input `⟨1^n, y⟩`; `NUPPT.Coins` — the coin type
   at parameter `n`; `NUPPT.runAt`, `NUPPT.runAtL`, `NUPPT.runLit` — activations.
 * `Complexity.NUPPT.Uniform` — no advice (a PPT); `Complexity.PPT` — the subtype.
-* `Complexity.NUPPT.Computes` — computes `f` with probability one [PS10, Definition 24.6].
+* `Complexity.NUPPT.Computes` — computes `f` with probability one: [PS10, Definition 24.6] for a
+  uniform `A` (`NUPPT.Uniform`), the advice analogue otherwise.
 * `Complexity.NUPPT.ofPolyTime`, `Complexity.NUPPT.ofPolyTimeUniform` — the `NUPPT` with a
   given polynomial-time output function, with and without advice.
 
@@ -224,7 +229,16 @@ def Uniform : Prop := ∀ n, A.advice n = []
 /-- `A` computes `f` with probability one [PS10, Definition 24.6]: at every parameter `n`,
 on every argument `y` and for **every** coin string `r`, `A(1^n, y; r) = f(⟨1^n, y⟩)`. On
 the finite uniform coin space "probability one" is the same as "every coin string"
-(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`). -/
+(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`).
+
+The definition does not require `A.Uniform`. [PS10, Definition 24.6] is about a randomized
+algorithm, i.e. a PPT, and is the case `A.Uniform ∧ A.Computes f`. For a non-uniform `A` this
+is the advice analogue, which holds for uncomputable functions: with advice `[h n]` at
+parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice projection), `A`
+computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
+`f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
+(`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
+`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`). -/
 def Computes (f : List Bool → List Bool) : Prop :=
   ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
 
diff --git a/TCSlib/Complexity/Randomized/PolyExpr.lean b/TCSlib/Complexity/Randomized/PolyExpr.lean
index 94e3c7ec..8fb04d06 100644
--- a/TCSlib/Complexity/Randomized/PolyExpr.lean
+++ b/TCSlib/Complexity/Randomized/PolyExpr.lean
@@ -63,7 +63,13 @@ open Turing
 campaign (coins, advice, input/output lengths, query and round budgets) is one of these,
 never an abstract `ℕ → ℕ`. `normal C c` is the campaign normal form `C * (n + 1) ^ c`.
 [PS10, §2.1] writes such bounds as "a polynomial `p(n)`"; foundation decision D9 of
-`PassShelatChapter2-4Plan.md` fixes the syntactic representation. -/
+`PassShelatChapter2-4Plan.md` fixes the syntactic representation.
+
+Cost of D9: an expression is a polynomial with natural-number coefficients and no
+subtraction, so lengths such as `n − 1`, `⌊n/2⌋`, `n(n − 1)/2` or `⌈log₂ n⌉` are not
+expressible. A consumer pads to a `PolyExpr` majorant or reparametrizes with
+`Complexity.NUPPT.exists_reparam_advice` (an abstract `φ : ℕ → ℕ` with a `PolyExpr`
+majorant, the one place such a function appears). -/
 inductive PolyExpr : Type
   | const : ℕ → PolyExpr
   | var : PolyExpr
diff --git a/TCSlib/Complexity/Randomized/Repetition.lean b/TCSlib/Complexity/Randomized/Repetition.lean
index d129a30b..2674b05a 100644
--- a/TCSlib/Complexity/Randomized/Repetition.lean
+++ b/TCSlib/Complexity/Randomized/Repetition.lean
@@ -34,69 +34,50 @@ an adversary depends on it and on nothing else admitted, and the headline axiom
 (`audits/pass-shelat/Checks.lean`) list it by name if it is still open. The derived lemmas of
 this file are to be closed from it (or by small direct machines), so that the admission stays
 a single named one. **Status (run 3b):** `polyTimeComputable_iterateFind` is closed — its
-machine is built in `TCSlib.Complexity.Randomized.Build.IterateFindHost` (clean modules and
-the finite host) and `TCSlib.Complexity.Randomized.Build.IterateFind` (assembly through
+machine is built on the public clean-module host `TCSlib.Complexity.TuringMachine.Build.ModuleHost`
+(clean modules and the finite host), with its instance in
+`TCSlib.Complexity.Randomized.Build.IterateFindHost` (the copier and the host's control) and
+the assembly in `TCSlib.Complexity.Randomized.Build.IterateFind` (through
 `Turing.FinTM.exists_loopFindTM`), and its axiom print is `[propext, Classical.choice, Quot.sound]`.
-The six derived lemmas are closed too, as instances of one private **state-loop** form
+The six derived lemmas are closed too, as instances of one public **state-loop** form
 `polyTimeComputable_stateFind` of the repetition lemma (a state word `⟨x, s⟩` retaining the
 input, a step on the state, a test firing first at round `N x ≤ R|x|`, an output read off the
 final state), whose loop data, orbit closed forms and bounds live in
 `TCSlib.Complexity.Randomized.Build.StateLoop` (the form itself and the two iteration loops)
 and `TCSlib.Complexity.Randomized.Build.StringLoops` (the four string loops).
 
-**Construction plan of `iterateFind` (DESIGN.md §2.6, with the three panel repairs built in;
-the proof sketch of the theorem repeats it).**
-
-1. *State word carries the input.* `s0 x := ⟨x, x⟩` (second component: the current orbit
-   point). Loop data for `Turing.FinTM.exists_loopFindTM`: `stepF x w := guardedStep g P x w`
-   (**length-guarded**: `⟨x, g (snd w)⟩` if `|g (snd w)| ≤ P|x|`, else `w`),
-   `acceptF x w := acc (snd w)`, `out x w := out (snd w)`,
-   `Inv x w := fst w = x ∧ |snd w| ≤ P|x|` (`LoopInv`). `hInv0` is `pairDecode_pairEncode`
-   plus `horbit x 0`; `hInvStep` holds for every `w` because the guarded step leaves `w`
-   unchanged when the new point would be too long (`loopInv_guardedStep`). On the orbit
-   `i ≤ R|x|`, `horbit` shows the guard is never taken, so
-   `(stepF x)^[i] (s0 x) = ⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`) and the `find?` of the
-   conclusion is the statement's.
-2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
-   `C₁ := exists_installCallTM` for `w ↦ ⟨[acc (snd w)], w⟩` (the verdict as the first cell of
-   the installed word, `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed);
-   `C₂ := exists_installCallTM` for the guarded step on the pair (FP by
-   `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on `⟨1^{P|fst w|}, g (snd w)⟩`,
-   `polyTimeComputable_unaryPoly P`); `C₃ := exists_emitCallTM` for `w ↦ out (snd (snd w))`.
-   Each module promises first-visit-to-exit from the clean seam over an arbitrary native
-   input and `0 < C.k`.
-3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
-   tape counts equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean). The
-   anchor is the fresh state `inl ()`, whose transition is stationary into `C₁.entry` (no
-   module-internal state is the anchor). The module tables are copied with every transition
-   *targeting* `Cᵢ.exit` redirected to a fresh branch state `inr (inr k)`, so the module's own
-   table at `exit` is never consulted and `entry = exit` is harmless: the first positive visit
-   of `exit` promised by the contract is exactly the first entry into the branch state, with
-   the clean seam on the tapes. Branch states: after `C₁`, read tape-0 cell 0 — `true` →
-   `C₃.entry`, `false` → `C₂.entry`; after `C₂` → anchor (one stationary step); after `C₃` → halt.
-4. *`hstart`.* From `initCfg x`, install `s0 x = ⟨x, x⟩` on tape 0: one more
-   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
-   argument word `x`, which is first copied onto tape 0 by a one-state copy scan of the native
-   input plus `timed_rewind` (precedent: the startup phases of `computesFunInTime_splitSolveWith`).
-   No anchor visit before the seam.
-5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
-   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
-   clause: `C₃` to its first exit emitting `out (snd w)` and halt; advancing clause: `C₂` to
-   its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside the
-   round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch state).
-   Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
-   `Q n := 2n + 2 + P.eval n + 4` (the length of the state word), a normal-form majorant by
-   `PolyExpr.eval_le`.
-6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
-   `polyTimeComputable_unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?`
-   range must be exactly `R|x| + 1`: use the exact form).
-7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
-   `PolyTimeComputable`. `iterate` threads a unary counter in the state
-   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input); `iterateEmit`
-   threads an accumulator; the derived string functions are instances.
-
-Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
-`satStopTM`, `sat_run_agree` in `TCSlib.Complexity.ClassNP.SAT` (private copies, not edits).
+**Construction of `iterateFind`, as built (DESIGN.md §2.6, step 1, and its as-built erratum,
+which records the departures from the frozen steps 2–5).**
+
+1. *State word carries the input.* The loop state is `⟨x, s⟩` (`pairEncode x s`) from
+   `⟨x, x⟩`; the step is the length-guarded `guardedStep g P x`, which advances to `⟨x, g s⟩` if
+   the **new** point fits, `|g s| ≤ P|x|`, and otherwise leaves the word unchanged. On the
+   orbit, for `i ≤ R|x|`, the guard is never taken (`iterate_guardedStep_eq`), so the loop's
+   `find?` is the statement's (`acc_guardedStep_eq`). The pure invariant `LoopInv` is closed
+   under the step (`loopInv_guardedStep`); the machine uses the stronger actual-pair invariant
+   `∃ s, w = ⟨x, s⟩ ∧ |s| ≤ P|x|`, which bounds the word's length by `2|x| + 2 + P|x|`.
+2. *The machine.* `Complexity.IterateFind.polyTimeComputable_find`
+   (`TCSlib.Complexity.Randomized.Build.IterateFind`) is an instance of
+   `Turing.FinTM.exists_loopFindTM` with the guarded step `IterateFind.step`, the same function
+   as `guardedStep` (`IterateFind.step_eq`). Its loop body runs five clean modules in the public
+   clean-module host `Turing.ModuleHost.hostTM` (`TCSlib.Complexity.TuringMachine.Build.ModuleHost`,
+   host H14): the copier, which puts the native input on tape 0 (`IterateFind.copyTM`); the
+   startup install `x ↦ ⟨x, x⟩`; the verdict install `w ↦ ⟨[acc (snd w)], w⟩`; the step install;
+   and the payload emit `w ↦ out (snd (snd w))`. The installs and the emit come from
+   `Turing.ModuleHost.clean_install`/`clean_emit` (a clean-call bridge stopped by a release flag
+   and cut at its first halt). The host's control
+   (`TCSlib.Complexity.Randomized.Build.IterateFindHost`) has three fresh states: the anchor, which
+   dispatches into the verdict module; the branch, which reads the verdict cell of tape 0 and
+   dispatches into the payload or the step module; and the halt.
+3. *Budget and fuel.* Every request has length at most `2n + 6 + P n`, so every module's
+   polynomial budget, and that of the fuel machine `x ↦ Nat.bits (R|x|)`
+   (`polyTimeComputable_unaryPoly R` and `computesFunInTime_lengthBits`, so that the `find?` range
+   is exactly `R|x| + 1`), fit `T n = A·(2n + 7 + P n)^D`; the loop combinator's bound
+   `c (T n + 1)(R n + 2)` is put in normal form by `PolyExpr.eval_le`.
+4. *The derived lemmas* are instances of the state-loop form `polyTimeComputable_stateFind`,
+   which runs `iterateFind` on the guarded step `StateLoop.gstep` of a state word `⟨x, s⟩`:
+   `iterate` threads a unary counter, tested against `1^{R|x|}` by `IterLoop.acc` (`R|x| ≤ |cnt|`);
+   `iterateEmit` also threads an accumulator; the string functions consume their input.
 
 ## Main definitions
 
@@ -111,6 +92,8 @@ Estimated size 1 200–1 800 lines; private precedent for the module gluing: `sa
 * `Complexity.polyTimeComputable_iterate`, `Complexity.polyTimeComputable_iterateEmit` —
   `R(|x|)`-fold iteration and concatenated emissions (proved; state loops with a unary round
   counter).
+* `Complexity.polyTimeComputable_stateFind` — the state-loop form of the repetition lemma, of
+  which the six derived lemmas are instances (proved, from `polyTimeComputable_iterateFind`).
 * `Complexity.polyTimeComputable_majority`, `polyTimeComputable_pairXor`,
   `polyTimeComputable_pairEq`, `polyTimeComputable_blockMap` — string tests and the block
   map used by the reductions (proved; state loops consuming the input).
@@ -196,23 +179,14 @@ with first success [PS10, Theorem 35.1], the `n(2^k−1)` calls of Goldreich–L
 [PS10, Theorem 87.3], rejection sampling (D10), the truncated simulators
 [PS10, Algorithms 123.4 and 128.7] (inventory Inf-4.3).
 
-**Proof sketch.** Instance of `Turing.FinTM.exists_loopFindTM` (Loop.lean) with the data of the
-construction plan in the module docstring: (1) state word `⟨x, s⟩`, guarded step
-`guardedStep g P`, invariant `LoopInv P` (`loopInv_init`, `loopInv_guardedStep`), and on the
-orbit `(stepF x)^[i] ⟨x, x⟩ = ⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`), so the loop's `find?`
-over `List.range (R|x| + 1)` is the statement's (`acc_guardedStep_eq`); (2) the three
-clean-call modules `C₁` (verdict installed as the first cell), `C₂` (guarded step on the
-pair, FP by `polyTimeComputable_ite`, `polyTimeComputable_lenLe`,
-`polyTimeComputable_unaryPoly P`) and `C₃` (`out` of the orbit point, emitted) from
-`exists_installCallTM`/`exists_emitCallTM`; (3) the glued body with the fresh anchor
-`inl ()` and transitions into each `exit` redirected to fresh branch states; (4) `hstart` by a
-`pairDup` install module after a copy scan and `timed_rewind`; (5) `hround` with budget
-`T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)`, `Q n := 2n + 2 + P n + 4`, in normal
-form by `PolyExpr.eval_le`; (6) fuel `Nat.bits (R|x|)` by `polyTimeComputable_unaryPoly R`
-and `computesFunInTime_lengthBits`; (7) `exists_loopFindTM` returns a machine within
-`c (T n + 1)(R n + 2)`, packaged as `PolyTimeComputable`. Sub-obligations: the four modules,
-the gluing lemma (precedent: `satClean_install`/`sat_run_agree` in `ClassNP/SAT.lean`), the
-startup phase, the round budget arithmetic. -/
+**Proof sketch.** The machine is `Complexity.IterateFind.polyTimeComputable_find`
+(`TCSlib.Complexity.Randomized.Build.IterateFind`; its construction is in the module docstring):
+it computes `out` of the first accepted point, among the first `R|x| + 1`, of the orbit of
+`⟨x, x⟩` under the guarded step `IterateFind.step g P x`, which is `guardedStep g P x`
+(`IterateFind.step_eq`). Convert its conclusion to the statement's: for `i ≤ R|x|` the guarded
+orbit is `⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`), so the two `find?` predicates agree on the
+range (`acc_guardedStep_eq`, `IterateFind.find?_congr_of_mem`), and at the index found the
+payloads agree (`iterate_guardedStep_eq`, `pairSndD_pairEncode`). -/
 theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyTimeComputable g)
     {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
     {out : List Bool → List Bool} (hout : PolyTimeComputable out)
@@ -226,7 +200,10 @@ theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyT
   have h := IterateFind.polyTimeComputable_find hg hacc hout R P horbit
   convert h using 1
   funext x
-  have hstep : IterateFind.step g P x = guardedStep g P x := rfl
+  have hstep : IterateFind.step g P x = guardedStep g P x := by
+    funext w
+    rw [IterateFind.step_eq]
+    rfl
   have hfind : (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) =
       (List.range (R.eval x.length + 1)).find?
         (fun i => acc (pairSndD ((IterateFind.step g P x)^[i] (pairEncode x x)))) := by
@@ -261,7 +238,7 @@ the genuine orbit the guard never fires (`StateLoop.gstep_iterate_eq`, from the
 first `N x` states), so the loop's `find?` over `List.range (R|⟨x, start x⟩| + 1)` — a range
 containing `N x`, as `R` is monotone (`PolyExpr.eval_mono`) — returns `some (N x)`
 (`StateLoop.find?_range_eq_some`), and the payload is `out ⟨x, orbit x (N x)⟩`. -/
-private theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
+theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
     {acc : List Bool → Bool} {out : List Bool → List Bool}
     (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
     (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
@@ -319,19 +296,19 @@ theorem polyTimeComputable_iterate {g : List Bool → List Bool} (hg : PolyTimeC
       IterLoop.acc R (pairEncode x (orbit IterLoop.start (IterLoop.step g) x i)) = false := by
     intro x i hi
     rw [IterLoop.orbit_eq]
-    simp [IterLoop.acc, hi]
+    simp [IterLoop.acc_eq, hi]
   have hlast : ∀ x, IterLoop.acc R
       (pairEncode x (orbit IterLoop.start (IterLoop.step g) x (R.eval x.length))) = true := by
     intro x
     rw [IterLoop.orbit_eq]
-    simp [IterLoop.acc]
+    simp [IterLoop.acc_eq]
   have h := polyTimeComputable_stateFind IterLoop.start_poly (IterLoop.step_poly hg)
     (IterLoop.acc_poly R) IterLoop.out_poly R _ (fun x => R.eval x.length) (fun _ => le_rfl)
     hbound hfirst hlast
   convert h using 1
   funext x
   rw [IterLoop.orbit_eq]
-  simp [IterLoop.out]
+  simp [IterLoop.out_eq]
 
 /-- **Polynomially many iterations with concatenated emissions:** under the orbit bound,
 `x ↦ emit x ++ emit (g x) ++ ⋯ ++ emit (g^[R|x|] x)` is polynomial-time computable (the
@@ -375,19 +352,19 @@ theorem polyTimeComputable_iterateEmit {g emit : List Bool → List Bool}
       IterLoop.acc R (pairEncode x (orbit EmitLoop.start (EmitLoop.step g emit) x i)) = false := by
     intro x i hi
     rw [EmitLoop.orbit_eq]
-    simp [IterLoop.acc, hi]
+    simp [IterLoop.acc_eq, hi]
   have hlast : ∀ x, IterLoop.acc R (pairEncode x
       (orbit EmitLoop.start (EmitLoop.step g emit) x (R.eval x.length))) = true := by
     intro x
     rw [EmitLoop.orbit_eq]
-    simp [IterLoop.acc]
+    simp [IterLoop.acc_eq]
   have h := polyTimeComputable_stateFind EmitLoop.start_poly (EmitLoop.step_poly hg hemit)
     (IterLoop.acc_poly R) (EmitLoop.out_poly hemit) R _ (fun x => R.eval x.length)
     (fun _ => le_rfl) hbound hfirst hlast
   convert h using 1
   funext x
   rw [EmitLoop.orbit_eq]
-  simp [EmitLoop.out, List.range_succ]
+  simp [EmitLoop.out_eq, List.range_succ]
 
 /-- **Majority vote** on a bit string: `w ↦ [decide (|w| < 2 · #true w)]` (strict majority of
 `true`) is polynomial-time computable (the vote of the Goldreich–Levin inverter
@@ -431,7 +408,7 @@ theorem polyTimeComputable_pairXor :
   have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
     intro z
     have := length_pairFstD_add_pairSndD_le z
-    unfold XorLoop.rounds
+    rw [XorLoop.rounds_eq]
     simp only [PolyExpr.eval_var]
     omega
   have h := polyTimeComputable_stateFind XorLoop.start_poly XorLoop.step_poly XorLoop.acc_poly
@@ -461,7 +438,7 @@ theorem polyTimeComputable_pairEq :
   have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
     intro z
     have := length_pairFstD_add_pairSndD_le z
-    unfold XorLoop.rounds
+    rw [XorLoop.rounds_eq]
     simp only [PolyExpr.eval_var]
     omega
   have h := polyTimeComputable_stateFind XorLoop.start_poly EqLoop.step_poly XorLoop.acc_poly
@@ -478,11 +455,11 @@ mapped, a partial last block is dropped). This evaluates `prodFun f q` blockwise
 [PS10, Theorem 35.1, Algorithm 38.5] and decodes tuples of `n`-bit strings.
 
 **Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
-`Complexity.StateLoop.BlockLoop`) with `R := var` (at most `|z|` blocks) on the state
+`Complexity.StateLoop.BlockMapLoop`) with `R := var` (at most `|z|` blocks) on the state
 `⟨rest, c⟩` from `⟨snd z, []⟩`, with `k := b(|fst z|)` read off the retained input: each step
 drops `k` bits of `rest` and appends `g (rest.take k)` to `c` (`polyTimeComputable_pairDropPoly b`,
 `polyTimeComputable_pairTakePoly b` on `⟨fst z, rest⟩`), so after `i` rounds the state is
-`⟨(snd z).drop (i k), g (block 0) ++ ⋯ ++ g (block (i − 1))⟩` (`BlockLoop.orbit_eq`,
+`⟨(snd z).drop (i k), g (block 0) ++ ⋯ ++ g (block (i − 1))⟩` (`BlockMapLoop.orbit_eq`,
 `List.drop_drop`); `acc` is "`|rest| < k` or `k = 0`" (two length tests against `1^k`), `false`
 below round `|snd z| / k` and `true` there (`Nat.le_div_iff_mul_le`, `Nat.lt_mul_div_succ`),
 where `out` returns `c`, the statement's `flatMap`. States have length at most
@@ -493,16 +470,17 @@ theorem polyTimeComputable_blockMap (b : PolyExpr) {g : List Bool → List Bool}
       (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
         g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length)) := by
   obtain ⟨C, c, hC⟩ := hg.output_length_le
-  have hN : ∀ z, BlockLoop.rounds b z ≤ PolyExpr.var.eval z.length := by
+  have hN : ∀ z, BlockMapLoop.rounds b z ≤ PolyExpr.var.eval z.length := by
     intro z
     have := length_pairFstD_add_pairSndD_le z
+    rw [BlockMapLoop.rounds_eq]
     exact (Nat.div_le_self _ _).trans (by simp only [PolyExpr.eval_var]; omega)
-  have h := polyTimeComputable_stateFind BlockLoop.start_poly (BlockLoop.step_poly b hg)
-    (BlockLoop.acc_poly b) BlockLoop.out_poly .var _ (BlockLoop.rounds b) hN
-    (BlockLoop.orbit_length_le b g C c hC) (BlockLoop.acc_orbit_false b g)
-    (BlockLoop.acc_orbit_true b g)
+  have h := polyTimeComputable_stateFind BlockMapLoop.start_poly (BlockMapLoop.step_poly b hg)
+    (BlockMapLoop.acc_poly b) BlockMapLoop.out_poly .var _ (BlockMapLoop.rounds b) hN
+    (BlockMapLoop.orbit_length_le b g C c hC) (BlockMapLoop.acc_orbit_false b g)
+    (BlockMapLoop.acc_orbit_true b g)
   convert h using 1
   funext z
-  exact (BlockLoop.out_orbit b g z).symm
+  rw [BlockMapLoop.out_orbit, BlockMapLoop.rounds_eq]
 
 end Complexity
diff --git a/TCSlib/Cryptography/Asymptotic/Adversary.lean b/TCSlib/Cryptography/Asymptotic/Adversary.lean
index 5ca92cbd..174e38fb 100644
--- a/TCSlib/Cryptography/Asymptotic/Adversary.lean
+++ b/TCSlib/Cryptography/Asymptotic/Adversary.lean
@@ -97,7 +97,15 @@ theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x
   simp [padFin]
 
 /-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
-[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`]. -/
+[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].
+
+**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
+a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
+another length, so the typed experiment can count fewer successes and typed one-wayness is
+implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
+with non-constant output length; with constant output length neither notion is
+satisfiable). The proviso is stated where string functions enter the typed world,
+`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
 def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
     (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
   fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)
diff --git a/TCSlib/Cryptography/Asymptotic/Ensembles.lean b/TCSlib/Cryptography/Asymptotic/Ensembles.lean
index b60c501a..e5b14f80 100644
--- a/TCSlib/Cryptography/Asymptotic/Ensembles.lean
+++ b/TCSlib/Cryptography/Asymptotic/Ensembles.lean
@@ -3,7 +3,12 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
-import TCSlib.Complexity.Randomized
+import TCSlib.Complexity.Randomized.Closure
+-- `NonUniform` is not used here. It replaces, for downstream files, the former import of the
+-- facade `TCSlib.Complexity.Randomized`: `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean`
+-- uses `NUPPT.Uniform.advice_eq` and reaches `NonUniform` only through this file (gate 03a,
+-- finding 12). Drop it once that file imports `NonUniform` itself.
+import TCSlib.Complexity.Randomized.NonUniform
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
 import TCSlib.Cryptography.Asymptotic.Sampling
@@ -34,7 +39,8 @@ uniform bits whose output law is exactly `X n` (`StatClose … 0`). The headline
 Definition 69.4 gives the distinguisher the input `1^n` (`Ensemble.Indist`, D5); the literal
 form `Ensemble.IndistLit` (the distinguisher receives the sample `t` only, activation at
 parameter `|t| = ℓ n`) is stated next to it with the bridges `Indist.toLit` and
-`IndistLit.toIndist` (injective `ℓ`), never unified silently.
+`IndistLit.toIndist` (injective, i.e. non-constant, `ℓ`; for constant `ℓ` the two forms
+coincide as well, by point tests, which is not formalized), never unified silently.
 
 Every asymptotic statement is proved by instantiating a concrete reduction of
 `TCSlib.Cryptography.Pseudorandom.Indistinguishability` [Gar26, §3.2] at each `n`, exhibiting
@@ -44,7 +50,8 @@ the reduction as a `Complexity.NUPPT` by the closure catalogue of
 `not_negligible_iff_exists_polyExpr`).
 
 **Deviation:** `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n`
-(literal form `IndistLit`, equivalent for injective `ℓ`).
+(literal form `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the
+constant case by point tests, not formalized).
 
 The machine constructions and the probability bookkeeping behind the proofs (the negated,
 padded-image and multicopy reductions as `NUPPT`s, coin-splitting bijections, the exactness
@@ -109,9 +116,12 @@ at each `n` a sampler `X n` from a finite seed type `σ n` (uniformly distribute
 the `ℓ(n)`-bit strings, the distribution `X_n` being the pushforward of the uniform seed. The
 length `ℓ` is a syntactic polynomial (D9).
 
-**Deviation:** every distribution is dyadic (a pushforward of uniform seeds); the text allows
-arbitrary distributions over `{0,1}^*`, but every ensemble of chapters 3 and 4 is of this form
-and the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
+**Deviation:** each `X_n` is the pushforward of the uniform distribution on a finite nonempty
+seed set, so its probabilities are rational (not necessarily dyadic: seeds `Fin 3` give mass
+`1/3`; the efficiently samplable ensembles, `Samplable`, are the dyadic ones, D6), and it lives
+on strings of the fixed length `ℓ(n)` that Definition 69.4 requires (Definition 69.3 allows
+arbitrary distributions over `{0,1}^*`). Every ensemble of chapters 3 and 4 is of this form;
+the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
 experiments, approximated by the rejection samplers of `Asymptotic/Sampling.lean` (D6, D10).
 
 **Repair (run-3 audit P2-2):** the field `nonempty` was added to the frozen structure of
@@ -144,8 +154,8 @@ def uniform (ℓ : PolyExpr) : Ensemble ℓ where
 /-- **Efficiently samplable** ensemble (distribution level, D6): there is a syntactic
 polynomial `s` and a polynomial-time sampler `S` such that at every `n` the law of
 `S(⟨1^n, r⟩)` for `s(n)` uniform bits `r` (padded or truncated to `ℓ(n)` bits) is exactly the
-law of `X n` (`StatClose … 0`). This is the "efficiently sample from the ensemble" of
-[PS10, p. 72 (Example) and Lemma 71.6's multicopy corollary]. -/
+law of `X n` (`StatClose … 0`). This is the "efficiently sample" of [PS10, p. 72, Example];
+the multicopy lemma that assumes it is [Gar26, Lemma 3.3] (`Indist.copies`). -/
 def Samplable (X : Ensemble ℓ) : Prop :=
   ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
     ∀ n, StatClose (fun r : Fin (s.eval n) → Bool =>
@@ -176,7 +186,10 @@ def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)
 /-- The image ensemble `{M(X_n)}` of [PS10, Lemma 71.5]: at parameter `n`, draw a seed of `X`
 and coins for `M`, run `M(1^n, X_n)` and pad or truncate the output to `ℓ'(n)` bits. The
 output length `ℓ'` is an explicit syntactic polynomial so that the padding is itself
-polynomial-time (`polyTimeComputable_unaryPoly`). -/
+polynomial-time (`polyTimeComputable_unaryPoly`). The padding (`padFin`: `false`-padding or
+truncation) is lossless when `M` outputs exactly `ℓ'(n)` bits, the only case Definition 69.4
+can type, and lossy otherwise (`[1]` and `[1, 0]` both pad to `[1, 0, …]`): variable-length
+outputs (ciphertexts, views, transcripts) are not ensembles of this kind. -/
 def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
   σ n := X.σ n × M.Coins n
   X n z := padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)
@@ -227,14 +240,6 @@ def Ensemble.DistinguishesWith {ℓ : PolyExpr} (X Y : Ensemble ℓ) (D : NUPPT)
     Prop :=
   ∀ n, Distinguishes (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) (μ n)
 
-/-- The constant zero is negligible. -/
-theorem negligible_zero : Negligible fun _ : ℕ => (0 : ℝ) := by
-  intro c
-  refine ⟨1, fun n hn => ?_⟩
-  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
-  simp only [abs_zero]
-  positivity
-
 /-- The text's form of Definition 69.4 — "there exists a negligible `ε` with advantage
 `< ε(n)` for all `n`" — is equivalent to the frozen form "the advantage is negligible"
 [PS10, Definition 69.4]: the advantage lies in `[0, 1]`, so one direction is `Negligible.mono`
@@ -341,6 +346,13 @@ theorem Ensemble.Indist.toLit {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indis
 the text): if `{X_n} ≈ {Y_n}` against literal distinguishers, then also against distinguishers
 receiving `1^n` [PS10, Definition 69.4; D5].
 
+The hypothesis `hℓ` excludes only constant `ℓ`: a `PolyExpr` has natural-number coefficients,
+so `ℓ.eval` is constant or strictly increasing. For constant `ℓ ≡ L` the two forms coincide as
+well (not formalized, no consumer): the `2^L` point tests `t ↦ [t = t₀]` are advice-free
+literal distinguishers, so `IndistLit` makes `Σ_{t₀} |Pr[X_n = t₀] − Pr[Y_n = t₀]|`, hence the
+statistical distance of `X_n` and `Y_n`, negligible, and that bounds every distinguisher
+(`distAdv_le_of_statClose`). So D5's "`D` receives `1^n`" costs nothing for ensembles.
+
 **Proof sketch.** `ℓ.eval` is monotone (`PolyExpr.eval_mono`) and injective, hence strictly
 increasing, so `n ≤ ℓ n` for all `n`. Let `φ m := n` if `m = ℓ n` (`Classical.choose` of the
 preimage, unique by injectivity) and `φ m := 0` off the image; then `φ m ≤ m`, so
@@ -387,7 +399,7 @@ non-uniform PPT `M` (and every explicit output length `ℓ'`), `{M(X_n)} ≈ {M(
 `combineAdvice (M.advice n) (D.advice n)`, built as `NUPPT.ofPolyTime` of a raw function of
 the layout `⟨⟨⟨1^n, t⟩, α⟩, r⟩` as in `NUPPT.exists_seq`) runs `M` on `t` with the first
 `M.coins n` coins, pads the result to `ℓ'(n)` bits *inside the layout*, where `1^n` is
-available (run-3 audit note P2-4: `NUPPT.exists_comp` sees only `y`; the padding is
+available (`NUPPT.exists_comp` sees only `y`, gate 03a finding 3; the padding is
 `EnsembleLemmas.polyTimeComputable_padL`, a typed cut `pairTakePoly ℓ'` of the output
 followed by `0^{ℓ'(n)}`), and hands it to `D` with the remaining coins. Its distinguisher at
 `n` is the concrete `sunglassRed P (D.distinguisher n (ℓ' n))` with
@@ -411,7 +423,9 @@ theorem Ensemble.Indist.push {ℓ ℓ' : PolyExpr} {X Y : Ensemble ℓ} (h : X.I
 `X^m` with advantage `ε` then some consecutive pair `X^i, X^{i+1}` (`i < m`) is distinguished
 by `D` with advantage at least `ε / m`. (The text indexes `X^1, …, X^m` and loses the factor
 `m` where `m − 1` steps would do; harmless.) This is the concrete `exists_hybrid_gap` applied to
-the acceptance probabilities `g_i = Pr[t ← X^i : D(t) = 1]`. -/
+the acceptance probabilities `g_i = Pr[t ← X^i : D(t) = 1]`. All hybrids share one seed type
+`σ` (`X : ℕ → σ → γ`); hybrids with seeds of different shapes are first embedded into a
+common product seed. -/
 theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
     (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
     ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
@@ -439,6 +453,12 @@ theorem Ensemble.Indist.trans {ℓ : PolyExpr} {X Y Z : Ensemble ℓ} (h₁ : X.
 samplable, then `t(n)` independent copies remain indistinguishable for every syntactic
 polynomial `t`.
 
+The samplability hypotheses are those of [Gar26, Lemma 3.3]'s uniform reduction, which
+samples the other copies (D6). Against non-uniform distinguishers they can be dropped: hard-wire
+the hybrid index and the other `t(n) − 1` copies that keep the gap as advice
+(`NUPPT.exists_withAdvice`). That form is not proved, since no consumer needs copies of a
+non-samplable ensemble (gate 03a, finding 2).
+
 **Proof sketch.** Fix a distinguisher `D` of the `t(n)`-fold products. At each `n` with
 `t(n) > 0`, `exists_multicopyRed_ge` (through the block bijection `blocks`) gives a hybrid
 index `k_n < t(n)` such that the concrete reduction `multicopyRed (X.X n) (Y.X n) (t n) k_n D'`
@@ -670,7 +690,10 @@ independent bits `X_1, …, X_m`, each `true` with probability `p`, and `ε > 0`
 
 **Deviation:** the text states the inequality for real random variables with `|X_i| ≤ 1` and
 mean `μ` with the bound `(1 − μ²)/(m ε²)`; here the variables are bits (the only case used in
-the campaign) and the bound is the variance bound `p(1−p) ≤ 1/4` of the concrete layer. -/
+the campaign) and the bound is the variance bound `p(1−p) ≤ 1/4` of the concrete layer. Bits
+satisfy the text's hypothesis, and `1/4 > 1 − p²` exactly when `p > √3/2`, so for such `p`
+this bound is weaker than the text's (at `p = 1` the text gives `0`); the variance form
+`p(1−p)/(m ε²)` would imply both. -/
 theorem pairwise_sampling_ineq {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
     {X : ι → Ω → Bool} (hX : HardcoreBit.PairwiseIndep X) {p : ℝ}
     (hp : ∀ i, uprob (fun ω => X i ω = true) = p) {ε : ℝ} (hε : 0 < ε)
diff --git a/TCSlib/Cryptography/Asymptotic/Sampling.lean b/TCSlib/Cryptography/Asymptotic/Sampling.lean
index d25fae40..614318c8 100644
--- a/TCSlib/Cryptography/Asymptotic/Sampling.lean
+++ b/TCSlib/Cryptography/Asymptotic/Sampling.lean
@@ -88,8 +88,9 @@ added for the permutation sampler, whose section moved to `Asymptotic/Permutatio
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-  (§2.4.2 Theorem 35.1; §2.6.5 Lemma 51.17; §2.12 Corollary 60.6 and Theorem 63.10;
-  §4.4–§4.6 Protocols 120.6 and 127.5 for the permutation sampler of `Asymptotic/Permutations.lean`.)
+  (Definition 181.1, `ε`-closeness; §2.4.2 Theorem 35.1; §2.6.5 Lemma 51.17; §2.12
+  Corollary 60.6 and Theorem 63.10; §4.4–§4.6 Protocols 120.6 and 127.5 for the permutation
+  sampler of `Asymptotic/Permutations.lean`.)
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
   draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
 -/
@@ -102,10 +103,19 @@ open Finset
 
 /-- Two samplers `X : σ → γ` and `Y : τ → γ` from uniform seeds are *statistically
 `δ`-close* when every test set `T ⊆ γ` has probabilities under the two sampled laws differing
-by at most `δ`: the sup-over-test-sets form of the statistical distance, usable for samples in
-an infinite type such as `List Bool`. The device of foundation decision D10: experiments use
-ideal distributions, samplers approximate them within `StatClose` error
-[PS10, §2.4.2 (the uniform position of Theorem 35.1), §4.3 (statistical zero-knowledge)]. -/
+by at most `δ`: the `ε`-closeness of [PS10, Definition 181.1] ("for every (deterministic)
+distinguisher `D` (with no time bound), `|Pr[D(x) = 1] − Pr[D(y) = 1]| ≤ ε`"), in its
+sup-over-test-sets form, usable for samples in an infinite type such as `List Bool`; on a
+finite sample space, with nonempty seed types, it is exactly `EpsClose` of the two laws
+(`statClose_iff_epsClose_map`, `Asymptotic/SamplingFinDist.lean`). The device of foundation
+decision D10: experiments use ideal distributions, samplers approximate them within
+`StatClose` error [PS10, §2.4.2 (the uniform position of Theorem 35.1), §4.3 (statistical
+zero-knowledge)].
+
+The seed types are not required to be nonempty. On an empty seed type every probability is
+`0` (`uprob`), so the "law" of an empty-seeded sampler is the zero measure and
+`StatClose X Y 0` fails as soon as `Y` has seeds; every use has nonempty seeds
+(`Ensemble.nonempty`, machine coins `Fin k → Bool`, the `[Nonempty σ]` of `SamplingFinDist`). -/
 def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
   ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
 
diff --git a/TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean b/TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean
index 3a619deb..c5e5d131 100644
--- a/TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean
+++ b/TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean
@@ -1,10 +1,12 @@
 /-
 Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
+Authors: TCSlib contributors
 -/
 import TCSlib.Cryptography.Asymptotic.Sampling
 import TCSlib.InformationTheory.Extractors
 
+set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
 set_option autoImplicit false
 
@@ -18,6 +20,10 @@ between two finite distributions by distinguishers (`EpsClose`,
 On a finite sample space the two agree: two samplers are `δ`-close exactly when the laws they push
 the uniform seed distribution to are `δ`-close. This closes duplication-ledger item DL-4.
 
+## Main definitions
+
+None.
+
 ## Main results
 
 * `uprob_comp_eq_probTrue_map`: the probability that a test accepts a sample is its acceptance
diff --git a/TCSlib/Cryptography/Foundations/Negligible.lean b/TCSlib/Cryptography/Foundations/Negligible.lean
index a006f767..9cec03b1 100644
--- a/TCSlib/Cryptography/Foundations/Negligible.lean
+++ b/TCSlib/Cryptography/Foundations/Negligible.lean
@@ -33,7 +33,7 @@ differences of probabilities can be fed in directly. [Gar26] restricts to values
 
 * `Negligible.add`, `Negligible.mul`, `Negligible.const_mul`, `Negligible.mono`: closure.
 * `Negligible.mul_pow`: a negligible function times a polynomial is negligible.
-* `negligible_two_pow_neg`: `2^{-n}` is negligible.
+* `negligible_two_pow_neg`: `2^{-n}` is negligible; `negligible_zero`: so is the constant `0`.
 * `Noticeable.not_negligible`: noticeable functions are not negligible.
 * `not_negligible_sub`: a non-negligible function minus a negligible one is
   non-negligible.
@@ -157,6 +157,17 @@ theorem negligible_two_pow_neg : Negligible (fun n => (2 : ℝ)⁻¹ ^ n) := by
   rw [abs_of_pos (by positivity), inv_pow, ← one_div]
   exact one_div_lt_one_div_of_lt (pow_pos (by linarith) c) hlt
 
+/-- The constant zero function is negligible: `|0| = 0 < 1 / n^c` for every `n ≥ 1`. Technical
+glue (the advantage of a distinguisher between two equal distributions). Added by the
+Pass–shelat campaign (gate 03a, ruling G3-7a), which moved it here from
+`Asymptotic/Ensembles.lean` under its unchanged full name. -/
+theorem negligible_zero : Negligible fun _ : ℕ => (0 : ℝ) := by
+  intro c
+  refine ⟨1, fun n hn => ?_⟩
+  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
+  simp only [abs_zero]
+  positivity
+
 /-- A noticeable function is not negligible. [Gar26, §1.2].
 
 **Proof sketch.** With the noticeability exponent `c`, at any `n` past both thresholds

### --- B1: the 03a repair commit e8f45ca3ca7246d1379c4b66ce5a7a72d0b2d820, outside this pack's files ---
diff --git a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
index 54ad6508..dc8fbb52 100644
--- a/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/EnsemblesLemmas.lean
@@ -3,7 +3,8 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
-import TCSlib.Complexity.Randomized
+import TCSlib.Complexity.Randomized.Closure
+import TCSlib.Complexity.Randomized.Repetition
 import TCSlib.Cryptography.Asymptotic.Adversary
 import TCSlib.Cryptography.Asymptotic.Sampling
 import TCSlib.Cryptography.Foundations.Negligible
diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index edb8e719..d4b35d6f 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -193,7 +193,17 @@ structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where
 def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ := (f (List.replicate n false)).length
 
 /-- The textbook `f : {0,1}* → {0,1}*` with the output length `p`: parameter = input length,
-the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`). -/
+the output padded or truncated to `p(n)` bits (exact when `f` is `LengthRegular f p`).
+
+Inversion is typed (D5, `NUPPT.inverter`): an inverter of `ofString f p` at parameter `n` must
+return a preimage of length `n`, while [PS10, Definition 27.3] accepts a preimage of any
+length. The two experiments agree when `f` is length-regular with non-constant `p` (then
+`|f(x)|` determines `|x|`); with constant `p` neither notion is satisfiable. Otherwise the typed
+notion can be strictly weaker: for a length-preserving one-way `g`, the function
+`f(0^k ‖ w) := w` (`|w| = k`), `f(x) := g(x)` elsewhere is inverted with probability one by
+`y ↦ 0^{|y|} ‖ y` in the text's experiment, while in the typed one every inverter succeeds
+with probability at most its inversion probability against `g` plus `2^{-n/2}` (gate 03a,
+note 15). -/
 def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily where
   inLen := .var
   outLen := p
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 01a9d640..767d14fe 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -3,7 +3,9 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: TCSlib contributors
 -/
-import TCSlib.Complexity.Randomized
+import TCSlib.Complexity.Randomized.Closure
+import TCSlib.Complexity.Randomized.NonUniform
+import TCSlib.Complexity.Randomized.Repetition
 import TCSlib.Cryptography.Candidates.Arithmetic
 import TCSlib.Cryptography.Candidates.Concrete
 import TCSlib.Cryptography.Asymptotic.Collections
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index db0e077b..d479fa0a 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -11,6 +11,10 @@ import TCSlib.Cryptography.NumberTheory
 import TCSlib.Cryptography.Candidates
 import TCSlib.Cryptography.ZeroKnowledge
 
+set_option maxHeartbeats 0
+set_option relaxedAutoImplicit false
+set_option autoImplicit false
+
 /-!
 # Pass–shelat Chapters 2–4 verification (run 2, statement phase)
 
@@ -18,6 +22,20 @@ Axiom prints for the sanity theorems and for every headline theorem of the campa
 (every theorem whose name corresponds to a numbered result of [PS10]). In the statement
 phase most headlines are sorried under their proof sketches and print `sorryAx`; proved
 results must print exactly `[propext, Classical.choice, Quot.sound]`.
+
+## Main definitions
+
+* `PassShelatChecks.zeros` — the constant ensemble `{0^{ℓ(n)}}` (gate 03a, note 21).
+
+## Main results
+
+* `PassShelatChecks.not_indist_uniform_zeros` — non-vacuity of `Ensemble.Indist`: `{U_n}` and
+  `{0^n}` are distinguishable (gate 03a, note 21).
+
+## References
+
+* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
+  (Definition 69.4, computational indistinguishability.)
 -/
 
 -- ## Sanity theorems (plan §6, workstream A)
@@ -392,3 +410,105 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.not_weakOneWay_id
 #print axioms TCSlib.Cryptography.not_worstCaseOneWay_id
 #print axioms TCSlib.Cryptography.FunFamily.not_toCollection_oneWay_id
+
+-- ## Gate 03a repairs (pack 03a: machines and probability)
+-- Note 19: interface lemmas that had no axiom print.
+#print axioms TCSlib.Cryptography.statClose_iff_epsClose_map
+#print axioms Complexity.NUPPT.computes_iff_uprob
+#print axioms Complexity.NUPPT.Computes.polyTimeComputable
+#print axioms Complexity.NUPPT.exists_uniform_computes
+#print axioms TCSlib.Cryptography.Ensemble.uniform_samplable
+#print axioms TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible
+#print axioms TCSlib.Cryptography.invProbOpt_le_invProb
+#print axioms TCSlib.Cryptography.invProbOpt_some
+#print axioms TCSlib.Cryptography.statClose_firstHit
+#print axioms TCSlib.Cryptography.pushesUniform_of_card_fiber
+#print axioms TCSlib.Cryptography.pairwise_sampling_ineq
+-- Ruling G3-7a: `negligible_zero` now lives in `Foundations/Negligible.lean` (name unchanged).
+#print axioms TCSlib.Cryptography.negligible_zero
+
+-- Note 21: `Ensemble.Indist` can fail (the distinguisher semantics is not trivial).
+namespace PassShelatChecks
+
+open TCSlib.Cryptography Complexity Turing
+
+/-- The constant ensemble `{0^{ℓ(n)}}`: one seed, the all-`false` string. -/
+def zeros (ℓ : PolyExpr) : Ensemble ℓ where
+  σ _ := Unit
+  X _ _ := fun _ => false
+
+/-- A uniformly random bit string of positive length has its first bit set with probability
+`1/2`: flipping that bit is a bijection that exchanges the event and its complement. -/
+theorem uprob_first_bit (m : ℕ) :
+    uprob (fun t : Fin (m + 1) → Bool => t 0 = true) = 1 / 2 := by
+  have hinv : Function.Involutive fun t : Fin (m + 1) → Bool => Function.update t 0 (!t 0) := by
+    intro t
+    funext j
+    by_cases hj : j = 0
+    · subst hj
+      simp
+    · simp [hj]
+  have h := uprob_comp_equiv hinv.toPerm (fun t : Fin (m + 1) → Bool => t 0 = true)
+  have hne : (fun t : Fin (m + 1) → Bool => hinv.toPerm _ t 0 = true) =
+      fun t => ¬ (t 0 = true) := by
+    funext t
+    simp [Function.Involutive.coe_toPerm]
+  rw [hne, uprob_not] at h
+  linarith
+
+/-- **Non-vacuity of `Ensemble.Indist`** [PS10, Definition 69.4] (gate 03a, note 21): the
+uniform ensemble `{U_n}` is not indistinguishable from the constant ensemble `{0^n}`.
+
+**Proof sketch.** The distinguisher `D` outputs the first bit of its sample: it is
+`ofPolyTimeUniform` of `polyTimeComputable_pairTakePoly` with the constant cut `1` applied to
+the slot `⟨1^n, t⟩` of the raw layout, so `D(1^n, t) = t.take 1`. At every `n = m + 1` it
+accepts `U_n` with probability `1/2` (`uprob_fst`, `uprob_first_bit`) and `0^n` never
+(`uprob_false`), so its advantage is `1/2`. Negligibility with exponent `1` would give
+`1/2 < 1/n` for all large `n`, false at any `n ≥ 2`. -/
+theorem not_indist_uniform_zeros : ¬ (Ensemble.uniform .var).Indist (zeros .var) := by
+  intro h
+  have hF : PolyTimeComputable fun z =>
+      (pairSndD (pairFstD (pairFstD z))).take
+        ((PolyExpr.const 1).eval (pairFstD (pairFstD (pairFstD z))).length) :=
+    (polyTimeComputable_pairTakePoly (.const 1)).comp
+      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
+  let D := NUPPT.ofPolyTimeUniform hF (.const 0)
+  have hrun : ∀ n (y : List Bool) (r : D.Coins n), D.runAt n y r = y.take 1 := by
+    intro n y r
+    rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
+    simp [NUPPT.advInput]
+  have hacc : ∀ m (t : Fin (m + 1) → Bool) (r : D.Coins (m + 1)),
+      D.distinguisher (m + 1) (m + 1) t r = t 0 := by
+    intro m t r
+    simp only [NUPPT.distinguisher, hrun, List.ofFn_succ]
+    cases t 0 <;> simp
+  have hadv : ∀ m, distAdv ((Ensemble.uniform .var).X (m + 1)) ((zeros .var).X (m + 1))
+      (D.distinguisher (m + 1) ((PolyExpr.var).eval (m + 1))) = 1 / 2 := by
+    intro m
+    have hU : acceptProb ((Ensemble.uniform .var).X (m + 1))
+        (D.distinguisher (m + 1) ((PolyExpr.var).eval (m + 1))) = 1 / 2 := by
+      show uprob (fun z : (Fin (m + 1) → Bool) × D.Coins (m + 1) =>
+        D.distinguisher (m + 1) (m + 1) z.1 z.2 = true) = 1 / 2
+      simp only [hacc]
+      exact (uprob_fst (fun t : Fin (m + 1) → Bool => t 0 = true)).trans (uprob_first_bit m)
+    have hZ : acceptProb ((zeros .var).X (m + 1))
+        (D.distinguisher (m + 1) ((PolyExpr.var).eval (m + 1))) = 0 := by
+      show uprob (fun z : Unit × D.Coins (m + 1) =>
+        D.distinguisher (m + 1) (m + 1) (fun _ => false) z.2 = true) = 0
+      simp only [hacc, Bool.false_eq_true]
+      exact uprob_false
+    rw [distAdv, hU, hZ]
+    norm_num
+  obtain ⟨n₀, hn₀⟩ := h D 1
+  have hlt := hn₀ (max n₀ 2 - 1 + 1) (by omega)
+  simp only at hlt
+  rw [hadv] at hlt
+  have h2 : (2 : ℝ) ≤ ((max n₀ 2 - 1 + 1 : ℕ) : ℝ) := by
+    exact_mod_cast (show 2 ≤ max n₀ 2 - 1 + 1 by omega)
+  rw [abs_of_pos (by norm_num), pow_one] at hlt
+  have : 1 / ((max n₀ 2 - 1 + 1 : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
+  linarith
+
+end PassShelatChecks
+
+#print axioms PassShelatChecks.not_indist_uniform_zeros
diff --git a/briefs/pass-shelat/DESIGN.md b/briefs/pass-shelat/DESIGN.md
index 65a36662..755283ac 100644
--- a/briefs/pass-shelat/DESIGN.md
+++ b/briefs/pass-shelat/DESIGN.md
@@ -44,7 +44,11 @@ D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim
     `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
     the two new machine lemmas of D11, (iii) negligible-function arithmetic through
     `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
-    frozen Garg files.
+    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
+    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
+    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
+    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
+    (ruling G3-5).
 
 D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
     `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
@@ -57,7 +61,10 @@ D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
     `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
     random tape is part of the input, the time bound holds for every coin string
     ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
-    is `Computes`: equality for every coin string. Honest evaluators ("easy to compute") are
+    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
+    24.6 proper is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
+    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
+    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
     stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
     totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
     inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
@@ -86,7 +93,9 @@ D5. **Domains are typed at each parameter.** A function family is
     Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
     `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
     form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
-    (injective `ℓ`, i.e. every ensemble of the text). The two are never unified silently.
+    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
+    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
+    unified silently.
 
 D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
     with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
@@ -160,6 +169,12 @@ D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
     audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
     (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
     show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
+    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
+    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
+    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
+    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
+    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
+    question 5, ruled outside the core on 2026-10-27).
 
 ---
 
@@ -977,7 +992,8 @@ Issues found in this synthesis and resolved here (not raised by the panel):
    computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
 4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
 5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
-   `IndistLit`, equivalent for injective `ℓ`).
+   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
+   by point tests, not formalized; gate 03a, note 14).
 6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
    rejection-sampled position (statistical term absorbed).
 7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
@@ -1245,7 +1261,9 @@ message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (h
 5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
    (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
    admission each; confirm they are out of the mandatory core (they are not needed by any
-   chapter 2–4 theorem).
+   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
+   The one admission in this area is the optional bridge
+   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
 6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
    are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
    scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
diff --git a/briefs/pass-shelat/inventory-ch2.md b/briefs/pass-shelat/inventory-ch2.md
index c8b22cde..a512d310 100644
--- a/briefs/pass-shelat/inventory-ch2.md
+++ b/briefs/pass-shelat/inventory-ch2.md
@@ -252,7 +252,7 @@ Full paths of the existing declarations cited below:
 
 **Rem-22.1 (§2.1.1 hard problems).** (i) Halting is uncomputable; (ii) the time hierarchy gives functions computable in exponential but not polynomial time; (iii) SAT is NP-complete, conjectured not in P. — Existing: `Complexity.HALT_not_computable` (relative to an `EffectiveMachineCode`), `Complexity.P_ssubset_EXP`, `Complexity.SAT_NPComplete`. Cite only.
 
-**Def-23.4 (PPT).** A randomized algorithm is a TM with an extra random tape of uniform independent bits. **Formal (D3):** a structure with a `FinTM Bool` `M`, coin-length constants `(Cr, cr)` and time constants `(Ct, ct)` such that for every `x : List Bool` and every `r : Fin (Cr·(|x|+1)^cr) → Bool`, `M` halts on `pairEncode x (ofFn r)` within `Ct·(|x|+1)^ct` steps; `M.run x r` is its completed output; `M(x)` is the sampler `r ↦ M.run x r` (a `(Fin ℓ → Bool) → List Bool`, directly usable by `uprob`). Deviation: coins are an input component (reading a random tape sequentially is a bounded-cost simulation), and the coin length is an explicit polynomial. — Existing pattern: `FinTM.DecidesWithAdviceInTime` (pair input, time in `|x|`). New file `TCSlib/Complexity/Randomized/PPT.lean`. Difficulty 3 (definition + run/sampler API + basic lemmas `run_eq_of_computesInTime`, determinism via `ComputesInTime.output_unique`).
+**Def-23.4 (PPT).** *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* A randomized algorithm is a TM with an extra random tape of uniform independent bits. **Formal (D3):** a structure with a `FinTM Bool` `M`, coin-length constants `(Cr, cr)` and time constants `(Ct, ct)` such that for every `x : List Bool` and every `r : Fin (Cr·(|x|+1)^cr) → Bool`, `M` halts on `pairEncode x (ofFn r)` within `Ct·(|x|+1)^ct` steps; `M.run x r` is its completed output; `M(x)` is the sampler `r ↦ M.run x r` (a `(Fin ℓ → Bool) → List Bool`, directly usable by `uprob`). Deviation: coins are an input component (reading a random tape sequentially is a bounded-cost simulation), and the coin length is an explicit polynomial. — Existing pattern: `FinTM.DecidesWithAdviceInTime` (pair input, time in `|x|`). New file `TCSlib/Complexity/Randomized/PPT.lean`. Difficulty 3 (definition + run/sampler API + basic lemmas `run_eq_of_computesInTime`, determinism via `ComputesInTime.output_unique`).
 
 **Def-23.5 (Running time, randomized).** `A` runs in time `T` if for all `x` and *every* random tape, `A(x)` halts within `T(|x|)` steps (worst case over coins). — Folded into Def-23.4's time clause (the clause quantifies over all `r`). Expected polynomial time is not formalized (plan D8).
 
@@ -262,7 +262,7 @@ Full paths of the existing declarations cited below:
 
 **Def-24.7 (Efficient private-key encryption).** `(Gen, Enc, Dec)` are PPTs; `Gen(1^n)` outputs a key `k`; `Enc_k(m)` for `m ∈ {0,1}^n` outputs `c`; `Dec_k(c)` outputs `m ∈ {0,1}^n ∪ {⊥}`; for all `n` and `m ∈ {0,1}^n`, `Pr[k ← Gen(1^n) : Dec_k(Enc_k(m)) = m] = 1` (over the coins of `Gen` and `Enc`). **Formal:** messages `Fin n → Bool`; keys/ciphertexts `List Bool`; `Enc`/`Dec` receive `pairEncode 1^n (pairEncode k m)` (so their polynomial bounds are in `n`; the text says "polynomial in the size of their inputs" — with `|k| ≤ poly(n)` the two readings agree); `Dec` output decoded as an `n`-bit string or `⊥`. Correctness quantifies over all coin strings (Def-24.6 reading). Asymptotic/Encryption.lean (plan). Difficulty 2. Depends on Def-23.4.
 
-**Def-26.8 (nuPPT).** A sequence `{A_i}` of probabilistic machines with `|A_i| < d(i)` and running time `< d(i)` for a polynomial `d`; `A(x)` runs `A_{|x|}(x)`. Equivalently (text): a uniform PPT with a polynomial-length advice string per input length. **Formal (D4):** a PPT `M` plus `α : ℕ → List Bool` with `|α n| ≤ Ca·(n+1)^ca`, run on `pairEncode (pairEncode x (α |x|)) r`, time `Ct·(|x|+1)^ct` for every `r`. Deviation: the machine-sequence formulation is not formalized. — Existing pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly`. New file `TCSlib/Complexity/Randomized/NonUniform.lean`. Difficulty 3. Note the standing convention "any adversarial algorithm is implicitly nuPPT" (p. 26) governs Defs 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and Assumptions 30.1, 52.2, 53.1.
+**Def-26.8 (nuPPT).** *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* A sequence `{A_i}` of probabilistic machines with `|A_i| < d(i)` and running time `< d(i)` for a polynomial `d`; `A(x)` runs `A_{|x|}(x)`. Equivalently (text): a uniform PPT with a polynomial-length advice string per input length. **Formal (D4):** a PPT `M` plus `α : ℕ → List Bool` with `|α n| ≤ Ca·(n+1)^ca`, run on `pairEncode (pairEncode x (α |x|)) r`, time `Ct·(|x|+1)^ct` for every `r`. Deviation: the machine-sequence formulation is not formalized. — Existing pattern: `FinTM.DecidesWithAdviceInTime`, `Complexity.PAdvicePoly`. New file `TCSlib/Complexity/Randomized/NonUniform.lean`. Difficulty 3. Note the standing convention "any adversarial algorithm is implicitly nuPPT" (p. 26) governs Defs 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and Assumptions 30.1, 52.2, 53.1.
 
 **Rem-26.2 (equivalence of nuPPT formulations).** Deferred (difficulty 4): `⇒` would use `Turing.timed_universal` with the description `A_{|x|}` as advice; `⇐` hard-wires the advice. Not needed downstream under D4.
 
diff --git a/briefs/pass-shelat/inventory-ch3.md b/briefs/pass-shelat/inventory-ch3.md
index 1730a3a1..d405ce53 100644
--- a/briefs/pass-shelat/inventory-ch3.md
+++ b/briefs/pass-shelat/inventory-ch3.md
@@ -35,7 +35,7 @@ Run 1 (understand & design), 2026-10-27. Source: `blueprint/src/references/pass-
 | Label | Meaning | Where it will live |
 | --- | --- | --- |
 | `Machine-PPT` | D3: `PPT` structure, run/sampler semantics `run M n : (Fin (coins n) → Bool) → List Bool`, `ComputesFun` (same output for every coin string), typed decoding of outputs (`List Bool` → `Fin m → Bool`, wrong length = failure/`false`) | `TCSlib/Complexity/Randomized/PPT.lean` |
-| `Machine-NUPPT` | D4: nuPPT = PPT + advice `α n` of length `Cα (n+1)^cα`, run on `pairEncode (pairEncode x (α |x|)) r`; Boolean output `decide (out = [true])` | `Randomized/NonUniform.lean` |
+| `Machine-NUPPT` | *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* D4: nuPPT = PPT + advice `α n` of length `Cα (n+1)^cα`, run on `pairEncode (pairEncode x (α |x|)) r`; Boolean output `decide (out = [true])` | `Randomized/NonUniform.lean` |
 | `Machine-Closure` | pre/post-composition with a PPT, pairing of inputs, hard-wiring a per-`n` constant (index `i`, message `m_n`, sign bit) into advice, drawing extra coins, a PPT is an nuPPT | `Randomized/Closure.lean` |
 | `Machine-Repetition` | polynomially many calls of an nuPPT with fresh coins and a post-processing (majority, list, XOR) — the load-bearing lemma for GL, DL, multi-message | `Randomized/Repetition.lean` |
 | `Machine-Loop` | iterate a PPT-computable function `poly(n)` times (PRG expansion, GGM evaluation, Shamir/Blum–Micali) | `Randomized/Repetition.lean` (or Closure) |
@@ -192,7 +192,7 @@ unbounded distinguisher (membership in the image of `G`) has advantage `≥ 1/2`
 distinguisher; `acceptProb` on `G` is `1`, on `U_m` is `|image|/2^m ≤ 2^{n−m}`). Optional,
 difficulty 2. (The text argues via Shannon's theorem from ch. 1; the pigeonhole form is simpler.)
 
-**Def-69.3** — *Ensemble.* A sequence `{X_n}` with `X_n` a distribution over `{0,1}^*`. D6 reading:
+**Def-69.3** — *Ensemble.* *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* A sequence `{X_n}` with `X_n` a distribution over `{0,1}^*`. D6 reading:
 `structure Ensemble` with `seedLen outLen : ℕ → ℕ` (explicit `C(n+1)^c` formulas, or at least
 `PolyBound`) and `sample n : (Fin (seedLen n) → Bool) → (Fin (outLen n) → Bool)`; the distribution
 `X_n` is the pushforward of uniform seeds (dyadic). `Samplable X` := the sampler family is computed
@@ -201,7 +201,7 @@ arbitrary distributions over `{0,1}^*`; the text's own ensembles are all of this
 DDH/El Gamal ones that sample primes and `Z_q` — see Asm-105.1).
 Reuse: samplers `σ → γ` of `Foundations/Experiments.lean` are the one-`n` slices.
 
-**Def-69.4** — *Computational indistinguishability.* `X ≈ Y` iff for every nuPPT `D` there is a
+**Def-69.4** — *Computational indistinguishability.* *[Superseded by DESIGN D3–D6 (gate 03a, note 23): the frozen form is in `DESIGN.md` §1–§2 and the Lean files.]* `X ≈ Y` iff for every nuPPT `D` there is a
 negligible `ε` with `|Pr[t ← X_n : D(t)=1] − Pr[t ← Y_n : D(t)=1]| < ε(n)` for all `n`. Formal:
 `CompIndist X Y := ∀ D : NUPPT, Negligible (fun n => distAdv (X.sample n) (Y.sample n) (D.dist n))`
 where `D.dist n : (Fin (outLen n) → Bool) → (Fin (coins n) → Bool) → Bool` runs the machine on

### --- B2: #203's item H commit 43e8fe2c27c54c2c50e01541024995e95c6bf6fa, outside this pack's files ---
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 15941575..61fb0276 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -465,6 +465,8 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.pairwise_sampling_ineq
 -- Ruling G3-7a: `negligible_zero` now lives in `Foundations/Negligible.lean` (name unchanged).
 #print axioms TCSlib.Cryptography.negligible_zero
+-- Finding 3: the parameter-aware closure under pre- and post-processing.
+#print axioms Complexity.NUPPT.exists_compParam
 
 -- Note 21: `Ensemble.Indist` can fail (the distinguisher semantics is not trivial).
 namespace PassShelatChecks

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/a2/replay.log =====

# closure of pack 03a2's files at e28773ef3bda6f7b4b112ec1657427bfef01e374: 64 modules, extracted from replay-combined2.log
TCSlib/Complexity/CircuitComplexity/Advice rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Basic rc=0 8s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuit rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGFanin rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGTransform rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredCircuit rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredDAG rc=0 6s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LayeredPPoly rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/PPoly rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/SizeClasses rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/TreeDAG rc=0 5s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTime rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassNP/PolyTimePairing rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/DTIME rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassP/P rc=0 2s errors=0 sorry=0
TCSlib/Complexity/ClassP/TimeConstructible rc=0 2s errors=0 sorry=2
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/PairSplit rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StateLoop rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/StringLoops rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/UnaryMul rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Complexity/Randomized/PPT rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/PolyExpr rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primitives rc=0 1s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Convention rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Embed rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Loop rc=0 50s errors=0 sorry=5
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 3s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Build/Primitives rc=0 54s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Build/Wrappers rc=0 4s errors=0 sorry=2
TCSlib/Complexity/TuringMachine/Composition rc=0 3s errors=0 sorry=3
TCSlib/Complexity/TuringMachine/Configuration rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Deterministic rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Encoding rc=0 3s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/Finite rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction rc=0 5s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Robustness/SingleTape rc=0 11s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Simulation rc=0 6s errors=0 sorry=1
TCSlib/Complexity/TuringMachine/StateRenaming rc=0 2s errors=0 sorry=0
TCSlib/Complexity/TuringMachine/Sweep rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Sampling rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/SamplingFinDist rc=0 1s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Negligible rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Foundations/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/HardcoreBit/PairwiseIndependence rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/OneWayFunctions/Basic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Generators rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Indistinguishability rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/Entropy rc=0 2s errors=0 sorry=0
TCSlib/InformationTheory/Extractors rc=0 2s errors=0 sorry=0
TCSlib/InformationTheory/FinDist rc=0 3s errors=0 sorry=0
TCSlib/InformationTheory/LeftoverHash rc=0 2s errors=0 sorry=0
TCSlib/InformationTheory/StatisticalDistance rc=0 2s errors=0 sorry=0
TCSlib/InformationTheory/UniversalHashing rc=0 2s errors=0 sorry=0

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/a2/axioms.log =====

# axiom prints of every public theorem and lemma for declarations in pack 03a2's files, at e28773ef3bda6f7b4b112ec1657427bfef01e374
Complexity.PolyExpr.eval_const: propext
Complexity.PolyExpr.eval_var: propext
Complexity.PolyExpr.eval_add: propext
Complexity.PolyExpr.eval_mul: propext
Complexity.PolyExpr.eval_pow: propext
Complexity.PolyExpr.eval_normal: propext
Complexity.PolyExpr.eval_subst: propext
Complexity.PolyExpr.subst_var: propext
Complexity.PolyExpr.eval_mono: propext
Complexity.PolyExpr.eval_le: propext, Classical.choice, Quot.sound
Complexity.PolyExpr.polyBound_eval: propext, Classical.choice, Quot.sound
Complexity.PolyExpr.exists_normal_ge: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_unaryNormal: propext, Classical.choice, Quot.sound
Complexity.NUPPT.output_spec: propext, Classical.choice, Quot.sound
Complexity.NUPPT.computesFunInTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_output: propext, Classical.choice, Quot.sound
Complexity.NUPPT.output_eq_of_computesInTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.output_length_le: propext, Classical.choice, Quot.sound
Complexity.NUPPT.length_advInput: propext, Quot.sound
Complexity.NUPPT.runAt_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.Computes.runAt_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.output_ofPolyTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.coins_ofPolyTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.adv_ofPolyTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.advice_ofPolyTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.runAtL_ofPolyTime: propext, Classical.choice, Quot.sound
Complexity.NUPPT.ofPolyTimeUniform_uniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.output_ofPolyTimeUniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.coins_ofPolyTimeUniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.runAtL_ofPolyTimeUniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_uniform_computes: propext, Classical.choice, Quot.sound
Complexity.NUPPT.nonempty: propext, Classical.choice, Quot.sound
Complexity.PPT.nonempty: propext, Classical.choice, Quot.sound
Turing.FinTM.computesFunInTime_pairSplitAt: propext, Classical.choice, Quot.sound
Turing.FinTM.computesFunInTime_unaryMul: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_unaryPoly: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_pairTakePoly: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_pairDropPoly: propext, Classical.choice, Quot.sound
Complexity.NUPPT.inParam_layout: propext, Quot.sound
Complexity.NUPPT.inArg_layout: propext, Quot.sound
Complexity.NUPPT.inAdvice_layout: propext, Quot.sound
Complexity.NUPPT.inCoins_layout: propext, Quot.sound
Complexity.NUPPT.runAtL_eq_output_layout: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_inParam: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_inArg: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_inAdvice: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_inCoins: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_layout: propext, Classical.choice, Quot.sound
Complexity.NUPPT.pairFstD_combineAdvice: propext, Quot.sound
Complexity.NUPPT.pairSndD_combineAdvice: propext, Quot.sound
Complexity.NUPPT.combineAdvice_nil: propext
Complexity.NUPPT.length_combineAdvice_le: propext, Quot.sound
Complexity.NUPPT.exists_compParam: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_comp: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_reparam: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_reparam_advice: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_withAdvice: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_split: propext, Classical.choice, Quot.sound
Complexity.NUPPT.exists_seq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.Computes.polyTimeComputable: propext, Classical.choice, Quot.sound
Complexity.loopInv_init: propext, Quot.sound
Complexity.loopInv_guardedStep: propext, Quot.sound
Complexity.iterate_guardedStep_eq: propext, Quot.sound
Complexity.acc_guardedStep_eq: propext, Quot.sound
Complexity.polyTimeComputable_iterateFind: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_stateFind: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_iterate: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_iterateEmit: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_majority: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_pairXor: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_pairEq: propext, Classical.choice, Quot.sound
Complexity.polyTimeComputable_blockMap: propext, Classical.choice, Quot.sound
Complexity.NUPPT.runLit_eq_runAt: propext, Classical.choice, Quot.sound
Complexity.NUPPT.runLit_eq_runAtL: propext, Classical.choice, Quot.sound
Complexity.NUPPT.Uniform.advice_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.Uniform.runAtL_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.Uniform.runAt_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.ofPolyTime_uniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.uniform_iff: propext, Classical.choice, Quot.sound
Complexity.NUPPT.runLit_ofPolyTimeUniform: propext, Classical.choice, Quot.sound
Complexity.NUPPT.polyTimeComputable_runAtL: propext, Classical.choice, Quot.sound
Complexity.NUPPT.decides_of_decidesWithAdviceInTime: propext,  sorryAx,  Classical.choice,  Quot.sound
Complexity.PPT.uniform: propext, Classical.choice, Quot.sound
Complexity.PPT.toNUPPT_ofPolyTime: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.decodeFin_ofFn: propext, Quot.sound
TCSlib.Cryptography.length_eq_of_decodeFin_eq_some: propext
TCSlib.Cryptography.padFin_ofFn: propext, Quot.sound
Complexity.NUPPT.inverterLit_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.distinguisher_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.predictor_eq: propext, Classical.choice, Quot.sound
Complexity.NUPPT.inverter_eq_some_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProbOpt_le_invProb: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProbOpt_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProbOpt_nonneg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.invProbOpt_le_one: propext, Classical.choice, Quot.sound
Complexity.NUPPT.computes_iff_uprob: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.abs_uprob_sub_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.uprob_le_add: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.nonneg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.refl: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.symm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.mono: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.trans: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.map: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.comp_equiv_left: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.comp_equiv_right: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_of_pushesUniform: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.comp_pushesUniform: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.abs_uprob_sub_le_prod: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.distAdv_le_of_statClose: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.StatClose.prod: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.pushesUniform_of_card_fiber: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.card_fiber_eq_of_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.pushesUniform_of_card_fiber_le: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.bitsToNat_lt: propext, Quot.sound
TCSlib.Cryptography.bitsToNat_injective: propext, Quot.sound
TCSlib.Cryptography.bitsEquiv_val: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_bitsToNat_lt: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uniformFromBits_eq_some_iff: propext
TCSlib.Cryptography.uniformFromBits_eq_none_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_uniformFromBits_eq_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_uniformFromBits_none: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_comp_eq_sum_fiber: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.firstHit_eq_none_iff: propext, Quot.sound
TCSlib.Cryptography.firstHit_eq_some_imp: propext, Quot.sound
TCSlib.Cryptography.uprob_firstHit_none: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.firstHit_uniform_of_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_firstHit: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.rejectionSample_eq_none_iff: propext, Quot.sound
TCSlib.Cryptography.map_rejectionSample_eq_firstHit: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.rejectionSample_uniform_of_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_rejectionSample_none: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_rejectionSample_none_le_half_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.one_sub_inv_pow_le_half: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_rejectionSample: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_getD_of_uniform_of_some: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.copies_X: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.uniform_samplable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.indist_iff_exists_negligible: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.not_negligible_iff_exists_polyExpr: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.refl: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.symm: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.toLit: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.IndistLit.toIndist: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.push: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.hybrid_lemma: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.trans: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Ensemble.Indist.copies: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.predict_eq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.prediction_lemma: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.pairwise_sampling_ineq: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.mono: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.add: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.mul_pow: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Negligible.const_mul: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_two_pow_neg: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.negligible_zero: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.Noticeable.not_negligible: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.not_negligible_iff: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.not_negligible_sub: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.exists_not_negligible_not_noticeable: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.uprob_comp_eq_probTrue_map: propext, Classical.choice, Quot.sound
TCSlib.Cryptography.statClose_iff_epsClose_map: propext, Classical.choice, Quot.sound

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/a2/admissions.txt =====

# declarations with `sorry` in pack 03a2's files, at e28773ef3bda6f7b4b112ec1657427bfef01e374
TCSlib/Complexity/Randomized/NonUniform.lean:160 Complexity.NUPPT.decides_of_decidesWithAdviceInTime

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/a2/lint.log =====

# scripts/style_lint.py on pack 03a2's files, at e28773ef3bda6f7b4b112ec1657427bfef01e374












0 findings in 11 files

## ===== TCSlib/Complexity/Randomized/PolyExpr.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Syntactic polynomials for lengths and budgets

Every length or budget of the Pass–shelat campaign that depends on the security parameter
`n` — the number of coins and of advice bits of a machine, the input and output lengths of
function families and ensembles, the stretch of a generator, query and round budgets,
auxiliary-input bounds — is a *syntactic* polynomial expression `Complexity.PolyExpr`
(constants, the variable, sums, products, powers), never an abstract function `ℕ → ℕ`
with a bound. This is foundation decision D9 of `PassShelatChapter2-4Plan.md`: an abstract
length function can smuggle undecidable information through length arithmetic (the audit
lesson recorded in `TCSlib.Complexity.ClassNP.NP`), while a syntactic expression is
evaluated, substituted, bounded and computed in unary by structural recursion.

Time bounds of machines stay in the normal form `C * (n + 1) ^ c` of
`Complexity.PolyTimeComputable`; `PolyExpr.normal C c` is that normal form as an
expression, and `PolyExpr.eval_le` shows that every expression is majorised by one.

The unary evaluator `x ↦ 1^{p(|x|)}` (`Complexity.polyTimeComputable_unaryPoly`) lives in
`TCSlib.Complexity.Randomized.Primitives`, next to the unary-multiplication machine its
`mul` case needs; the normal-form instance `Complexity.polyTimeComputable_unaryNormal` is
proved here from the library's `Complexity.polyTimeComputable_polyUnary`.

## Main definitions

* `Complexity.PolyExpr` — syntactic polynomial expressions in the parameter `n`.
* `Complexity.PolyExpr.eval` — evaluation at a parameter.
* `Complexity.PolyExpr.subst` — substitution `p[q/n]` (parameter changes `n ↦ q(n)`).
* `Complexity.PolyExpr.normal` — the normal form `C * (n + 1) ^ c` as an expression.

## Main results

* `Complexity.PolyExpr.eval_subst` — evaluation commutes with substitution.
* `Complexity.PolyExpr.eval_mono` — evaluation is monotone in the parameter.
* `Complexity.PolyExpr.eval_le`, `Complexity.PolyExpr.polyBound_eval` — every expression is
  bounded by a normal form `C * (n + 1) ^ c` (the bridge to `Complexity.PolyBound`).
* `Complexity.polyTimeComputable_unaryNormal` — `x ↦ 1^{C(|x|+1)^c}` is polynomial-time
  computable (the normal-form case of the unary evaluator).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: polynomials `p(n)` as running-time, coin and advice bounds.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, the function class FP.)
-/

namespace Complexity

open Turing

/-- Syntactic polynomial expressions in the security parameter `n`: every length of the
campaign (coins, advice, input/output lengths, query and round budgets) is one of these,
never an abstract `ℕ → ℕ`. `normal C c` is the campaign normal form `C * (n + 1) ^ c`.
[PS10, §2.1] writes such bounds as "a polynomial `p(n)`"; foundation decision D9 of
`PassShelatChapter2-4Plan.md` fixes the syntactic representation.

Cost of D9: an expression is a polynomial with natural-number coefficients and no
subtraction, so lengths such as `n − 1`, `⌊n/2⌋`, `n(n − 1)/2` or `⌈log₂ n⌉` are not
expressible. A consumer pads to a `PolyExpr` majorant or reparametrizes with
`Complexity.NUPPT.exists_reparam_advice` (an abstract `φ : ℕ → ℕ` with a `PolyExpr`
majorant, the one place such a function appears). -/
inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr

/-- Evaluation of a syntactic polynomial at the parameter `n`, by structural recursion. -/
def eval : PolyExpr → ℕ → ℕ
  | const c, _ => c
  | var, n => n
  | add p q, n => p.eval n + q.eval n
  | mul p q, n => p.eval n * q.eval n
  | pow p c, n => (p.eval n) ^ c

/-- Substitution `p[q/n]`: the expression `p` with every occurrence of the variable
replaced by `q` (parameter changes `n ↦ q(n)`, e.g. the coin polynomial of a machine run
at parameter `p(n)` is `coins.subst p`). -/
def subst : PolyExpr → PolyExpr → PolyExpr
  | const c, _ => const c
  | var, q => q
  | add p p', q => add (p.subst q) (p'.subst q)
  | mul p p', q => mul (p.subst q) (p'.subst q)
  | pow p c, q => pow (p.subst q) c

/-- The campaign normal form `C * (n + 1) ^ c` as a syntactic polynomial: the shape of the
time bounds of `Complexity.PolyTimeComputable`. -/
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)

/-- Evaluating a constant. -/
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl

/-- Evaluating the variable. -/
@[simp] theorem eval_var (n : ℕ) : var.eval n = n := rfl

/-- Evaluating a sum. -/
@[simp] theorem eval_add (p q : PolyExpr) (n : ℕ) : (add p q).eval n = p.eval n + q.eval n := rfl

/-- Evaluating a product. -/
@[simp] theorem eval_mul (p q : PolyExpr) (n : ℕ) : (mul p q).eval n = p.eval n * q.eval n := rfl

/-- Evaluating a power. -/
@[simp] theorem eval_pow (p : PolyExpr) (c n : ℕ) : (pow p c).eval n = (p.eval n) ^ c := rfl

/-- The normal form evaluates to `C * (n + 1) ^ c`. -/
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl

/-- Evaluation commutes with substitution: `(p[q/n])(n) = p(q(n))`. -/
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n) := by
  induction p <;> simp_all [subst, eval]

/-- Substituting the variable itself is the identity. -/
theorem subst_var (p : PolyExpr) : p.subst var = p := by
  induction p <;> simp_all [subst]

/-- Evaluation is monotone in the parameter (every coefficient is a natural number). -/
theorem eval_mono (p : PolyExpr) : Monotone p.eval := by
  induction p with
  | const k => intro a b _; exact le_rfl
  | var => intro a b h; exact h
  | add p q hp hq => intro a b h; exact Nat.add_le_add (hp h) (hq h)
  | mul p q hp hq => intro a b h; exact Nat.mul_le_mul (hp h) (hq h)
  | pow p k hp => intro a b h; exact Nat.pow_le_pow_left (hp h) k

/-- Every expression is bounded by a normal form `C * (n + 1) ^ c`: the bridge from syntactic
polynomials to the time bounds of `Complexity.PolyTimeComputable` and to
`Complexity.PolyBound`.

**Proof sketch.** Induction on `p`. Constants and the variable are their own majorants
(`k * (n+1)^0`, `1 * (n+1)^1`). For a sum, raise both degrees to their maximum
(`Nat.pow_le_pow_right`) and add the coefficients; for a product, multiply the coefficients
and add the degrees; for a power, raise the coefficient and multiply the degree
(`Nat.pow_le_pow_left`, `mul_pow`, `pow_mul`). -/
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c := by
  induction p with
  | const k => exact ⟨k, 0, fun n => by simp⟩
  | var => exact ⟨1, 1, fun n => by simp⟩
  | add p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max c₁ c₂, fun n => ?_⟩
    have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_left _ _)
    have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ (max c₁ c₂) :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right _ _)
    calc (add p q).eval n = p.eval n + q.eval n := rfl
      _ ≤ C₁ * (n + 1) ^ c₁ + C₂ * (n + 1) ^ c₂ := Nat.add_le_add (h₁ n) (h₂ n)
      _ ≤ C₁ * (n + 1) ^ (max c₁ c₂) + C₂ * (n + 1) ^ (max c₁ c₂) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
      _ = (C₁ + C₂) * (n + 1) ^ (max c₁ c₂) := by ring
  | mul p q hp hq =>
    obtain ⟨C₁, c₁, h₁⟩ := hp
    obtain ⟨C₂, c₂, h₂⟩ := hq
    refine ⟨C₁ * C₂, c₁ + c₂, fun n => ?_⟩
    calc (mul p q).eval n = p.eval n * q.eval n := rfl
      _ ≤ (C₁ * (n + 1) ^ c₁) * (C₂ * (n + 1) ^ c₂) := Nat.mul_le_mul (h₁ n) (h₂ n)
      _ = (C₁ * C₂) * (n + 1) ^ (c₁ + c₂) := by ring
  | pow p k hp =>
    obtain ⟨C, c, h⟩ := hp
    refine ⟨C ^ k, c * k, fun n => ?_⟩
    calc (pow p k).eval n = (p.eval n) ^ k := rfl
      _ ≤ (C * (n + 1) ^ c) ^ k := Nat.pow_le_pow_left (h n) k
      _ = C ^ k * (n + 1) ^ (c * k) := by rw [mul_pow, ← pow_mul]

/-- The evaluation of a syntactic polynomial is a `Complexity.PolyBound` (the library's
numerical majorant predicate), by `eval_le`. -/
theorem polyBound_eval (p : PolyExpr) : PolyBound p.eval := p.eval_le

/-- A syntactic polynomial is bounded by its own normal-form majorant *as an expression*:
there are `C, c` with `p.eval n ≤ (normal C c).eval n` for every `n`. -/
theorem exists_normal_ge (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ (normal C c).eval n := by
  obtain ⟨C, c, h⟩ := p.eval_le
  exact ⟨C, c, fun n => by rw [eval_normal]; exact h n⟩

end PolyExpr

/-- The unary evaluator of a normal form is polynomial-time: `x ↦ 1^{C(|x|+1)^c}`, i.e.
`x ↦ 1^{(normal C c)(|x|)}`, is polynomial-time computable (the library's
`Complexity.polyTimeComputable_polyUnary`, restated on `PolyExpr.normal`). This is the
case of `Complexity.polyTimeComputable_unaryPoly` that needs no unary multiplication. -/
theorem polyTimeComputable_unaryNormal (C c : ℕ) :
    PolyTimeComputable fun x => List.replicate ((PolyExpr.normal C c).eval x.length) true :=
  polyTimeComputable_polyUnary C c

end Complexity

## ===== TCSlib/Complexity/Randomized/PPT.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic polynomial-time machines, uniform and non-uniform

The randomized machine model of [PS10, §2.1]: the probabilistic polynomial-time Turing
machine (PPT) [PS10, Definition 23.4] with the worst-case running-time convention
[PS10, Definition 23.5], the notion "computes `f` with probability one"
[PS10, Definition 24.6], and the non-uniform PPT of [PS10, Definition 26.8] in its advice
formulation ("a uniform p.p.t. machine `A` that receives an advice string for each input
length"). One structure, `Complexity.NUPPT`, carries all of them (foundation decisions D3
and D4 of `PassShelatChapter2-4Plan.md`):

* a finite binary machine `M : Turing.FinTM Bool` that halts on **every** input `z` within
  `Ct * (|z| + 1) ^ ct` steps;
* an explicit coin polynomial `coins : PolyExpr` (`coins.eval n` uniform coins at parameter
  `n`) and an advice polynomial `adv : PolyExpr` with an advice function `advice : ℕ → List Bool`
  of length `≤ adv.eval n`;
* the single semantic primitive `output z` (the output tape when the budget expires), which is
  `PolyTimeComputable` (`NUPPT.polyTimeComputable_output`), and conversely every
  `PolyTimeComputable` function is the output of some `NUPPT` (`NUPPT.ofPolyTime`).

The activation at security parameter `n` on argument `y` with coins `r` is
`runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`
(pairs are `Turing.pairEncode`, `1^n = List.replicate n true`). The random tape is part of the
input, so the time bound holds for every coin string, which is exactly the worst-case
convention of [PS10, Definition 23.5]; "`A` computes `f` with probability 1"
[PS10, Definition 24.6] is `NUPPT.Computes`: equality for every coin string (on the finite
uniform coin space, probability one is the same as every coin string, see
`TCSlib.Cryptography.Asymptotic.Adversary`). A PPT [PS10, Definition 23.4] is an `NUPPT` with
empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does not require
`Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
`A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`; efficient computation is
`∃ A, A.Uniform ∧ A.Computes f` (`NUPPT.exists_uniform_computes`, and conversely
`NUPPT.Computes.polyTimeComputable` of `TCSlib.Complexity.Randomized.Closure`). The
input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.

## Deviations (DESIGN.md §5, items 1–2)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional
   module).

In detail (D3): a machine that is polynomial-time on well-formed inputs can be clocked by
`Turing.timed_universal` into one that halts on every input, so requiring totality does not
change the class of behaviours (the optional lemma `NUPPT.ofPartial` doing this is not needed
by any theorem of chapters 2–4); the time bound is measured in the length of the machine
input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`, a polynomial in `n + |y|`, so the classes "polynomial in
`n`" (for `|y|` polynomial in `n`, the only case the experiments produce) and "polynomial in
the machine input" coincide.

**Interdefinability of the `1^n`-indexed and the input-length-indexed forms (D3/D4).** The
text indexes advice and coins by the input length (`A_{|x|}(x)`), while `NUPPT` indexes
them by the parameter `n` read from the unary prefix `1^n`. The two are interdefinable in
every experiment of the text: (i) an `NUPPT` run at `n := |y|` is exactly the text's
`A_{|y|}(y)`, by definition (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information);
(ii) conversely, every experiment of the text hands the adversary strings
whose length is a fixed polynomial `ℓ(n)` of the parameter, and an input-length-indexed
machine at length `ℓ(n)` becomes a `1^n`-indexed one by hard-wiring its advice at `ℓ(n)` and
evaluating its coin polynomial at `ℓ(n)` (`exists_reparam_advice` with `φ := ℓ.eval`); for
injective `ℓ` the converse hard-wires `1^n` into the advice at length `ℓ(n)`. The `1^n`
indexing is what makes one random tape per `n` well-typed for the oracle and interactive
layouts of chapters 3–4, where the machine is activated several times at one parameter on
inputs of varying length. Both forms are kept side by side where the text uses the literal
one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unified silently.

## Main definitions

* `Complexity.NUPPT` — non-uniform PPT [PS10, Definition 26.8, advice formulation]; a PPT
  [PS10, Definition 23.4] is the case `NUPPT.Uniform` (empty advice).
* `Complexity.NUPPT.output` — the output of the machine on a raw input (the semantic
  primitive); `NUPPT.timeBound`, `NUPPT.coinLen`, `NUPPT.adviceLen`.
* `Complexity.NUPPT.advInput` — the adversary input `⟨1^n, y⟩`; `NUPPT.Coins` — the coin type
  at parameter `n`; `NUPPT.runAt`, `NUPPT.runAtL`, `NUPPT.runLit` — activations.
* `Complexity.NUPPT.Uniform` — no advice (a PPT); `Complexity.PPT` — the subtype.
* `Complexity.NUPPT.Computes` — computes `f` with probability one: [PS10, Definition 24.6] for a
  uniform `A` (`NUPPT.Uniform`), the advice analogue otherwise.
* `Complexity.NUPPT.ofPolyTime`, `Complexity.NUPPT.ofPolyTimeUniform` — the `NUPPT` with a
  given polynomial-time output function, with and without advice.

## Main results

* `Complexity.NUPPT.output_spec`, `NUPPT.computesFunInTime`,
  `NUPPT.polyTimeComputable_output` — the output function is computed by the machine within
  its budget, hence is polynomial-time computable.
* `Complexity.NUPPT.output_eq_of_computesInTime` — determinism: any completed computation of
  the machine names `output`.
* `Complexity.NUPPT.output_ofPolyTime`, `NUPPT.ofPolyTimeUniform_uniform` — the converse
  direction: `ofPolyTime hf` outputs `f`, and `ofPolyTimeUniform` is uniform.
* `Complexity.NUPPT.exists_uniform_computes` — every polynomial-time computable function is
  computed with probability one by a PPT [PS10, Definition 24.6, non-vacuity].
* `Complexity.NUPPT.nonempty` — the class is inhabited.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: Definitions 23.4, 23.5, 24.6 and 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 1.3, time-bounded computation; §6.3, advice.)
-/

namespace Complexity

open Turing

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine halting on **every** input `z` within
`Ct (|z|+1)^ct` steps, the explicit polynomial `coins` giving the number of uniform coins at
parameter `n`, and an advice string of length at most `adv.eval n` per parameter.
A PPT [PS10, Definition 23.4] is the case of empty advice (`Uniform`); the time bound holds
for every coin string, the worst-case convention of [PS10, Definition 23.5].

**Deviation:** `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time
in the machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). -/
structure NUPPT where
  /-- The underlying deterministic finite machine; coins and advice are input components. -/
  M : FinTM Bool
  /-- Coefficient of the running-time bound `Ct * (|z| + 1) ^ ct`. -/
  Ct : ℕ
  /-- Degree of the running-time bound. -/
  ct : ℕ
  /-- The coin polynomial: `coins.eval n` uniform coins at parameter `n`. -/
  coins : PolyExpr
  /-- The advice polynomial: `|advice n| ≤ adv.eval n`. -/
  adv : PolyExpr
  /-- The advice string per parameter (empty for a uniform machine). -/
  advice : ℕ → List Bool
  /-- The advice is polynomially bounded. -/
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  /-- The machine halts on every input within its polynomial budget. -/
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

/-- The running-time budget of `A` on inputs of length `m`: `Ct * (m + 1) ^ ct`. -/
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct

/-- The number of coins of `A` at parameter `n`. -/
def coinLen (n : ℕ) : ℕ := A.coins.eval n

/-- The advice-length bound of `A` at parameter `n`. -/
def adviceLen (n : ℕ) : ℕ := A.adv.eval n

/-- The output of `A` on the raw machine input `z`: the output tape when the budget expires
(the machine has halted by then, `output_spec`). This is the single semantic primitive; all
activations are instances of it. -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

/-- The machine halts on `z` within its budget with `output z` on the output tape. -/
theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

/-- The machine computes the function `output` within the budget `timeBound`. -/
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  fun z => A.output_spec z

/-- The output function of an `NUPPT` is polynomial-time computable: the black box through
which every reduction of the campaign is exhibited as a machine (D2). -/
theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

/-- Determinism: any completed computation of the machine on `z` produces `output z`
(`Turing.FinTM.ComputesInTime.output_unique`). -/
theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The output is no longer than the budget (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem output_length_le (z : List Bool) : (A.output z).length ≤ A.timeBound z.length :=
  A.M.tm.output_length_le z (A.timeBound z.length)

/-- The adversary input `⟨1^n, y⟩`: the unary security parameter paired with the argument,
exactly as the text writes `A(1^n, y)` [PS10, Definition 27.3]. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

/-- The length of the adversary input `⟨1^n, y⟩` is `2n + 2 + |y|`. -/
theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

/-- The coin type of `A` at parameter `n`: `coins.eval n` uniform bits
[PS10, Definition 23.4, "each bit of the random tape is uniformly and independently chosen"]. -/
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Activation at parameter `n` on argument `y` with coins `r`: machine input
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The sampler `r ↦ runAt n y r` on the uniform coin type
`Coins n` is the distribution `A(1^n, y)` of the text. -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Activation with an untyped coin string (the interactive and oracle layouts of
chapters 3–4 hand the machine a coin string of the right length as a list). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

/-- The typed activation is the untyped one on `List.ofFn r`. -/
theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- The input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8]: the
parameter is the input length (the `1^{|y|}` prefix carries no information). It is the layout
of the literal forms of [PS10, Definition 26.1] and [PS10, Definition 69.4] (D5). -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r

/-- `A` is *uniform* — a PPT [PS10, Definition 23.4] — when its advice is empty at every
parameter. -/
def Uniform : Prop := ∀ n, A.advice n = []

/-- `A` computes `f` with probability one [PS10, Definition 24.6]: at every parameter `n`,
on every argument `y` and for **every** coin string `r`, `A(1^n, y; r) = f(⟨1^n, y⟩)`. On
the finite uniform coin space "probability one" is the same as "every coin string"
(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`).

The definition does not require `A.Uniform`. [PS10, Definition 24.6] is about a randomized
algorithm, i.e. a PPT, and is the case `A.Uniform ∧ A.Computes f`. For a non-uniform `A` this
is the advice analogue, which holds for uncomputable functions: with advice `[h n]` at
parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice projection), `A`
computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
`f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
(`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`). -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

/-- A machine that computes `f` returns `f ⟨1^n, y⟩` on every activation. -/
theorem Computes.runAt_eq {f : List Bool → List Bool} (h : A.Computes f) (n : ℕ)
    (y : List Bool) (r : A.Coins n) : A.runAt n y r = f (advInput n y) :=
  h n y r

/-- The `NUPPT` whose machine is a polynomial-time machine for `f` (chosen from the
`PolyTimeComputable` witness), with the given coin polynomial and advice. Its output function
is `f` (`output_ofPolyTime`). This is how every reduction of the campaign is packaged: the
reduction is an FP function of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` (D2). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool)
    (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT where
  M := Classical.choose hf
  Ct := Classical.choose (Classical.choose_spec hf)
  ct := Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
  coins := coins
  adv := adv
  advice := advice
  advice_length := hα
  halts := fun z => ⟨f z, Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z⟩

/-- The output function of `ofPolyTime hf …` is `f` (determinism of completed outputs). -/
theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).output = f := by
  funext z
  exact (ofPolyTime hf coins adv advice hα).output_eq_of_computesInTime
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf)) z)

/-- The coin polynomial of `ofPolyTime hf coins adv advice hα` is `coins`. -/
@[simp] theorem coins_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).coins = coins := rfl

/-- The advice polynomial of `ofPolyTime hf coins adv advice hα` is `adv`. -/
@[simp] theorem adv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).adv = adv := rfl

/-- The advice of `ofPolyTime hf coins adv advice hα` is `advice`. -/
@[simp] theorem advice_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).advice = advice := rfl

/-- The untyped activation of `ofPolyTime hf …` is `f` on the raw layout. -/
theorem runAtL_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (y r : List Bool) :
    (ofPolyTime hf coins adv advice hα).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) (advice n)) r) := by
  simp [runAtL, output_ofPolyTime]

/-- The uniform `NUPPT` with output function `f`: `ofPolyTime` with empty advice. -/
noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : NUPPT :=
  ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- `ofPolyTimeUniform hf coins` is uniform. -/
theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).Uniform := fun _ => rfl

/-- The output function of `ofPolyTimeUniform hf coins` is `f`. -/
theorem output_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).output = f :=
  output_ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- The coin polynomial of `ofPolyTimeUniform hf coins` is `coins`. -/
@[simp] theorem coins_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).coins = coins := rfl

/-- The untyped activation of `ofPolyTimeUniform hf coins` is `f` on the raw layout with
empty advice. -/
theorem runAtL_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (y r : List Bool) :
    (ofPolyTimeUniform hf coins).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, ofPolyTimeUniform, output_ofPolyTime]

/-- **Non-vacuity of [PS10, Definition 24.6].** Every polynomial-time computable function
`f` is computed with probability one by a PPT (a uniform `NUPPT`): the machine for
`f ∘ pairFstD ∘ pairFstD` applied to the raw input `⟨⟨⟨1^n, y⟩, []⟩, r⟩` ignores the advice
and the coins and returns `f ⟨1^n, y⟩`. (This is the direction "`PolyTimeComputable f` gives a
PPT computing `f`" of the equivalence behind Deviation 3, `FunFamily.Easy`.) -/
theorem exists_uniform_computes {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧ A.Computes f := by
  have hF : PolyTimeComputable fun z => f (pairFstD (pairFstD z)) :=
    hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  refine ⟨ofPolyTimeUniform hF coins, ofPolyTimeUniform_uniform hF coins, rfl, fun n y r => ?_⟩
  rw [runAt_eq, runAtL_ofPolyTimeUniform]
  simp

end NUPPT

/-- PPT [PS10, Definition 23.4] = non-uniform PPT with empty advice: the subtype of uniform
`NUPPT`s. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

/-- Non-vacuity: the class is inhabited (the identity machine with no coins). -/
theorem NUPPT.nonempty : Nonempty NUPPT :=
  ⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0)⟩

/-- Non-vacuity: the class of PPTs is inhabited. -/
theorem PPT.nonempty : Nonempty PPT :=
  ⟨⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0),
    NUPPT.ofPolyTimeUniform_uniform _ _⟩⟩

end Complexity

## ===== TCSlib/Complexity/Randomized/Primitives.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Build.PairSplit
import TCSlib.Complexity.Randomized.Build.UnaryMul
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two new machine primitives: coin splitting and unary multiplication

The closure calculus of non-uniform PPTs ([PS10, §2.1], implicit in every reduction of
chapters 2–4; inventory item Claim-26.3) needs two string machines that the library's
catalog `TCSlib.Complexity.TuringMachine.Build.Primitives` does not provide:

* `Turing.FinTM.computesFunInTime_pairSplitAt` — `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩`: cut a
  coin string at a unary length (fresh coin segments as independent uniform strings);
* `Turing.FinTM.computesFunInTime_unaryMul` — `⟨1^a, 1^b⟩ ↦ 1^{ab}`: unary multiplication,
  which makes every syntactic polynomial computable in unary
  (`Complexity.polyTimeComputable_unaryPoly`) without the repetition lemma (D9).

Both are built in the `Build/` style (foundation decision D11): explicit finite machines with
a proved timed contract (`TCSlib.Complexity.Randomized.Build.PairSplit`,
`TCSlib.Complexity.Randomized.Build.UnaryMul`). This file states the two contracts with their
construction sketches (DESIGN.md §2.4) and derives the FP-level consequences the closure
catalogue consumes:
`polyTimeComputable_unaryPoly` (by induction on the expression, the `mul` case being the
only use of `unaryMul`) and the typed cuts `polyTimeComputable_pairTakePoly` /
`polyTimeComputable_pairDropPoly` (`pairSplitAt` applied to `⟨1^{p(|fst z|)}, snd z⟩`).

The unary evaluator is hosted here rather than in `TCSlib.Complexity.Randomized.PolyExpr`
because its `mul` case needs `unaryMul`, while the cuts below need both the evaluator and
`PolyExpr`; this keeps the import graph acyclic.

## Main results

* `Turing.FinTM.computesFunInTime_pairSplitAt` — coin splitting at a unary length, linear
  time (proved; the machine is `Turing.FinTM.exists_pairSplitTM` in
  `TCSlib.Complexity.Randomized.Build.PairSplit`).
* `Turing.FinTM.computesFunInTime_unaryMul` — unary multiplication, quadratic time
  (proved; the machine is `Turing.FinTM.exists_unaryMulTM` in
  `TCSlib.Complexity.Randomized.Build.UnaryMul`).
* `Complexity.polyTimeComputable_unaryPoly` — `x ↦ 1^{p(|x|)}` is polynomial-time
  computable for every syntactic polynomial `p` (proved by induction; the `mul` and `pow`
  cases rest on `unaryMul`).
* `Complexity.polyTimeComputable_pairTakePoly`, `Complexity.polyTimeComputable_pairDropPoly`
  — on `⟨u, b⟩`, the first / the remaining `p(|u|)` bits of `b` (proved from `pairSplitAt`).

## Main definitions

None (the primitives are existence statements over `Turing.FinTM Bool`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of p.p.t. machines used implicitly throughout.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, multi-tape machines and linear-time string
  manipulation.)
-/

namespace Turing.FinTM

/-- **Coin splitting at a unary length** (new primitive): on a pair `⟨u, b⟩` the machine
outputs the pair `⟨b.take |u|, b.drop |u|⟩`; on a malformed word it outputs `[]`. Linear
time. This is how a reduction uses disjoint segments of its coin string as independent
uniform strings [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.PairSplit`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it reads the doubled prefix of
`u` onto the work tape without emitting anything, and stops at the separator `01` (a
malformed prefix halts with empty output). Phase 2 rewinds the work head. Phase 3 is a copy
scan of `b`: while the work head walks across the stored `u`, each bit `c` of `b` read on
the input tape is emitted doubled as `cc` (the doubled first component of the output pair);
when the stored `u` is exhausted the machine emits the separator `01` and then copies the
remainder of `b` verbatim (if `b` is shorter than `u`, the separator is emitted when the
input ends and the second component is empty). The step ledger gives at most `5 (n + 1)`
steps; the output is `pairEncode (b.take |u|) (b.drop |u|)` by `Turing.pairEncode_eq_dbl`
(`Turing.FinTM.exists_pairSplitTM`, with `c = 5`). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
          | none => [])
        fun n => c * (n + 1) := by
  obtain ⟨M, hM⟩ := exists_pairSplitTM
  exact ⟨M, 5, hM⟩

/-- **Unary multiplication** (new primitive): on a pair `⟨u, v⟩` the machine outputs
`1^{|u| · |v|}`; on a malformed word it outputs `[]`. Quadratic time. With it every syntactic
polynomial is computable in unary (`Complexity.polyTimeComputable_unaryPoly`), so the lengths
`1^{p(n)}` that reductions need never go through the repetition lemma (D9).

**Proof sketch (construction, DESIGN.md §2.4; built in
`TCSlib.Complexity.Randomized.Build.UnaryMul`).** One work tape. Phase 1 is the buffered
aligned parser of `Turing.FinTM.computesFunInTime_pairFst`: it undoubles the prefix `u` onto
the work tape without emitting anything (one cell per token of `u`, so the content of `u` is
irrelevant) and validates the separator `01`; a malformed input halts with empty output.
Phase 2 rewinds the work head and then, for each symbol of the second component `v` (read
left to right, its content irrelevant), walks across the stored word emitting one `true`
per cell (`emitAction`-style) and rewinds the work tape; at the end of the input it halts.
**Deviation from the DESIGN.md sketch** (which stores `v` and replays it once per token of
`u`): storing `u` and replaying it once per symbol of `v` needs no input rewind, and the
product `|u| · |v|` is the same. The run takes `|u| + 1 + |v| (2 |u| + 3) + 1` steps after
the parser, at most `(n + 1) ^ 2 + 3 n + 5 ≤ 5 (n + 1) ^ 2` in all (step ledger `mul_run`),
and the output is `List.replicate (|u| * |v|) true` by induction on the symbols of `v`
(`List.replicate_add`, `Nat.mul_succ`) — `Turing.FinTM.exists_unaryMulTM`, with `c = 5`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (u, v) => List.replicate (u.length * v.length) true
          | none => [])
        fun n => c * (n + 1) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_unaryMulTM
  exact ⟨M, 5, hM⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- FP-level unary multiplication: if `x ↦ 1^{f x}` and `x ↦ 1^{g x}` are polynomial-time
computable, so is `x ↦ 1^{f x · g x}` (pair the two unary strings with
`PolyTimeComputable.pairEncode` and apply the unary-multiplication machine). -/
private theorem polyTimeComputable_unaryMulFun {f g : List Bool → ℕ}
    (hf : PolyTimeComputable fun x => List.replicate (f x) true)
    (hg : PolyTimeComputable fun x => List.replicate (g x) true) :
    PolyTimeComputable fun x => List.replicate (f x * g x) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have hmul : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert hmul.comp (hf.pairEncode hg) using 1
  funext x
  simp [pairDecode_pairEncode]

/-- **The unary evaluator of a syntactic polynomial is polynomial-time:** for every
`p : PolyExpr`, the map `x ↦ 1^{p(|x|)}` is polynomial-time computable. This is the device by
which a reduction produces every length `1^{p(n)}` it needs (coin cuts, parameter changes,
padding), foundation decision D9; it is never routed through the repetition lemma.

**Proof sketch.** Induction on `p`. `const c`: the constant string `1^c`
(`Complexity.polyTimeComputable_const`). `var`: `x ↦ 1^{|x|}`
(`Complexity.polyTimeComputable_unary`). `add p q`: concatenate the two unary strings
(`Complexity.PolyTimeComputable.append`, `List.replicate_add`). `mul p q`: pair the two unary
strings and apply the unary-multiplication machine `Turing.FinTM.computesFunInTime_unaryMul`
(the only case that uses the new primitive). `pow p c`: inner induction on `c`, the step
being the `mul` case against `1^{p(|x|)}` (`pow_succ`). -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true := by
  induction p with
  | const c => exact polyTimeComputable_const (List.replicate c true)
  | var => exact polyTimeComputable_unary
  | add p q hp hq =>
    simpa only [PolyExpr.eval_add, List.replicate_add] using hp.append hq
  | mul p q hp hq => exact polyTimeComputable_unaryMulFun hp hq
  | pow p c hp =>
    induction c with
    | zero => simpa using polyTimeComputable_const (List.replicate 1 true)
    | succ c ih =>
      simpa only [PolyExpr.eval_pow, pow_succ] using polyTimeComputable_unaryMulFun ih hp

/-- The FP form of the coin-splitting machine: `z ↦ ⟨(snd z).take |fst z|, (snd z).drop |fst z|⟩`
on pairs, `[]` on malformed words. -/
private theorem polyTimeComputable_pairSplitAt :
    PolyTimeComputable fun z => match pairDecode z with
      | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
      | none => [] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_pairSplitAt
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- The re-pairing `z ↦ ⟨1^{p(|fst z|)}, snd z⟩` is polynomial-time (the unary evaluator on
the first component, paired with the second component). -/
private theorem polyTimeComputable_pairUnaryFst (p : PolyExpr) :
    PolyTimeComputable fun z =>
      pairEncode (List.replicate (p.eval (pairFstD z).length) true) (pairSndD z) :=
  ((polyTimeComputable_unaryPoly p).comp polyTimeComputable_pairFstD).pairEncode
    polyTimeComputable_pairSndD

/-- **Typed coin cut, head:** on `z = ⟨u, b⟩`, the first `p(|u|)` bits of `b` are
polynomial-time computable (`z ↦ (snd z).take (p(|fst z|))`, with the total projections
`Complexity.pairFstD`/`pairSndD`). A reduction run on `⟨1^n, r⟩` thereby reads the first
`p(n)` coins as data [PS10, §2.1, implicit; inventory Claim-26.3(c)].

**Proof sketch.** `pairFstD ∘ pairSplitAt ∘ (z ↦ ⟨1^{p(|fst z|)}, snd z⟩)`: the re-pairing is
`polyTimeComputable_unaryPoly p` on `pairFstD` paired with `pairSndD`
(`PolyTimeComputable.pairEncode`), the split is `Turing.FinTM.computesFunInTime_pairSplitAt`
via `polyTimeComputable_of_linear`, and the composite equals the claimed function by
`Turing.pairDecode_pairEncode`, `Complexity.pairFstD_pairEncode` and `List.length_replicate`
(`PolyTimeComputable.comp`, `funext`). -/
theorem polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairDecode_pairEncode]

/-- **Typed coin cut, tail:** on `z = ⟨u, b⟩`, the bits of `b` after the first `p(|u|)` are
polynomial-time computable (`z ↦ (snd z).drop (p(|fst z|))`): the remaining coins of a
reduction after the first `p(n)` were consumed.

**Proof sketch.** As `polyTimeComputable_pairTakePoly` with `pairSndD` in place of `pairFstD`
after the split (`Complexity.pairSndD_pairEncode`). -/
theorem polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length) := by
  convert polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSplitAt.comp (polyTimeComputable_pairUnaryFst p)) using 1
  funext z
  simp [pairDecode_pairEncode]

end Complexity

## ===== TCSlib/Complexity/Randomized/Closure.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The closure calculus of non-uniform PPTs

The class of non-uniform PPTs is closed under the operations every reduction of
[PS10, ch. 2–4] performs silently (inventory item Claim-26.3, "implicit throughout"):
pre- and post-composition with polynomial-time maps, parameter changes, hard-wiring advice,
using fresh coin segments as data, and sequential composition with fresh coins. Each lemma
here exhibits the composite machine as `Complexity.NUPPT.ofPolyTime` of an FP function of
the raw input `⟨⟨⟨1^n, y⟩, α⟩, r⟩` (foundation decision D2), built from
`NUPPT.polyTimeComputable_output`, the pairing calculus of
`TCSlib.Complexity.ClassNP.PolyTimePairing`, the unary evaluator
`Complexity.polyTimeComputable_unaryPoly` and the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` of
`TCSlib.Complexity.Randomized.Primitives`; the functional equation is
`NUPPT.runAtL_ofPolyTime` followed by the projection identities of the layout.
`Uniform` is preserved whenever the advice is the given machine's or empty.

The supplier table (DESIGN.md §2.5):

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_compParam` | `pre ⟨1^n, y⟩`, then `A.output`, then `post ⟨1^n, ·⟩` | projections, `comp` |
| `exists_comp` | `exists_compParam` with `pre`, `post` ignoring `1^n` | `exists_compParam` |
| `exists_reparam p` | advice `A.advice (p n)`; replace `1^n` by `1^{p n}` (`unaryPoly p`) | `unaryPoly` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩`; cut `A.coins (φ n)` coins | `pairTakePoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `p n`; pass the head as data | `pairTakePoly`, `pairDropPoly` |
| `exists_seq` | cut at `A.coins n`; run `A`, then `B` on `⟨y, a⟩`; advice `⟨α_A, α_B⟩` | both outputs, cuts, pairing |

Not in this file (they are FP-level facts the campaign uses directly): negation and
`[true]`-normalisation of verdicts (`Turing.FinTM.computesFunInTime_ifEq` through
`exists_comp`), branching (`Complexity.polyTimeComputable_ite`), length tests
(`polyTimeComputable_lenEq`/`_lenLe`), and the loop fuel of the repetition lemma
(`TCSlib.Complexity.Randomized.Repetition`).

## Main definitions

* `Complexity.NUPPT.layout`, `NUPPT.inParam`, `NUPPT.inArg`, `NUPPT.inAdvice`,
  `NUPPT.inCoins` — the raw input layout `⟨⟨⟨u, y⟩, α⟩, r⟩` and its four projections.
* `Complexity.NUPPT.combineAdvice` — two advice strings as one, keeping `[]` when both are
  empty (so that sequential composition preserves uniformity).

## Main results

* `Complexity.NUPPT.exists_compParam` — closure under polynomial-time pre- and post-processing
  that reads the parameter (`pre` sees `⟨1^n, y⟩`, `post` sees `⟨1^n, output⟩`).
* `Complexity.NUPPT.exists_comp` — its case that does not read the parameter (`pre` sees only
  `y`, `post` only the output).
* `Complexity.NUPPT.exists_reparam` — parameter change `n ↦ p(n)` (uniformity preserved).
* `Complexity.NUPPT.exists_reparam_advice` — parameter change along a polynomially bounded
  `φ : ℕ → ℕ`, hard-wiring `1^{φ n}` and the advice at `φ n`; extra coins unread.
* `Complexity.NUPPT.exists_withAdvice` — hard-wiring an extra polynomial-length advice.
* `Complexity.NUPPT.exists_split` — the first `p(n)` coins passed as data.
* `Complexity.NUPPT.exists_seq` — sequential composition with input pass-through and fresh
  coins (the "sunglass" composition of [Gar26]'s reductions, at the machine level).
* `Complexity.NUPPT.Computes.polyTimeComputable` — a PPT computing `f` with probability one
  gives `f ∘ advInput` as a polynomial-time function (coins hard-wired to `1^{coins n}`).
* `Complexity.NUPPT.polyTimeComputable_layout` and the projection lemmas — the FP calculus of
  the layout.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of (non-uniform) p.p.t. machines used implicitly throughout.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete reductions these machines package).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, closure of FP under composition.)
-/

namespace Complexity

open Turing

namespace NUPPT

/-! ### The raw input layout and its projections -/

/-- The raw machine input `⟨⟨⟨u, y⟩, α⟩, r⟩`: unary parameter `u`, argument `y`, advice `α`,
coins `r` (`runAtL n y r` is `output (layout 1^n y (advice n) r)`). -/
def layout (u y α r : List Bool) : List Bool := pairEncode (pairEncode (pairEncode u y) α) r

/-- The unary-parameter slot of a raw input. -/
def inParam (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD z))

/-- The argument slot of a raw input. -/
def inArg (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD z))

/-- The advice slot of a raw input. -/
def inAdvice (z : List Bool) : List Bool := pairSndD (pairFstD z)

/-- The coin slot of a raw input. -/
def inCoins (z : List Bool) : List Bool := pairSndD z

/-- The parameter slot of a layout. -/
@[simp] theorem inParam_layout (u y α r : List Bool) : inParam (layout u y α r) = u := by
  simp [inParam, layout]

/-- The argument slot of a layout. -/
@[simp] theorem inArg_layout (u y α r : List Bool) : inArg (layout u y α r) = y := by
  simp [inArg, layout]

/-- The advice slot of a layout. -/
@[simp] theorem inAdvice_layout (u y α r : List Bool) : inAdvice (layout u y α r) = α := by
  simp [inAdvice, layout]

/-- The coin slot of a layout. -/
@[simp] theorem inCoins_layout (u y α r : List Bool) : inCoins (layout u y α r) = r := by
  simp [inCoins, layout]

/-- An activation is the output on the layout `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem runAtL_eq_output_layout (A : NUPPT) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (layout (List.replicate n true) y (A.advice n) r) := rfl

/-- The parameter projection is polynomial-time. -/
theorem polyTimeComputable_inParam : PolyTimeComputable inParam :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The argument projection is polynomial-time. -/
theorem polyTimeComputable_inArg : PolyTimeComputable inArg :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The advice projection is polynomial-time. -/
theorem polyTimeComputable_inAdvice : PolyTimeComputable inAdvice :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The coin projection is polynomial-time. -/
theorem polyTimeComputable_inCoins : PolyTimeComputable inCoins :=
  polyTimeComputable_pairSndD

/-- Assembling a layout from four polynomial-time functions is polynomial-time
(three applications of `PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_layout {f₁ f₂ f₃ f₄ : List Bool → List Bool}
    (h₁ : PolyTimeComputable f₁) (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃)
    (h₄ : PolyTimeComputable f₄) :
    PolyTimeComputable fun z => layout (f₁ z) (f₂ z) (f₃ z) (f₄ z) :=
  ((h₁.pairEncode h₂).pairEncode h₃).pairEncode h₄

/-- Composition of polynomial-time functions, in applied form. -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-! ### Combined advice -/

/-- Two advice strings as one: `⟨a, b⟩`, except that two empty strings combine to `[]`
(so that composing uniform machines gives a uniform machine). Decoded by `pairFstD` and
`pairSndD`, which return `[]` on `[]`. -/
def combineAdvice (a b : List Bool) : List Bool :=
  if a = [] ∧ b = [] then [] else pairEncode a b

/-- Decoding the first combined advice string. -/
@[simp] theorem pairFstD_combineAdvice (a b : List Bool) : pairFstD (combineAdvice a b) = a := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

/-- Decoding the second combined advice string. -/
@[simp] theorem pairSndD_combineAdvice (a b : List Bool) : pairSndD (combineAdvice a b) = b := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · simp

/-- Two empty advice strings combine to the empty string. -/
theorem combineAdvice_nil : combineAdvice [] [] = [] := by
  simp [combineAdvice]

/-- The combined advice has length at most `2|a| + 2 + |b|`. -/
theorem length_combineAdvice_le (a b : List Bool) :
    (combineAdvice a b).length ≤ 2 * a.length + 2 + b.length := by
  unfold combineAdvice
  split_ifs
  · simp
  · rw [length_pairEncode]

/-! ### The closure catalogue -/

/-- **Closure under parameter-aware pre- and post-processing** [PS10, §2.1, implicit;
inventory Claim-26.3(a), (b)] (gate 03a, finding 3): for an `NUPPT` `A` and polynomial-time
`pre`, `post` there is an `NUPPT` `B` with the same coins and advice that, at parameter `n` on
argument `y` with coins `r`, computes `post ⟨1^n, A(1^n, pre ⟨1^n, y⟩; r)⟩`: `pre` sees the
adversary input `⟨1^n, y⟩` (`advInput n y`), and `post` sees the parameter `1^n` paired with
`A`'s output. `exists_comp` is the case where `pre` and `post` ignore `1^n`.

**Proof sketch.** The raw function is
`z ↦ post ⟨inParam z, A.output (layout (inParam z) (pre ⟨inParam z, inArg z⟩) (inAdvice z)
(inCoins z))⟩`, polynomial-time by `polyTimeComputable_layout`,
`PolyTimeComputable.pairEncode`, `PolyTimeComputable.comp`, `NUPPT.polyTimeComputable_output`,
`hpre`, `hpost`; `B := ofPolyTime` of it with `A`'s coins and advice. On the layout
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` the projections return the slots (`runAtL_ofPolyTime`, the
`pairFstD_pairEncode`/`pairSndD_pairEncode` identities), so `⟨inParam z, inArg z⟩` is
`⟨1^n, y⟩ = advInput n y` and the value is `post ⟨1^n, A.runAtL n (pre (advInput n y)) r⟩`. -/
theorem exists_compParam (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        post (pairEncode (List.replicate n true) (A.runAtL n (pre (advInput n y)) r)) := by
  have hF := ptc_comp hpost (polyTimeComputable_inParam.pairEncode
    (ptc_comp A.polyTimeComputable_output (polyTimeComputable_layout polyTimeComputable_inParam
      (ptc_comp hpre (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
      polyTimeComputable_inAdvice polyTimeComputable_inCoins)))
  refine ⟨ofPolyTime hF A.coins A.adv A.advice A.advice_length, rfl, rfl, rfl, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Closure under polynomial-time pre- and post-processing** [PS10, §2.1, implicit;
inventory Claim-26.3(a), (b)]: for an `NUPPT` `A` and polynomial-time `pre`, `post` there is an
`NUPPT` `B` with the same coins and advice that computes `post (A(1^n, pre y; r))`.

**Scope** (gate 03a, finding 3): `pre` sees only the argument `y` and `post` only `A`'s output;
neither sees `1^n`. Pre- and post-processing that depends on the parameter (padding or cutting
to `ℓ'(n)` bits, slicing `p(n)` bits, planting at a position that depends on `n`) is the
parameter-aware form `exists_compParam`, where `pre` sees `⟨1^n, y⟩` and `post` sees `1^n`
paired with the output. Reductions that also read the advice or the coins are built as
`ofPolyTime` of a raw function of the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`,
`polyTimeComputable_layout`), as `EnsembleLemmas.exists_pushRed` does for [PS10, Lemma 71.5].

**Proof sketch.** `exists_compParam` with `pre ∘ snd` and `post ∘ snd`: the second component of
`advInput n y = ⟨1^n, y⟩` is `y`, and that of `⟨1^n, A.runAtL n (pre y) r⟩` is `A`'s output
(`pairSndD_pairEncode`). -/
theorem exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
  obtain ⟨B, hc, ha, hα, hB⟩ := exists_compParam A (ptc_comp hpre polyTimeComputable_pairSndD)
    (ptc_comp hpost polyTimeComputable_pairSndD)
  refine ⟨B, hc, ha, hα, fun n y r => ?_⟩
  rw [hB, pairSndD_pairEncode]
  simp [advInput]

/-- **Parameter change `n ↦ p(n)`** [PS10, §2.1, implicit; inventory Claim-26.3]: for an
`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `A.coins.subst p`
that at parameter `n` behaves as `A` at parameter `p(n)`; `B` is uniform when `A` is (the
prefix `1^{p(n)}` is computed, not hard-wired).

**Proof sketch.** Advice `A.advice (p n)` of length `≤ (A.adv.subst p).eval n`
(`PolyExpr.eval_subst`); the raw function replaces the parameter slot `1^n` by
`1^{p(|1^n|)} = 1^{p n}` (`polyTimeComputable_unaryPoly p` on `inParam`) and re-pairs
(`polyTimeComputable_layout`), then applies `A.output`; the equation is `runAtL_ofPolyTime`
plus the projection identities and `List.length_replicate`. -/
theorem exists_reparam (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout
      (ptc_comp (polyTimeComputable_unaryPoly p) polyTimeComputable_inParam)
      polyTimeComputable_inArg polyTimeComputable_inAdvice polyTimeComputable_inCoins)
  have hadv : ∀ n, (A.advice (p.eval n)).length ≤ (A.adv.subst p).eval n := fun n => by
    rw [PolyExpr.eval_subst]
    exact A.advice_length _
  refine ⟨ofPolyTime hF (A.coins.subst p) (A.adv.subst p) (fun n => A.advice (p.eval n)) hadv,
    rfl, fun hA n => hA _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Parameter change along an arbitrary polynomially bounded `φ : ℕ → ℕ`** (non-uniform)
[PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`, `φ` with `φ n ≤ p n`,
there is an `NUPPT` `B` with coins `A.coins.subst p` that at parameter `n` behaves as `A` at
parameter `φ n` on the first `A.coins (φ n)` coins (extra coins are unread). This is the one
place an abstract `ℕ → ℕ` appears (as a hypothesis with a `PolyExpr` majorant, D9); it serves
Lemma 64.3's `m(n) = n − ⌊log₂ n⌋`, the literal/`1^n` bridges of Definitions 26.1 and 69.4, and
the interdefinability argument of D3/D4.

**Proof sketch.** Advice `⟨1^{φ n}, A.advice (φ n)⟩`, of length
`2 φ n + 2 + |A.advice (φ n)| ≤ 2 p n + 2 + A.adv (p n)` by `hφ`, `advice_length` and
`PolyExpr.eval_mono` — the bound `add (add (mul (const 2) p) (const 2)) (A.adv.subst p)`. The
raw function reads `w := 1^{φ n}` and `α := A.advice (φ n)` from the advice slot
(`pairFstD`/`pairSndD` of `inAdvice`), cuts the coins to `A.coins.eval |w|` bits
(`polyTimeComputable_pairTakePoly A.coins` on `⟨w, inCoins z⟩`), and runs `A.output` on
`layout w (inArg z) α coins'`; `B.coins = A.coins.subst p ≥ A.coins (φ n)` by `eval_mono`, so
the cut reads existing coins. The equation is `runAtL_ofPolyTime` plus the projection
identities. -/
theorem exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n))) := by
  have hw := ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout hw polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice)
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins) (hw.pairEncode polyTimeComputable_inCoins)))
  have hadv : ∀ n, (pairEncode (List.replicate (φ n) true) (A.advice (φ n))).length ≤
      (PolyExpr.add (.add (.mul (.const 2) p) (.const 2)) (A.adv.subst p)).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ n
    have h₂ := A.advice_length (φ n)
    have h₃ := A.adv.eval_mono (hφ n)
    omega
  refine ⟨ofPolyTime hF (A.coins.subst p) _
    (fun n => pairEncode (List.replicate (φ n) true) (A.advice (φ n))) hadv, rfl, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, coinLen, layout, inArg, inAdvice, inCoins]

/-- **Hard-wiring advice** [PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`
and a polynomially bounded family `β n` there is an `NUPPT` `B` with the same coins that
computes `A(1^n, ⟨y, β n⟩; r)` (the reductions of chapters 2–4 hard-wire hybrid indices,
worst-case inputs and the given adversary's advice this way).

**Proof sketch.** Advice `⟨A.advice n, β n⟩` of length `2 A.adv n + 2 + b n`
(`length_pairEncode`); the raw function re-pairs the argument slot with the second half of
the advice slot and runs `A.output` with the first half as advice
(`polyTimeComputable_layout`, projections). -/
theorem exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode
        (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice))
      (ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice) polyTimeComputable_inCoins)
  have hadv : ∀ n, (pairEncode (A.advice n) (β n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) b).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := A.advice_length n
    have h₂ := hβ n
    omega
  refine ⟨ofPolyTime hF A.coins _ (fun n => pairEncode (A.advice n) (β n)) hadv, rfl,
    fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Extra coins passed as data** [PS10, §2.1, implicit; inventory Claim-26.3(c)]: for an
`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `p + A.coins`
and `A`'s advice such that `B(1^n, y; r) = A(1^n, ⟨y, r.take (p n)⟩; r.drop (p n))`: the first
`p n` coins become part of the input (a uniformly random string of length `p n`), the rest are
`A`'s coins.

**Proof sketch.** The raw function cuts the coin slot at `p(|1^n|)` with
`polyTimeComputable_pairTakePoly p`/`pairDropPoly p` on `⟨inParam z, inCoins z⟩`, re-pairs the
argument with the head and runs `A.output` with the tail as coins; the equation is
`runAtL_ofPolyTime`, the projection identities and `List.length_replicate`. -/
theorem exists_split (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode (ptc_comp (polyTimeComputable_pairTakePoly p) hcut))
      polyTimeComputable_inAdvice (ptc_comp (polyTimeComputable_pairDropPoly p) hcut))
  refine ⟨ofPolyTime hF (.add p A.coins) A.adv A.advice A.advice_length, rfl, rfl,
    fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]

/-- **Sequential composition with input pass-through and fresh coins** [PS10, §2.1, implicit;
inventory Claim-26.3(b), (c), (e) with one call]: for `NUPPT`s `A`, `B` there is an `NUPPT`
`C` with coins `A.coins + B.coins`, uniform when both are, computing
`B(1^n, ⟨y, A(1^n, y; r₁)⟩; r₂)` where `r = r₁ ++ r₂` is cut at `A.coins n`. This is the
machine-level form of the "sunglass" reduction `D' := D ∘ (sampler)` of [Gar26] used by
Lemma 71.5 (`Indist.push`) and every two-stage reduction.

**Proof sketch.** Advice `combineAdvice (A.advice n) (B.advice n)` of length
`≤ 2 A.adv n + 2 + B.adv n` (`length_combineAdvice_le`), equal to `[]` when both are empty
(`combineAdvice_nil`, so uniformity is preserved). The raw function cuts the coins at
`A.coins(|1^n|)` (`pairTakePoly`/`pairDropPoly` on `⟨inParam z, inCoins z⟩`), runs `A.output` on
`layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pairs the result with the argument
and runs `B.output` on `layout (inParam z) ⟨inArg z, a⟩ (pairSndD (inAdvice z)) r₂`; the
equation is `runAtL_ofPolyTime`, the projection identities, `pairFstD_combineAdvice`,
`pairSndD_combineAdvice` and `List.length_replicate`. -/
theorem exists_seq (A B : NUPPT) :
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hr₁ := ptc_comp (polyTimeComputable_pairTakePoly A.coins) hcut
  have hr₂ := ptc_comp (polyTimeComputable_pairDropPoly A.coins) hcut
  have ha := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg
      (ptc_comp polyTimeComputable_pairFstD polyTimeComputable_inAdvice) hr₁)
  have hF := ptc_comp B.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam (polyTimeComputable_inArg.pairEncode ha)
      (ptc_comp polyTimeComputable_pairSndD polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (combineAdvice (A.advice n) (B.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) B.adv).eval n := fun n => by
    have h₁ := length_combineAdvice_le (A.advice n) (B.advice n)
    have h₂ := A.advice_length n
    have h₃ := B.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨ofPolyTime hF (.add A.coins B.coins) _
    (fun n => combineAdvice (A.advice n) (B.advice n)) hadv, rfl, fun hA hB n => ?_,
    fun n y r => ?_⟩
  · show combineAdvice (A.advice n) (B.advice n) = []
    rw [hA n, hB n, combineAdvice_nil]
  · rw [runAtL_ofPolyTime]
    simp [runAtL, advInput, coinLen, layout, inParam, inArg, inAdvice, inCoins]

/-- **From "computes with probability one" to FP** [PS10, Definition 24.6; the direction
"a PPT computing `f` gives a polynomial-time evaluator" behind Deviation 3]: if a uniform
`A` computes `f`, then `z ↦ f ⟨1^{|fst z|}, snd z⟩` is polynomial-time computable — run `A`
with the coins hard-wired to the all-`true` string of length `coins n`.

**Proof sketch.** The raw function `z ↦ A.output (layout 1^{|fst z|} (snd z) [] 1^{A.coins |fst z|})`
is polynomial-time (`polyTimeComputable_unary`, `polyTimeComputable_unaryPoly A.coins`,
`polyTimeComputable_layout`); by `Computes` at parameter `|fst z|`, argument `snd z` and
the constant coin string `fun _ => true` (`List.ofFn_const`), it equals
`f (advInput |fst z| (snd z))` everywhere. -/
theorem Computes.polyTimeComputable {A : NUPPT} {f : List Bool → List Bool} (hA : A.Uniform)
    (h : A.Computes f) :
    PolyTimeComputable fun z => f (advInput (pairFstD z).length (pairSndD z)) := by
  have hF := ptc_comp A.polyTimeComputable_output
    (polyTimeComputable_layout (ptc_comp polyTimeComputable_unary polyTimeComputable_pairFstD)
      polyTimeComputable_pairSndD (polyTimeComputable_const [])
      (ptc_comp (polyTimeComputable_unaryPoly A.coins) polyTimeComputable_pairFstD))
  convert hF using 1
  funext z
  have hz := h (pairFstD z).length (pairSndD z) (fun _ => true)
  have hadv := hA (pairFstD z).length
  simp only [runAt, List.ofFn_const] at hz
  rw [← hz]
  simp [layout, advInput, coinLen, hadv]

end NUPPT

end Complexity

## ===== TCSlib/Complexity/Randomized/Repetition.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Build.IterateFind
import TCSlib.Complexity.Randomized.Build.StateLoop
import TCSlib.Complexity.Randomized.Build.StringLoops
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The repetition lemma: polynomially many rounds of a polynomial-time step

Every theorem of [PS10, ch. 2–4] that *repeats* an adversary — hardness amplification
[PS10, Theorem 35.1, Algorithm 38.5: `2nm²p(n)` fresh-coin calls returning the first
success], Goldreich–Levin [PS10, Theorem 87.3: `n(2^k − 1)` calls and a majority], the
next-bit predictor, the GGM distinguisher hosting `q(n)` oracle queries, the truncated
simulators of the zero-knowledge chapter (inventory item Inf-4.3: "restart loops with a
bounded number of attempts as strict PPT", Claims 123.d and 128.a), rejection samplers
(D10) — reduces to one machine lemma, `Complexity.polyTimeComputable_iterateFind`: iterate a
polynomial-time step `g` at most `R(|x|)` times on a polynomially bounded orbit and return
the payload `out` of the first orbit point accepted by `acc` (`[]` on exhaustion). The
iteration `polyTimeComputable_iterate`, the concatenating variant
`polyTimeComputable_iterateEmit`, the block map and the string tests `majority`, `pairXor`,
`pairEq` are instances or small machines.

**Admissions policy (D11).** `polyTimeComputable_iterateFind` is the single machine lemma
that may remain admitted at the end of the fill campaign (run 4); every theorem that repeats
an adversary depends on it and on nothing else admitted, and the headline axiom prints
(`audits/pass-shelat/Checks.lean`) list it by name if it is still open. The derived lemmas of
this file are to be closed from it (or by small direct machines), so that the admission stays
a single named one. **Status (run 3b):** `polyTimeComputable_iterateFind` is closed — its
machine is built on the public clean-module host `TCSlib.Complexity.TuringMachine.Build.ModuleHost`
(clean modules and the finite host), with its instance in
`TCSlib.Complexity.Randomized.Build.IterateFindHost` (the copier and the host's control) and
the assembly in `TCSlib.Complexity.Randomized.Build.IterateFind` (through
`Turing.FinTM.exists_loopFindTM`), and its axiom print is `[propext, Classical.choice, Quot.sound]`.
The six derived lemmas are closed too, as instances of one public **state-loop** form
`polyTimeComputable_stateFind` of the repetition lemma (a state word `⟨x, s⟩` retaining the
input, a step on the state, a test firing first at round `N x ≤ R|x|`, an output read off the
final state), whose loop data, orbit closed forms and bounds live in
`TCSlib.Complexity.Randomized.Build.StateLoop` (the form itself and the two iteration loops)
and `TCSlib.Complexity.Randomized.Build.StringLoops` (the four string loops).

**Construction of `iterateFind`, as built (DESIGN.md §2.6, step 1, and its as-built erratum,
which records the departures from the frozen steps 2–5).**

1. *State word carries the input.* The loop state is `⟨x, s⟩` (`pairEncode x s`) from
   `⟨x, x⟩`; the step is the length-guarded `guardedStep g P x`, which advances to `⟨x, g s⟩` if
   the **new** point fits, `|g s| ≤ P|x|`, and otherwise leaves the word unchanged. On the
   orbit, for `i ≤ R|x|`, the guard is never taken (`iterate_guardedStep_eq`), so the loop's
   `find?` is the statement's (`acc_guardedStep_eq`). The pure invariant `LoopInv` is closed
   under the step (`loopInv_guardedStep`); the machine uses the stronger actual-pair invariant
   `∃ s, w = ⟨x, s⟩ ∧ |s| ≤ P|x|`, which bounds the word's length by `2|x| + 2 + P|x|`.
2. *The machine.* `Complexity.IterateFind.polyTimeComputable_find`
   (`TCSlib.Complexity.Randomized.Build.IterateFind`) is an instance of
   `Turing.FinTM.exists_loopFindTM` with the guarded step `IterateFind.step`, the same function
   as `guardedStep` (`IterateFind.step_eq`). Its loop body runs five clean modules in the public
   clean-module host `Turing.ModuleHost.hostTM` (`TCSlib.Complexity.TuringMachine.Build.ModuleHost`,
   host H14): the copier, which puts the native input on tape 0 (`IterateFind.copyTM`); the
   startup install `x ↦ ⟨x, x⟩`; the verdict install `w ↦ ⟨[acc (snd w)], w⟩`; the step install;
   and the payload emit `w ↦ out (snd (snd w))`. The installs and the emit come from
   `Turing.ModuleHost.clean_install`/`clean_emit` (a clean-call bridge stopped by a release flag
   and cut at its first halt). The host's control
   (`TCSlib.Complexity.Randomized.Build.IterateFindHost`) has three fresh states: the anchor, which
   dispatches into the verdict module; the branch, which reads the verdict cell of tape 0 and
   dispatches into the payload or the step module; and the halt.
3. *Budget and fuel.* Every request has length at most `2n + 6 + P n`, so every module's
   polynomial budget, and that of the fuel machine `x ↦ Nat.bits (R|x|)`
   (`polyTimeComputable_unaryPoly R` and `computesFunInTime_lengthBits`, so that the `find?` range
   is exactly `R|x| + 1`), fit `T n = A·(2n + 7 + P n)^D`; the loop combinator's bound
   `c (T n + 1)(R n + 2)` is put in normal form by `PolyExpr.eval_le`.
4. *The derived lemmas* are instances of the state-loop form `polyTimeComputable_stateFind`,
   which runs `iterateFind` on the guarded step `StateLoop.gstep` of a state word `⟨x, s⟩`:
   `iterate` threads a unary counter, tested against `1^{R|x|}` by `IterLoop.acc` (`R|x| ≤ |cnt|`);
   `iterateEmit` also threads an accumulator; the string functions consume their input.

## Main definitions

* `Complexity.guardedStep` — the length-guarded step on the state word `⟨x, s⟩`.
* `Complexity.LoopInv` — the loop invariant `fst w = x ∧ |snd w| ≤ P|x|`.

## Main results

* `Complexity.polyTimeComputable_iterateFind` — the load-bearing lemma (proved: the machine
  is built in `TCSlib.Complexity.Randomized.Build.IterateFind`, and the pure facts below
  identify its guarded orbit with `g^[i] x`).
* `Complexity.polyTimeComputable_iterate`, `Complexity.polyTimeComputable_iterateEmit` —
  `R(|x|)`-fold iteration and concatenated emissions (proved; state loops with a unary round
  counter).
* `Complexity.polyTimeComputable_stateFind` — the state-loop form of the repetition lemma, of
  which the six derived lemmas are instances (proved, from `polyTimeComputable_iterateFind`).
* `Complexity.polyTimeComputable_majority`, `polyTimeComputable_pairXor`,
  `polyTimeComputable_pairEq`, `polyTimeComputable_blockMap` — string tests and the block
  map used by the reductions (proved; state loops consuming the input).
* `Complexity.loopInv_init`, `Complexity.loopInv_guardedStep`,
  `Complexity.iterate_guardedStep_eq`, `Complexity.acc_guardedStep_eq` — the pure facts about
  the guarded step (proved; step 1 of the plan).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 38.5 and Theorem 35.1; Theorem 87.3; Algorithms 123.4 and 128.7.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–1.3, time-bounded machines.)
-/

namespace Complexity

open Turing StateLoop

/-! ### The guarded step and its pure theory (step 1 of the plan) -/

/-- The length-guarded step on the state word `w = ⟨x, s⟩`: advance to `⟨x, g s⟩` if the new
orbit point fits the bound `P|x|`, else stay (DESIGN.md §2.6, step 1). The guard makes the
loop invariant `LoopInv` closed under the step for every state word; on the orbit it is
never taken. -/
def guardedStep (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool) : List Bool :=
  if (g (pairSndD w)).length ≤ P.eval x.length then pairEncode x (g (pairSndD w)) else w

/-- The loop invariant: the state word carries the input `x` in its first component and an
orbit point of length at most `P|x|` in its second. -/
def LoopInv (P : PolyExpr) (x w : List Bool) : Prop :=
  pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length

/-- The initial state word `⟨x, x⟩` satisfies the invariant when `|x| ≤ P|x|` (the case `i = 0`
of the orbit bound). -/
theorem loopInv_init (P : PolyExpr) (x : List Bool) (h0 : x.length ≤ P.eval x.length) :
    LoopInv P x (pairEncode x x) := by
  simp [LoopInv, h0]

/-- The invariant is closed under the guarded step, for every state word: if the new orbit
point fits, the new word is `⟨x, g s⟩`; otherwise the word is unchanged. -/
theorem loopInv_guardedStep (g : List Bool → List Bool) (P : PolyExpr) (x w : List Bool)
    (h : LoopInv P x w) : LoopInv P x (guardedStep g P x w) := by
  unfold guardedStep
  split_ifs with hg
  · simp [LoopInv, hg]
  · exact h

/-- On the orbit the guard is never taken: for `i ≤ R|x|`, the `i`-fold guarded step from
`⟨x, x⟩` is `⟨x, g^[i] x⟩` (induction on `i`, using the orbit bound at `i`). -/
theorem iterate_guardedStep_eq (g : List Bool → List Bool) (R P : PolyExpr) (x : List Bool)
    (horbit : ∀ i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length)
    (i : ℕ) (hi : i ≤ R.eval x.length) :
    (guardedStep g P x)^[i] (pairEncode x x) = pairEncode x (g^[i] x) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (Nat.le_of_succ_le hi)]
    unfold guardedStep
    have hlen : (g (g^[i] x)).length ≤ P.eval x.length := by
      rw [← Function.iterate_succ_apply' g i x]
      exact horbit (i + 1) hi
    simp [hlen, Function.iterate_succ_apply']

/-- The acceptance tests of the loop agree with those of the statement on the whole range
`0, …, R|x|`: `acc (snd ((stepF x)^[i] ⟨x, x⟩)) = acc (g^[i] x)`. -/
theorem acc_guardedStep_eq (g : List Bool → List Bool) (acc : List Bool → Bool) (R P : PolyExpr)
    (x : List Bool)
    (horbit : ∀ i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length)
    (i : ℕ) (hi : i ≤ R.eval x.length) :
    acc (pairSndD ((guardedStep g P x)^[i] (pairEncode x x))) = acc (g^[i] x) := by
  rw [iterate_guardedStep_eq g R P x horbit i hi, pairSndD_pairEncode]

/-! ### The repetition lemma and its instances -/

/-- **The repetition lemma (load-bearing; D11).** Let `g` be a polynomial-time step, `acc` a
polynomial-time acceptance test, `out` a polynomial-time payload map, `R` and `P` syntactic
polynomials such that the orbit `g^[i] x` stays of length `≤ P|x|` for `i ≤ R|x|`. Then the
function "iterate `g` from `x` at most `R|x|` times and return `out` of the first accepted
orbit point, `[]` if none is accepted" is polynomial-time computable. It is the machine
behind every repeated-adversary argument of [PS10]: Algorithm 38.5's `2nm²p(n)` attempts
with first success [PS10, Theorem 35.1], the `n(2^k−1)` calls of Goldreich–Levin
[PS10, Theorem 87.3], rejection sampling (D10), the truncated simulators
[PS10, Algorithms 123.4 and 128.7] (inventory Inf-4.3).

**Proof sketch.** The machine is `Complexity.IterateFind.polyTimeComputable_find`
(`TCSlib.Complexity.Randomized.Build.IterateFind`; its construction is in the module docstring):
it computes `out` of the first accepted point, among the first `R|x| + 1`, of the orbit of
`⟨x, x⟩` under the guarded step `IterateFind.step g P x`, which is `guardedStep g P x`
(`IterateFind.step_eq`). Convert its conclusion to the statement's: for `i ≤ R|x|` the guarded
orbit is `⟨x, g^[i] x⟩` (`iterate_guardedStep_eq`), so the two `find?` predicates agree on the
range (`acc_guardedStep_eq`, `IterateFind.find?_congr_of_mem`), and at the index found the
payloads agree (`iterate_guardedStep_eq`, `pairSndD_pairEncode`). -/
theorem polyTimeComputable_iterateFind {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out : List Bool → List Bool} (hout : PolyTimeComputable out)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x)
      | none => [] := by
  have h := IterateFind.polyTimeComputable_find hg hacc hout R P horbit
  convert h using 1
  funext x
  have hstep : IterateFind.step g P x = guardedStep g P x := by
    funext w
    rw [IterateFind.step_eq]
    rfl
  have hfind : (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) =
      (List.range (R.eval x.length + 1)).find?
        (fun i => acc (pairSndD ((IterateFind.step g P x)^[i] (pairEncode x x)))) := by
    apply IterateFind.find?_congr_of_mem
    intro i hi
    rw [List.mem_range] at hi
    rw [hstep, acc_guardedStep_eq g acc R P x (horbit x) i (by omega)]
  rw [hfind]
  cases hf : (List.range (R.eval x.length + 1)).find?
      (fun i => acc (pairSndD ((IterateFind.step g P x)^[i] (pairEncode x x)))) with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hf
    rw [List.mem_range] at hi
    simp only [hstep, iterate_guardedStep_eq g R P x (horbit x) i (by omega), pairSndD_pairEncode]

/-! ### State loops: the common form of the derived lemmas -/

/-- **State loops** (the common form of the six derived lemmas; DESIGN.md §2.6, step 7). A
state word `⟨x, s⟩` retains the input `x` and evolves its state from `start x` by
`s ↦ step ⟨x, s⟩` (`Complexity.StateLoop.orbit`); a test `acc` on the state word is `false`
before round `N x` and `true` at round `N x ≤ R|x|`, the states up to that round have length at
most `B|x|`, and `out` reads the answer off the final state word. Then
`x ↦ out ⟨x, orbit x (N x)⟩` is polynomial-time computable.

**Proof sketch.** Instance of `polyTimeComputable_iterateFind` on the length-guarded step
`Complexity.StateLoop.gstep step B` (which refuses to move when the new state would exceed
`B|fst w|`), with `R` as the round polynomial and `StateLoop.gstepBound B = 3n + 2 + B(n)` as
the orbit bound — valid for *every* word by `StateLoop.length_gstep_iterate_le`, which is what
`horbit` demands — pre-composed with `x ↦ ⟨x, start x⟩` (`PolyTimeComputable.pairEncode`). On
the genuine orbit the guard never fires (`StateLoop.gstep_iterate_eq`, from the bound on the
first `N x` states), so the loop's `find?` over `List.range (R|⟨x, start x⟩| + 1)` — a range
containing `N x`, as `R` is monotone (`PolyExpr.eval_mono`) — returns `some (N x)`
(`StateLoop.find?_range_eq_some`), and the payload is `out ⟨x, orbit x (N x)⟩`. -/
theorem polyTimeComputable_stateFind {start step : List Bool → List Bool}
    {acc : List Bool → Bool} {out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hacc : PolyTimeComputable fun w => [acc w]) (hout : PolyTimeComputable out)
    (R B : PolyExpr) (N : List Bool → ℕ) (hN : ∀ x, N x ≤ R.eval x.length)
    (hbound : ∀ x i, i ≤ N x → (orbit start step x i).length ≤ B.eval x.length)
    (hfirst : ∀ x i, i < N x → acc (pairEncode x (orbit start step x i)) = false)
    (hlast : ∀ x, acc (pairEncode x (orbit start step x (N x))) = true) :
    PolyTimeComputable fun x => out (pairEncode x (orbit start step x (N x))) := by
  have hF := polyTimeComputable_iterateFind (gstep_poly hstep B) hacc hout R (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  convert hF.comp hpre using 1
  funext x
  simp only [Function.comp_apply]
  have horb := gstep_iterate_eq start step B x (N x) (hbound x)
  have hle : N x ≤ R.eval (pairEncode x (start x)).length :=
    (hN x).trans (R.eval_mono (by rw [length_pairEncode]; omega))
  have hfind : (List.range (R.eval (pairEncode x (start x)).length + 1)).find?
      (fun i => acc ((gstep step B)^[i] (pairEncode x (start x)))) = some (N x) := by
    apply find?_range_eq_some hle
    · intro i hi
      rw [horb i hi.le]
      exact hfirst x i hi
    · rw [horb (N x) le_rfl]
      exact hlast x
  rw [hfind]
  exact (congrArg out (horb (N x) le_rfl)).symm

/-- **Polynomially many iterations:** under the orbit bound, `x ↦ g^[R|x|] x` is
polynomial-time computable (the honest `m(n)`-fold evaluations of [PS10, Theorem 35.1]
and the `ℓ(n)`-fold generator expansion of [PS10, Lemma 80.5] are instances).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.IterLoop`) on the state `⟨1^i, g^[i] x⟩` from `⟨[], x⟩`: the step
appends a token to the unary counter and advances the orbit point (`IterLoop.orbit_eq`);
`acc` is the length test `R|x| ≤ |cnt|` against `1^{R|x|}` of the retained input
(`polyTimeComputable_unaryPoly R`, `polyTimeComputable_lenLe`), `false` below round `R|x|`
and `true` there; `out` projects the orbit point. The states of the first `R|x|` rounds have
length `2i + 2 + |g^[i] x| ≤ 2R|x| + 2 + P|x|` by `horbit`. -/
theorem polyTimeComputable_iterate {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x => g^[R.eval x.length] x := by
  have hbound : ∀ x i, i ≤ R.eval x.length →
      (orbit IterLoop.start (IterLoop.step g) x i).length ≤
        (PolyExpr.add (.mul (.const 2) R) (.add (.const 2) P)).eval x.length := by
    intro x i hi
    rw [IterLoop.orbit_eq, length_pairEncode, List.length_replicate]
    have := horbit x i hi
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hfirst : ∀ x i, i < R.eval x.length →
      IterLoop.acc R (pairEncode x (orbit IterLoop.start (IterLoop.step g) x i)) = false := by
    intro x i hi
    rw [IterLoop.orbit_eq]
    simp [IterLoop.acc_eq, hi]
  have hlast : ∀ x, IterLoop.acc R
      (pairEncode x (orbit IterLoop.start (IterLoop.step g) x (R.eval x.length))) = true := by
    intro x
    rw [IterLoop.orbit_eq]
    simp [IterLoop.acc_eq]
  have h := polyTimeComputable_stateFind IterLoop.start_poly (IterLoop.step_poly hg)
    (IterLoop.acc_poly R) IterLoop.out_poly R _ (fun x => R.eval x.length) (fun _ => le_rfl)
    hbound hfirst hlast
  convert h using 1
  funext x
  rw [IterLoop.orbit_eq]
  simp [IterLoop.out_eq]

/-- **Polynomially many iterations with concatenated emissions:** under the orbit bound,
`x ↦ emit x ++ emit (g x) ++ ⋯ ++ emit (g^[R|x|] x)` is polynomial-time computable (the
`m − 1` evaluations of `f` whose outputs form the tuple of Algorithm 38.5, the block
evaluations of `prodFun`, the lazily sampled GGM table).

**Proof sketch.** As `polyTimeComputable_iterate` (state loop, data in
`Complexity.StateLoop.EmitLoop`), with the state `⟨1^i, ⟨g^[i] x, acc_i⟩⟩` where
`acc_i = (List.range i).flatMap (emit ∘ g^[·] x)`: the step appends `emit` of the current
orbit point to the accumulator (`PolyTimeComputable.append`) before advancing
(`EmitLoop.orbit_eq`); the counter test `IterLoop.acc R` fires first at round `R|x|`, where
`out` returns `acc_i ++ emit (g^[i] x)` (`List.range_succ`, `List.flatMap_append`). The
accumulator is bounded by `R|x| · C (P|x| + 1)^c` with `C, c` from `hemit.output_length_le`
(`StateLoop.length_flatMap_range_le`), the `PolyExpr` `R · (normal C c)[P/n]`
(`PolyExpr.eval_subst`). -/
theorem polyTimeComputable_iterateEmit {g emit : List Bool → List Bool}
    (hg : PolyTimeComputable g) (hemit : PolyTimeComputable emit) (R P : PolyExpr)
    (horbit : ∀ (x : List Bool) (i : ℕ), i ≤ R.eval x.length →
      (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x) := by
  obtain ⟨Ce, ce, hCe⟩ := hemit.output_length_le
  have hbound : ∀ x i, i ≤ R.eval x.length →
      (orbit EmitLoop.start (EmitLoop.step g emit) x i).length ≤
        (PolyExpr.add (.mul (.const 2) R) (.add (.const 4) (.add (.mul (.const 2) P)
          (.mul R ((PolyExpr.normal Ce ce).subst P))))).eval x.length := by
    intro x i hi
    rw [EmitLoop.orbit_eq, length_pairEncode, length_pairEncode, List.length_replicate]
    have h1 := horbit x i hi
    have hchunk : ∀ j < i, (emit (g^[j] x)).length ≤ Ce * (P.eval x.length + 1) ^ ce := by
      intro j hj
      refine (hCe _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      have := horbit x j (by omega)
      omega
    have h2 := (length_flatMap_range_le _ _ i hchunk).trans (Nat.mul_le_mul_right _ hi)
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_subst,
      PolyExpr.eval_normal]
    generalize R.eval x.length * (Ce * (P.eval x.length + 1) ^ ce) = Q at h2
    omega
  have hfirst : ∀ x i, i < R.eval x.length →
      IterLoop.acc R (pairEncode x (orbit EmitLoop.start (EmitLoop.step g emit) x i)) = false := by
    intro x i hi
    rw [EmitLoop.orbit_eq]
    simp [IterLoop.acc_eq, hi]
  have hlast : ∀ x, IterLoop.acc R (pairEncode x
      (orbit EmitLoop.start (EmitLoop.step g emit) x (R.eval x.length))) = true := by
    intro x
    rw [EmitLoop.orbit_eq]
    simp [IterLoop.acc_eq]
  have h := polyTimeComputable_stateFind EmitLoop.start_poly (EmitLoop.step_poly hg hemit)
    (IterLoop.acc_poly R) (EmitLoop.out_poly hemit) R _ (fun x => R.eval x.length)
    (fun _ => le_rfl) hbound hfirst hlast
  convert h using 1
  funext x
  rw [EmitLoop.orbit_eq]
  simp [EmitLoop.out_eq, List.range_succ]

/-- **Majority vote** on a bit string: `w ↦ [decide (|w| < 2 · #true w)]` (strict majority of
`true`) is polynomial-time computable (the vote of the Goldreich–Levin inverter
[PS10, Algorithm 89.6] and of the next-bit predictor).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.MajLoop`) with `R := var` on the state `⟨rest, ⟨1^{#true}, 1^{#false}⟩⟩`
from `⟨w, ⟨[], []⟩⟩`: each step drops the first bit of `rest` (`StateLoop.tail_poly`) and
appends a token to the counter of its value (`StateLoop.headBit_poly`,
`polyTimeComputable_ite`), so after `i ≤ |w|` rounds the state is
`⟨w.drop i, ⟨1^{#true (w.take i)}, 1^{#false (w.take i)}⟩⟩` (`MajLoop.orbit_eq`); `acc` is the
emptiness test on `rest`, first `true` at round `|w|`; `out` is the length test
`|1 :: 1^{#false}| ≤ |1^{#true}|` (`polyTimeComputable_lenLe`), which is the verdict since
`|w| < 2 #true ↔ #false + 1 ≤ #true` (`List.count_true_add_count_false`). States have length
at most `5|w| + 4`. -/
theorem polyTimeComputable_majority :
    PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)] := by
  have h := polyTimeComputable_stateFind MajLoop.start_poly MajLoop.step_poly MajLoop.acc_poly
    MajLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 4)) List.length (fun _ => le_rfl)
    (fun w i hi => by simpa using MajLoop.orbit_length_le w i hi) MajLoop.acc_orbit_false
    MajLoop.acc_orbit_true
  convert h using 1
  funext w
  exact (MajLoop.out_orbit w).symm

/-- **Bitwise exclusive-or of the two components of a pair** (`List.zipWith xor`) is
polynomial-time computable (the one-time pad of [PS10, Algorithm 92.1 and 99.1] and the
hard-core-bit mask of [PS10, Algorithm 104.3]).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.XorLoop`) with `R := var` on the state `⟨a', ⟨b', c⟩⟩` from
`⟨fst z, ⟨snd z, []⟩⟩`: each step drops the heads of `a'`, `b'` and appends their xor to `c`
(`StateLoop.tail_poly`, `StateLoop.headBit_poly`, `StateLoop.xor_poly`), so after
`i ≤ min |a| |b|` rounds the state is `⟨a.drop i, ⟨b.drop i, (zipWith xor a b).take i⟩⟩`
(`XorLoop.orbit_eq`, by `List.take_succ` and `List.getElem?_zipWith`); `acc` is "one of `a'`,
`b'` is empty" (`StateLoop.isNil_poly`, `StateLoop.or_poly`), first `true` at round
`min |a| |b| = |zipWith xor a b|` (`List.length_zipWith`), where `out` returns `c`. States have
length at most `5|z| + 4` (`StateLoop.length_pairFstD_add_pairSndD_le`). -/
theorem polyTimeComputable_pairXor :
    PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z) := by
  have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    rw [XorLoop.rounds_eq]
    simp only [PolyExpr.eval_var]
    omega
  have h := polyTimeComputable_stateFind XorLoop.start_poly XorLoop.step_poly XorLoop.acc_poly
    XorLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 4)) XorLoop.rounds hN
    (fun z i hi => by simpa using XorLoop.orbit_length_le z i hi) XorLoop.acc_orbit_false
    XorLoop.acc_orbit_true
  convert h using 1
  funext z
  exact (XorLoop.out_orbit z).symm

/-- **Equality test of the two components of a pair** (`[decide (fst z = snd z)]`) is
polynomial-time computable (the test `f(z_i) = y` of [PS10, Algorithm 38.5] and every
verification step of the reductions).

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.EqLoop`) with `R := var` on the state `⟨a', ⟨b', flag⟩⟩` from
`⟨fst z, ⟨snd z, []⟩⟩`: each step drops the heads of `a'`, `b'` and sets `flag := [true]` if
they differ (`polyTimeComputable_ite` on `StateLoop.xor_poly`), so after `i ≤ min |a| |b|`
rounds the state is `⟨a.drop i, ⟨b.drop i, flag⟩⟩` with `flag = []` iff `a.take i = b.take i`
(`EqLoop.orbit_eq`, `EqLoop.flag_succ`); `acc` is `XorLoop.acc` ("one of `a'`, `b'` is
empty"), first `true` at round `min |a| |b|`, where `out` is the conjunction of the three
emptiness tests `a' = [] ∧ b' = [] ∧ flag = []` (`polyTimeComputable_and`), i.e. `a = b`
(`EqLoop.verdict_eq`: equal lengths and equal prefixes). States have length at most
`5|z| + 5`. -/
theorem polyTimeComputable_pairEq :
    PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)] := by
  have hN : ∀ z, XorLoop.rounds z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    rw [XorLoop.rounds_eq]
    simp only [PolyExpr.eval_var]
    omega
  have h := polyTimeComputable_stateFind XorLoop.start_poly EqLoop.step_poly XorLoop.acc_poly
    EqLoop.out_poly .var (.add (.mul (.const 5) .var) (.const 5)) XorLoop.rounds hN
    (fun z i hi => by simpa using EqLoop.orbit_length_le z i hi) EqLoop.acc_orbit_false
    EqLoop.acc_orbit_true
  convert h using 1
  funext z
  exact (EqLoop.out_orbit z).symm

/-- **Block map:** apply `g` to the consecutive blocks of length `b(|fst z|)` of `snd z` and
concatenate (the first component carries `1^n`; the `⌊|snd z| / b(n)⌋` full blocks are
mapped, a partial last block is dropped). This evaluates `prodFun f q` blockwise
[PS10, Theorem 35.1, Algorithm 38.5] and decodes tuples of `n`-bit strings.

**Proof sketch.** State loop (`polyTimeComputable_stateFind`, data in
`Complexity.StateLoop.BlockMapLoop`) with `R := var` (at most `|z|` blocks) on the state
`⟨rest, c⟩` from `⟨snd z, []⟩`, with `k := b(|fst z|)` read off the retained input: each step
drops `k` bits of `rest` and appends `g (rest.take k)` to `c` (`polyTimeComputable_pairDropPoly b`,
`polyTimeComputable_pairTakePoly b` on `⟨fst z, rest⟩`), so after `i` rounds the state is
`⟨(snd z).drop (i k), g (block 0) ++ ⋯ ++ g (block (i − 1))⟩` (`BlockMapLoop.orbit_eq`,
`List.drop_drop`); `acc` is "`|rest| < k` or `k = 0`" (two length tests against `1^k`), `false`
below round `|snd z| / k` and `true` there (`Nat.le_div_iff_mul_le`, `Nat.lt_mul_div_succ`),
where `out` returns `c`, the statement's `flatMap`. States have length at most
`2|z| + 2 + |z| · C (b(|z|) + 1)^c` with `C, c` from `hg.output_length_le`. -/
theorem polyTimeComputable_blockMap (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z =>
      (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
        g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length)) := by
  obtain ⟨C, c, hC⟩ := hg.output_length_le
  have hN : ∀ z, BlockMapLoop.rounds b z ≤ PolyExpr.var.eval z.length := by
    intro z
    have := length_pairFstD_add_pairSndD_le z
    rw [BlockMapLoop.rounds_eq]
    exact (Nat.div_le_self _ _).trans (by simp only [PolyExpr.eval_var]; omega)
  have h := polyTimeComputable_stateFind BlockMapLoop.start_poly (BlockMapLoop.step_poly b hg)
    (BlockMapLoop.acc_poly b) BlockMapLoop.out_poly .var _ (BlockMapLoop.rounds b) hN
    (BlockMapLoop.orbit_length_le b g C c hC) (BlockMapLoop.acc_orbit_false b g)
    (BlockMapLoop.acc_orbit_true b g)
  convert h using 1
  funext z
  rw [BlockMapLoop.out_orbit, BlockMapLoop.rounds_eq]

end Complexity

## ===== TCSlib/Complexity/Randomized/NonUniform.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.CircuitComplexity.Advice

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Non-uniform PPT: the two formulations of Definition 26.8

[PS10, Definition 26.8] defines a non-uniform probabilistic polynomial-time machine in two
ways. **Machine-sequence form:** a sequence `A = {A₁, A₂, …}` of probabilistic machines with
a polynomial `d` such that `|Aᵢ| < d(i)` and the running time of `Aᵢ` is less than `d(i)`;
`A(x)` denotes the distribution obtained by running `A_{|x|}(x)`. **Advice form** ("alternatively"):
a uniform p.p.t. machine `A` that receives an advice string for each input length. The text
adds that "any adversarial algorithm `A` will implicitly be a non-uniform PPT", the standing
convention governing Definitions 26.1, 27.3, 28.4, 41.1(4), 56.1(5) and the hardness
assumptions.

The frozen definition is the advice form, `Complexity.NUPPT` of
`TCSlib.Complexity.Randomized.PPT` (foundation decision D4): `advice n` of length
`≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
`A_{|y|}(y)` of the text is `NUPPT.runLit y r := runAt |y| y r` — the prefix `1^{|y|}` carries
no information — and it is the layout of the literal forms of Definition 26.1
(`WorstCaseOneWay`, `inverterLit`) and Definition 69.4 (`Ensemble.IndistLit`). The
machine-sequence form is reflected only as a sanity statement here: at every parameter `n`
the activation is a deterministic polynomial-time function of `(y, r)`
(`NUPPT.polyTimeComputable_runAtL`). The machine of that statement hard-wires `1^n` and
`advice n`, so its size and its time constants depend on `n`: the lemma bounds neither the
size of "`A_n`" nor its running time uniformly in `n` (it would hold equally with
exponentially long advice). The polynomial size of Definition 26.8's `A_n` comes from
`|advice n| ≤ adv.eval n` (the field `NUPPT.advice_length`), not from this lemma.

**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). The equivalence of the two forms (`NUPPTSeq`, `nuppt_seq_iff_advice`, with
`Turing.CodeTM.serialize` as the description size, `⇒` through `Turing.timed_universal`) is
the optional module `Randomized/Sequence.lean` with one named admission; no theorem of
chapters 2–4 depends on it.

This file also holds the uniformity lemmas (a PPT is an `NUPPT` with empty advice,
`Complexity.PPT` the subtype) and the **optional** sanity bridge to the library's
advice-taking machines `Turing.FinTM.DecidesWithAdviceInTime` [AB09, Definition 6.16]
(`NUPPT.decides_of_decidesWithAdviceInTime`, stated with its sketch; it needs the clocking
construction `NUPPT.ofPartial` and is off every critical path).

## Main definitions

* `Complexity.PPT.toNUPPT`, `Complexity.PPT.ofPolyTime` — the subtype API of PPTs.

## Main results

* `Complexity.NUPPT.runLit_eq_runAt`, `NUPPT.runLit_eq_runAtL` — the literal activation
  unfolds to the activation at parameter `|y|`.
* `Complexity.NUPPT.Uniform.advice_eq`, `NUPPT.Uniform.runAtL_eq`, `NUPPT.Uniform.runAt_eq`,
  `NUPPT.ofPolyTime_uniform` — uniform machines run on `⟨⟨⟨1^n, y⟩, []⟩, r⟩`.
* `Complexity.NUPPT.polyTimeComputable_runAtL` — at a fixed parameter the activation is a
  deterministic polynomial-time function of `(y, r)`, with constants that depend on `n` (not a
  uniform size bound on the "`A_n`" of the machine-sequence form).
* `Complexity.NUPPT.decides_of_decidesWithAdviceInTime` — (optional, sorried) a language
  decided with polynomial advice in polynomial time [AB09, Definition 6.16] is decided by an
  `NUPPT` at the input length.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1.3, Definition 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.3, Definition 6.16, machines with advice.)
-/

namespace Complexity

open Turing

namespace NUPPT

variable (A : NUPPT)

/-- The literal activation `A_{|y|}(y)` is the activation at parameter `|y|`
[PS10, Definition 26.8, "`A(x)` denotes `A_{|x|}(x)`"]. -/
theorem runLit_eq_runAt (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAt y.length y r := rfl

/-- The literal activation with the coins as a list. -/
theorem runLit_eq_runAtL (y : List Bool) (r : A.Coins y.length) :
    A.runLit y r = A.runAtL y.length y (List.ofFn r) := rfl

/-- A uniform machine has empty advice at every parameter. -/
theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = [] := h n

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩`: the advice slot is empty. -/
theorem Uniform.runAtL_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, h n]

/-- A uniform machine runs on the layout `⟨⟨⟨1^n, y⟩, []⟩, r⟩` (typed coins). -/
theorem Uniform.runAt_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.output (pairEncode (pairEncode (advInput n y) []) (List.ofFn r)) := by
  rw [NUPPT.runAt_eq, h.runAtL_eq]

/-- `ofPolyTime` with an everywhere-empty advice function is uniform. -/
theorem ofPolyTime_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (h : ∀ n, advice n = []) : (ofPolyTime hf coins adv advice hα).Uniform := h

/-- Uniformity is the conjunction of the advice clauses (definitional unfolding). -/
theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = [] := Iff.rfl

/-- The literal activation of a uniform polynomial-time machine is `f` on
`⟨⟨⟨1^{|y|}, y⟩, []⟩, r⟩`. -/
theorem runLit_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (y : List Bool) (r : (ofPolyTimeUniform hf coins).Coins y.length) :
    (ofPolyTimeUniform hf coins).runLit y r =
      f (pairEncode (pairEncode (advInput y.length y) []) (List.ofFn r)) := by
  rw [runLit_eq_runAtL, runAtL_ofPolyTimeUniform]

/-- **The machine-sequence view, sanity direction.** At each fixed parameter `n`, the
activation of `A` is a deterministic polynomial-time function of the pair `⟨y, r⟩`
[PS10, Definition 26.8, first formulation, the "`A_n`"]. The machine hard-wires `1^n` and
`advice n`, so its size and its time constants depend on `n`: the statement is per `n` and
would hold equally with exponentially long advice. It is **not** the polynomial-size half of
Definition 26.8; that half comes from `|advice n| ≤ adv.eval n` (`NUPPT.advice_length`), not
from this lemma.

**Proof sketch.** The raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` is assembled from `⟨y, r⟩` by
`PolyTimeComputable.pairEncode` with the constant strings `1^n` and `advice n`
(`polyTimeComputable_const`) and the projections `pairFstD`/`pairSndD`; then
`NUPPT.polyTimeComputable_output`. -/
theorem polyTimeComputable_runAtL (n : ℕ) :
    PolyTimeComputable fun z => A.runAtL n (pairFstD z) (pairSndD z) := by
  have h := A.polyTimeComputable_output.comp
    ((((polyTimeComputable_const (List.replicate n true)).pairEncode
      polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_const (A.advice n))).pairEncode
      polyTimeComputable_pairSndD)
  convert h using 1

/-- **Optional sanity bridge** (not on the critical path): a language decided by a machine
with polynomial-length advice within polynomial time [AB09, Definition 6.16]
(`Turing.FinTM.DecidesWithAdviceInTime`) is decided by an `NUPPT` activated at the input
length, i.e. by a non-uniform PPT in the sense of [PS10, Definition 26.8]. The two advice
notions agree: `α n` becomes the advice at parameter `n` and the time bound in `|x|` becomes
a bound in the machine-input length.

**Proof sketch.** The hypothesis bounds `M` only on the well-formed inputs
`pairEncode x (α |x|)`; the `NUPPT` must halt on every input, so `M` is first clocked:
`Turing.timed_universal` run on `⟨⟨bits (C (m+1)^c), code M⟩, w⟩` halts on every `w`
within a polynomial of `|w|` and agrees with `M` whenever `M` halts within the clock
(this is the optional lemma `NUPPT.ofPartial`). The `NUPPT` `A` has advice `α n` (length
`Ca (n+1)^ca = (normal Ca ca).eval n`, so `adv := normal Ca ca`), no coins (`coins := const 0`),
and output function `z ↦ clockedM (pairEncode (inArg z) (inAdvice z))` where `inArg`/`inAdvice`
are the projections of the raw layout (FP by the pairing calculus). On the raw input
`⟨⟨⟨1^{|x|}, x⟩, α |x|⟩, r⟩` the re-pairing is `pairEncode x (α |x|)`, on which `M` halts within
`C (|x|+1)^c` with output `[indicator L x]` (hypothesis `h x`), so the clocked machine returns
the same by determinism (`NUPPT.output_eq_of_computesInTime`). -/
theorem decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x] := by
  sorry

end NUPPT

namespace PPT

/-- The underlying non-uniform machine of a PPT. -/
def toNUPPT (A : PPT) : NUPPT := A.1

/-- A PPT has empty advice. -/
theorem uniform (A : PPT) : A.toNUPPT.Uniform := A.2

/-- The PPT with output function `f` and coin polynomial `coins`
(`Complexity.NUPPT.ofPolyTimeUniform`). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : PPT :=
  ⟨NUPPT.ofPolyTimeUniform hf coins, NUPPT.ofPolyTimeUniform_uniform hf coins⟩

/-- The underlying machine of `PPT.ofPolyTime hf coins` is `NUPPT.ofPolyTimeUniform hf coins`. -/
theorem toNUPPT_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTime hf coins).toNUPPT = NUPPT.ofPolyTimeUniform hf coins := rfl

end PPT

end Complexity

## ===== TCSlib/Cryptography/Asymptotic/Adversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as adversaries of the concrete experiments

The bridge between the machine layer (`Complexity.NUPPT`, strings `List Bool`) and the
concrete security experiments of `TCSlib.Cryptography.Foundations.Experiments` (typed
inputs `Fin m → Bool`, adversaries as functions of the input and of a uniform coin string).
An `NUPPT` `A` activated at parameter `n` becomes

* an *inverter* `A.inverter n ℓ m : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)`
  [PS10, Definitions 27.3, 28.4]: `A(1^n, y)` with the output decoded as an `ℓ`-bit string;
* its literal variant `A.inverterLit ℓ m` for [PS10, Definition 26.1] (`A(f(x))`, activation
  at the input length `m`, no `1^n`);
* a *distinguisher* / *predictor* `A.distinguisher n m`, `A.predictor n m`
  [PS10, Definitions 69.4, 75.2, 78.3]: `A(1^n, t) = 1`, i.e. the output is the string `[true]`;
  `A.distinguisherL n` takes an untyped sample.

Inversion with a possibly failing decoder is `invProbOpt` (the probability that the decoded
output is a preimage); it is bridged to the concrete `invProb` by `invProbOpt_le_invProb`
(any default for a failure can only increase the probability) and `invProbOpt_some` (a total
inverter has the same probability). Foundation decision D5: inverses are sought in the
domain at the current parameter, and a wrong-length output counts as failure.

The file also records that "computes `f` with probability one" [PS10, Definition 24.6]
is, on the finite uniform coin space, the same as "for every coin string"
(`Complexity.NUPPT.computes_iff_uprob`), which justifies the frozen form of
`Complexity.NUPPT.Computes`.

**Deviation:** `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable
by `ifEq`).

## Main definitions

* `TCSlib.Cryptography.decodeFin` — decode a string as an `ℓ`-bit string, failure on a wrong
  length; `TCSlib.Cryptography.padFin` — pad/truncate (for samplers).
* `Complexity.NUPPT.inverter`, `Complexity.NUPPT.inverterLit` — an `NUPPT` as an inverter
  (with `1^n`, and literal).
* `Complexity.NUPPT.distinguisher`, `Complexity.NUPPT.distinguisherL`,
  `Complexity.NUPPT.predictor` — an `NUPPT` as a distinguisher / predictor.
* `TCSlib.Cryptography.invProbOpt` — inversion probability of a possibly failing inverter.

## Main results

* `TCSlib.Cryptography.decodeFin_ofFn`, `TCSlib.Cryptography.padFin_ofFn` — decoding and
  padding invert `List.ofFn`.
* `TCSlib.Cryptography.invProbOpt_le_invProb`, `TCSlib.Cryptography.invProbOpt_some` — the
  bridges to the concrete `invProb`.
* `TCSlib.Cryptography.invProbOpt_nonneg`, `TCSlib.Cryptography.invProbOpt_le_one` — bounds.
* `Complexity.NUPPT.computes_iff_uprob` — probability one is every coin string
  [PS10, Definition 24.6].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1–2.2: Definitions 24.6, 26.1, 27.3; §3.1–3.3: Definitions 69.4, 75.2, 78.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definitions 2.1, 2.3, 3.2–3.4 (the concrete experiments).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-- Decode a string as an `ℓ`-bit string: `some` of its bits if the length is exactly `ℓ`,
`none` otherwise (a wrong-length answer of an inverter is a failure, D5). -/
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool) :=
  if h : w.length = ℓ then some (fun i => w.get (Fin.cast h.symm i)) else none

/-- Pad with `false` or truncate a string to exactly `ℓ` bits (the output convention of
samplers, where no failure is possible). -/
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i false

/-- Decoding the encoding of an `ℓ`-bit string returns it. -/
theorem decodeFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : decodeFin ℓ (List.ofFn x) = some x := by
  simp [decodeFin]

/-- A decoded string has exactly the decoded length. -/
theorem length_eq_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : w.length = ℓ := by
  by_contra hw
  simp [decodeFin, hw] at h

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padFin_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padFin ℓ (List.ofFn x) = x := by
  funext i
  simp [padFin]

/-- `A(1^n, y)` as an inverter: output decoded as an `ℓ`-bit string, wrong length = failure
[PS10, Definitions 27.3 and 28.4, the experiment `f(A(1^n, y)) = y`].

**Deviation:** wrong-length output = failure (D5). For a typed family this loses nothing. For
a string function `f : {0,1}* → {0,1}*` the text's experiment also accepts a preimage of
another length, so the typed experiment can count fewer successes and typed one-wayness is
implied by, but weaker than, the text's, unless `|f(x)|` determines `|x|` (length-regular `f`
with non-constant output length; with constant output length neither notion is
satisfiable). The proviso is stated where string functions enter the typed world,
`FunFamily.ofString` (`Asymptotic/OneWay.lean`; gate 03a, note 15). -/
def _root_.Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt n (List.ofFn y) r)

/-- The literal inverter `A(y)` of [PS10, Definition 26.1]: activation at parameter `|y| = m`
(the text gives the adversary `f(x)` only; the `1^{|y|}` prefix carries no information). -/
def _root_.Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) :
    (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool) :=
  fun y r => decodeFin ℓ (A.runAt m (List.ofFn y) r)

/-- `A(1^n, t)` as a distinguisher: accepts iff the output is the string `[true]`
[PS10, Definition 69.4]. -/
def _root_.Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  fun t r => decide (A.runAt n (List.ofFn t) r = [true])

/-- `A(1^n, w)` as a distinguisher of untyped samples (ciphertexts, views, histories). -/
def _root_.Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool :=
  fun w r => decide (A.runAt n w r = [true])

/-- `A(1^n, y)` as a predictor of a bit: the same verdict convention as a distinguisher
[PS10, Definitions 75.2 and 78.3]. -/
def _root_.Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) :
    (Fin m → Bool) → A.Coins n → Bool :=
  A.distinguisher n m

/-- The literal inverter is the inverter at parameter `m`. -/
theorem _root_.Complexity.NUPPT.inverterLit_eq (A : NUPPT) (ℓ m : ℕ) :
    A.inverterLit ℓ m = A.inverter m ℓ m := rfl

/-- The typed distinguisher is the untyped one on `List.ofFn t`. -/
theorem _root_.Complexity.NUPPT.distinguisher_eq (A : NUPPT) (n m : ℕ) (t : Fin m → Bool)
    (r : A.Coins n) : A.distinguisher n m t r = A.distinguisherL n (List.ofFn t) r := rfl

/-- The predictor is the distinguisher. -/
theorem _root_.Complexity.NUPPT.predictor_eq (A : NUPPT) (n m : ℕ) :
    A.predictor n m = A.distinguisher n m := rfl

/-- The inverter succeeds on `(y, r)` iff the machine's output is the encoding of some `x'`. -/
theorem _root_.Complexity.NUPPT.inverter_eq_some_iff (A : NUPPT) (n ℓ m : ℕ) (y : Fin m → Bool)
    (r : A.Coins n) (x' : Fin ℓ → Bool) :
    A.inverter n ℓ m y r = some x' ↔ A.runAt n (List.ofFn y) r = List.ofFn x' := by
  constructor
  · intro h
    have hw : (A.runAt n (List.ofFn y) r).length = ℓ := length_eq_of_decodeFin_eq_some h
    simp only [NUPPT.inverter, decodeFin, dif_pos hw, Option.some.injEq] at h
    subst h
    refine List.ext_get (by simp [hw]) fun i h₁ h₂ => ?_
    simp
  · intro h
    show decodeFin ℓ _ = _
    rw [h, decodeFin_ofFn]

/-- The probability that a possibly failing inverter `A`, given `f x` for uniform `x` and
uniform coins, outputs `some x'` with `f x' = f x` (the typed experiment of
[PS10, Definition 27.3] with a wrong-length output counted as failure, D5). -/
noncomputable def invProbOpt {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : ℝ :=
  uprob fun z : α × ρ => ∃ x', A (f z.1) z.2 = some x' ∧ f x' = f z.1

/-- Replacing a failure by any default can only increase the inversion probability: the
bridge from `invProbOpt` to the concrete `invProb` [Gar26, Definition 2.1]. -/
theorem invProbOpt_le_invProb {α β ρ : Type*} [Fintype α] [Fintype ρ] [Inhabited α] (f : α → β)
    (A : β → ρ → Option α) :
    invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default) := by
  refine uprob_mono ?_
  rintro ⟨x, r⟩ ⟨x', hx', hf⟩
  simp [hx', hf]

/-- A total inverter has the same probability under both conventions. -/
theorem invProbOpt_some {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → α) :
    invProbOpt f (fun y r => some (A y r)) = invProb f A := by
  unfold invProbOpt invProb
  congr 1
  funext z
  simp

/-- The inversion probability is nonnegative. -/
theorem invProbOpt_nonneg {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : 0 ≤ invProbOpt f A :=
  uprob_nonneg _

/-- The inversion probability is at most one. -/
theorem invProbOpt_le_one {α β ρ : Type*} [Fintype α] [Fintype ρ] (f : α → β)
    (A : β → ρ → Option α) : invProbOpt f A ≤ 1 :=
  uprob_le_one _

/-- An event of probability one holds everywhere (private copy of
`TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one`, which lives in a frozen file). -/
private theorem forall_of_uprob_eq_one {Ω : Type*} [Fintype Ω] {p : Ω → Prop}
    (h : uprob p = 1) (ω : Ω) : p ω := by
  classical
  rw [uprob_eq_card_filter] at h
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at h; exact zero_ne_one h
  have hcard : (univ.filter p).card = Fintype.card Ω := by
    have := (div_eq_one_iff_eq hc).1 h
    exact_mod_cast this
  have := Finset.eq_univ_of_card _ hcard
  have hω : ω ∈ univ.filter p := by rw [this]; exact mem_univ ω
  exact (mem_filter.1 hω).2

/-- **"With probability one" is "for every coin string"** [PS10, Definition 24.6]: `A`
computes `f` in the frozen sense (`Complexity.NUPPT.Computes`, equality for every coin
string) iff at every parameter and argument the event `A(1^n, y; r) = f(⟨1^n, y⟩)` has
probability one over the uniform coins. (On a finite uniform space an event of probability
one is the whole space.) -/
theorem _root_.Complexity.NUPPT.computes_iff_uprob (A : NUPPT) (f : List Bool → List Bool) :
    A.Computes f ↔
      ∀ n y, uprob (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = 1 := by
  constructor
  · intro h n y
    have hp : (fun r : A.Coins n => A.runAt n y r = f (NUPPT.advInput n y)) = fun _ => True :=
      funext fun r => propext ⟨fun _ => trivial, fun _ => h n y r⟩
    rw [hp, uprob_true]
  · intro h n y r
    exact forall_of_uprob_eq_one (h n y) r

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Sampling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sampling devices: statistical closeness, rejection sampling, random permutations

The one sampling device of the Pass–shelat campaign (foundation decision D10). Experiments
are stated with *ideal* uniform distributions, exactly as in [PS10]; honest parties and
reductions, which only have uniform coin strings, sample these distributions by truncated
rejection sampling, and every theorem carries the explicit statistical term. The file is
concrete-layer only: no machines, one security parameter at a time.

* `StatClose X Y δ` — two samplers from uniform seeds are statistically `δ`-close: every
  test set has probabilities under the two laws differing by at most `δ` (the
  sup-over-test-sets form of the statistical distance, usable for samples in an infinite type
  such as `List Bool`). It is closed under post-processing (`StatClose.map`), products
  (`StatClose.prod`), composition (`StatClose.trans`) and reparametrisation of the seed by a
  uniform-preserving map (`StatClose.comp_pushesUniform`), and bounds every distinguishing
  advantage (`distAdv_le_of_statClose`) and, more generally, every success probability of an
  experiment with auxiliary coins (`StatClose.abs_uprob_sub_le_prod`) — the statistical-switch
  lemma C10 of the Chapter 2 inventory.
* `HardcoreBit.PushesUniform` from equal fibres (`pushesUniform_of_card_fiber`, lemma C5): a map
  all of whose fibres have the same size pushes uniform to uniform (`QR_N` sampling by squaring,
  [PS10, Corollary 60.6, Theorem 63.10]).
* `firstHit E xs` — the first of `T` draws satisfying `E`: uniform on `E` conditioned on
  existence, and no hit with probability `(1 - Pr[E])^T` (lemma C4, [PS10, Lemma 51.17]).
* `rejectionSample m k T` — `T` trials of `k` bits read as a number, the first one below `m`:
  uniform on `Fin m` conditioned on `some`, `none` with probability `(1 - m/2^k)^T`, and the
  total sampler obtained by falling back to a default is `StatClose` to uniform within that
  term. This is the uniform position of [PS10, Theorem 35.1] and the samplers of `Π_n`, `Z_q`,
  `Z_N^*` and `QR_N` of [PS10, §2.6–§2.12].
* `statClose_getD_of_uniform_of_some` — a sampler that is uniform conditioned on success,
  made total by a default, is `StatClose` to uniform within its failure probability (C4 in
  abstract form); `one_sub_inv_pow_le_half` — `(1 - 1/m)^m ≤ 1/2`, the dyadic form of
  "`(1 - 1/m)^m ≈ e^{-1}`" used for the closed forms of the failure terms.
* The permutation sampler `permFromCoins n k T` (Fisher–Yates with rejection-sampled
  offsets, the permutations of [PS10, Protocols 118.3, 120.6 and 127.5]) and the campaign
  parameters `permBits`, `permTrials` live in `Asymptotic/Permutations.lean`
  (file-size limit).

**Deviation:** [PS10] samples primes, residues and permutations exactly, in expected
polynomial time; here every such sampler is truncated to `T` trials and the experiments carry
an explicit statistical term (D10, deviations register #15).

**Repair (run-3 audit P2-1):** the general closeness lemma `statClose_getD_of_uniform_of_some`,
the seed reparametrisation `StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` were
added for the permutation sampler, whose section moved to `Asymptotic/Permutations.lean`.

## Main definitions

* `TCSlib.Cryptography.StatClose` — statistical `δ`-closeness of two samplers.
* `TCSlib.Cryptography.bitsToNat`, `TCSlib.Cryptography.bitsEquiv` — a `k`-bit string as a
  number below `2^k`, and the resulting bijection with `Fin (2^k)`.
* `TCSlib.Cryptography.uniformFromBits`, `TCSlib.Cryptography.rejectionSample` — one rejection
  trial, and `T` trials.
* `TCSlib.Cryptography.firstHit` — the first of `T` draws satisfying a predicate.

## Main results

* `TCSlib.Cryptography.StatClose.abs_uprob_sub_le_prod`,
  `TCSlib.Cryptography.distAdv_le_of_statClose` — the statistical-switch lemma (C10).
* `TCSlib.Cryptography.StatClose.map`, `TCSlib.Cryptography.StatClose.prod`,
  `TCSlib.Cryptography.StatClose.trans`, `TCSlib.Cryptography.StatClose.comp_pushesUniform`
  — closure properties.
* `TCSlib.Cryptography.pushesUniform_of_card_fiber` — equal fibres push uniform to uniform (C5).
* `TCSlib.Cryptography.firstHit_uniform_of_some`, `TCSlib.Cryptography.uprob_firstHit_none`,
  `TCSlib.Cryptography.statClose_firstHit` — the first hit is uniform (C4).
* `TCSlib.Cryptography.rejectionSample_uniform_of_some`,
  `TCSlib.Cryptography.uprob_rejectionSample_none`,
  `TCSlib.Cryptography.statClose_rejectionSample` — the rejection sampler.
* `TCSlib.Cryptography.statClose_getD_of_uniform_of_some` — a sampler that is uniform
  conditioned on success, made total by a default, is close to uniform within its failure
  probability (C4 in abstract form).
* `TCSlib.Cryptography.one_sub_inv_pow_le_half` — `(1 - 1/m)^m ≤ 1/2`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 181.1, `ε`-closeness; §2.4.2 Theorem 35.1; §2.6.5 Lemma 51.17; §2.12
  Corollary 60.6 and Theorem 63.10; §4.4–§4.6 Protocols 120.6 and 127.5 for the permutation
  sampler of `Asymptotic/Permutations.lean`.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
-/

namespace TCSlib.Cryptography

open Finset

/-! ### Statistical closeness -/

/-- Two samplers `X : σ → γ` and `Y : τ → γ` from uniform seeds are *statistically
`δ`-close* when every test set `T ⊆ γ` has probabilities under the two sampled laws differing
by at most `δ`: the `ε`-closeness of [PS10, Definition 181.1] ("for every (deterministic)
distinguisher `D` (with no time bound), `|Pr[D(x) = 1] − Pr[D(y) = 1]| ≤ ε`"), in its
sup-over-test-sets form, usable for samples in an infinite type such as `List Bool`; on a
finite sample space, with nonempty seed types, it is exactly `EpsClose` of the two laws
(`statClose_iff_epsClose_map`, `Asymptotic/SamplingFinDist.lean`). The device of foundation
decision D10: experiments use ideal distributions, samplers approximate them within
`StatClose` error [PS10, §2.4.2 (the uniform position of Theorem 35.1), §4.3 (statistical
zero-knowledge)].

The seed types are not required to be nonempty. On an empty seed type every probability is
`0` (`uprob`), so the "law" of an empty-seeded sampler is the zero measure and
`StatClose X Y 0` fails as soon as `Y` has seeds; every use has nonempty seeds
(`Ensemble.nonempty`, machine coins `Fin k → Bool`, the `[Nonempty σ]` of `SamplingFinDist`). -/
def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ

section StatClose

variable {σ τ υ γ γ' : Type*} [Fintype σ] [Fintype τ] [Fintype υ]

/-- Unfolding: for a `δ`-close pair the probability of any test set moves by at most `δ`. -/
theorem StatClose.abs_uprob_sub_le {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
    (T : γ → Prop) : |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  h T

/-- One-sided form: the probability of a test set under `X` is at most its probability under
`Y` plus `δ`. -/
theorem StatClose.uprob_le_add {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
    (T : γ → Prop) : uprob (fun s => T (X s)) ≤ uprob (fun t => T (Y t)) + δ := by
  linarith [(abs_le.1 (h T)).2]

/-- A closeness bound is nonnegative. -/
theorem StatClose.nonneg {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) : 0 ≤ δ :=
  (abs_nonneg _).trans (h fun _ => True)

/-- A sampler is `0`-close to itself. -/
theorem StatClose.refl (X : σ → γ) : StatClose X X 0 := fun _ => by
  rw [sub_self, abs_zero]

/-- Closeness is symmetric. -/
theorem StatClose.symm {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) :
    StatClose Y X δ := fun T => by
  rw [abs_sub_comm]
  exact h T

/-- A closeness bound may be weakened. -/
theorem StatClose.mono {X : σ → γ} {Y : τ → γ} {δ δ' : ℝ} (h : StatClose X Y δ) (hδ : δ ≤ δ') :
    StatClose X Y δ' := fun T => (h T).trans hδ

/-- Closeness bounds add along a chain (triangle inequality). -/
theorem StatClose.trans {X : σ → γ} {Y : τ → γ} {Z : υ → γ} {δ δ' : ℝ}
    (h : StatClose X Y δ) (h' : StatClose Y Z δ') : StatClose X Z (δ + δ') := fun T =>
  (abs_sub_le _ _ _).trans (add_le_add (h T) (h' T))

/-- Post-processing both samplers by the same function preserves closeness: the test set `T`
for the images is the test set `T ∘ g` for the sources (statistical-switch lemma C10,
first half). -/
theorem StatClose.map {σ τ γ γ' : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ :=
  fun T => h fun c => T (g c)

/-- Relabelling the seed space of the first sampler by a bijection preserves closeness. -/
theorem StatClose.comp_equiv_left {σ' : Type*} [Fintype σ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (e : σ' ≃ σ) : StatClose (fun s => X (e s)) Y δ := fun T => by
  rw [uprob_comp_equiv e (fun s => T (X s))]
  exact h T

/-- Relabelling the seed space of the second sampler by a bijection preserves closeness. -/
theorem StatClose.comp_equiv_right {τ' : Type*} [Fintype τ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (e : τ' ≃ τ) : StatClose X (fun t => Y (e t)) δ := fun T => by
  rw [uprob_comp_equiv e (fun t => T (Y t))]
  exact h T

/-- A map pushing uniform to uniform is `0`-close to the identity sampler: an exact sampler
(for example squaring onto `QR_N`, lemma C5) has no statistical term. -/
theorem statClose_of_pushesUniform {Ω : Type*} [Fintype Ω] [Fintype γ] {π : Ω → γ}
    (h : HardcoreBit.PushesUniform π) : StatClose π (id : γ → γ) 0 := fun T => by
  rw [h.uprob_eq T]
  simp

/-- Precomposing the first sampler with a map that pushes uniform to uniform (for example
reading a party's random tape as a coin table, `pushesUniform_coinTable`) preserves
closeness: the law of `X ∘ π` is the law of `X`.

**Repair (run-3 audit P2-1):** added for the string-level permutation samplers. -/
theorem StatClose.comp_pushesUniform {Ω : Type*} [Fintype Ω] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) {π : Ω → σ} (hπ : HardcoreBit.PushesUniform π) :
    StatClose (fun ω => X (π ω)) Y δ := fun T => by
  rw [hπ.uprob_eq (fun s => T (X s))]
  exact h T

/-- Averages of pointwise `c`-close functions are `c`-close (`0 ≤ c` covers the empty type). -/
private theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
  rw [← HardcoreBit.uexp_sub]
  unfold uexp
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · rw [h0]
    simpa using hc
  · have hc' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    rw [abs_div, abs_of_pos hc', div_le_iff₀ hc']
    calc |∑ a, (f a - g a)| ≤ ∑ a, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => h a
      _ = c * Fintype.card α := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- The statistical-switch lemma (C10 of the Chapter 2 inventory): replacing a sampler by a
`δ`-close one changes the success probability of any experiment that also uses independent
auxiliary coins `r : ρ` by at most `δ`. [Gar26, Lemma 3.1] in the sup-over-test-sets form.

**Proof sketch.** Average over the coins `r` (`uprob_prod` after swapping the coordinates):
for fixed `r` the event is the test set `P · r`, whose probability moves by at most `δ`
(`h`); the absolute value of an average is at most the average of the absolute values. -/
theorem StatClose.abs_uprob_sub_le_prod {ρ : Type*} [Fintype ρ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (P : γ → ρ → Prop) :
    |uprob (fun z : σ × ρ => P (X z.1) z.2) - uprob (fun z : τ × ρ => P (Y z.1) z.2)| ≤ δ := by
  have e1 := uprob_comp_equiv (Equiv.prodComm ρ σ) (fun z : σ × ρ => P (X z.1) z.2)
  have e2 := uprob_comp_equiv (Equiv.prodComm ρ τ) (fun z : τ × ρ => P (Y z.1) z.2)
  rw [← e1, ← e2, uprob_prod, uprob_prod]
  exact abs_uexp_sub_le h.nonneg fun r => h fun g => P g r

/-- The distinguishing advantage of any distinguisher `D` (with its own coins) between two
`δ`-close samplers is at most `δ`: the computational counterpart of the statistical
distance bound `distAdv_le_statDist` [Gar26, Lemma 3.1], in the form used by every
"replace the ideal sampler by the rejection sampler" step of the campaign (C10). -/
theorem distAdv_le_of_statClose {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    (X : σ → γ) (Y : τ → γ) {δ : ℝ} (h : StatClose X Y δ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ := by
  unfold distAdv acceptProb
  exact h.abs_uprob_sub_le_prod fun g r => D g r = true

/-- Closeness bounds add under independent products: if `X` is `δ`-close to `X'` and `Y` is
`δ'`-close to `Y'` then the pair sampler `(X, Y)` is `(δ + δ')`-close to `(X', Y')`.

**Proof sketch.** Hybrid `(X', Y)`: the first switch `(X, Y) → (X', Y)` is
`StatClose.abs_uprob_sub_le_prod` for `X, X'` with the second coordinate as auxiliary coins;
the second switch `(X', Y) → (X', Y')` is the same lemma for `Y, Y'` after swapping the
coordinates; conclude by the triangle inequality. -/
theorem StatClose.prod {σ σ' τ τ' γ γ' : Type*} [Fintype σ] [Fintype σ'] [Fintype τ] [Fintype τ']
    {X : σ → γ} {X' : τ → γ} {Y : σ' → γ'} {Y' : τ' → γ'} {δ δ' : ℝ}
    (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ') := by
  intro T
  have h1 := h.abs_uprob_sub_le_prod fun g s' => T (g, Y s')
  have h2 := h'.abs_uprob_sub_le_prod fun g t => T (X' t, g)
  rw [← uprob_comp_equiv (Equiv.prodComm τ σ') (fun z : σ' × τ => T (X' z.2, Y z.1)),
    ← uprob_comp_equiv (Equiv.prodComm τ τ') (fun z : τ' × τ => T (X' z.2, Y' z.1))] at h2
  exact (abs_sub_le _ (uprob fun z : τ × σ' => T (X' z.1, Y z.2)) _).trans (add_le_add h1 h2)

end StatClose

/-! ### Equal fibres push uniform to uniform (C5) -/

/-- A map all of whose fibres have the same positive size `c` pushes the uniform distribution
forward to the uniform distribution (lemma C5 of the Chapter 2 inventory): sampling `QR_N` by
squaring a uniform unit, the squaring map being `4`-to-`1` on `Z_N^*` for `N = pq`
[PS10, Corollary 60.6, Theorem 63.10 (3)].

**Proof sketch.** Group the sum of `F ∘ π` by fibres: every fibre contributes `c · F g`, so
`∑ F ∘ π = c ∑ F` and `|Ω| = c |γ|`; the factor `c` cancels in the average. -/
theorem pushesUniform_of_card_fiber {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ]
    (π : Ω → γ) {c : ℕ} (hc : 0 < c)
    (hfib : ∀ g : γ, (univ.filter fun ω => π ω = g).card = c) : HardcoreBit.PushesUniform π := by
  intro F
  have hsum : ∑ ω, F (π ω) = (c : ℝ) * ∑ g, F g := by
    rw [← Finset.sum_fiberwise' univ π F, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [sum_const, nsmul_eq_mul, hfib]
  have hcard : Fintype.card Ω = c * Fintype.card γ := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, smul_eq_mul, mul_comm]
  have hpos : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [uexp, hsum, hcard, Nat.cast_mul]
  rw [mul_div_mul_left _ _ hpos]

/-- Pigeonhole for fibres: if every fibre of `π` has at most `c` elements and the domain has
exactly `c` times as many elements as the codomain, then every fibre has exactly `c`
elements (the counting form of "`4`-to-`1`" in [PS10, Corollary 60.6]).

**Proof sketch.** `|Ω| = ∑_g |π⁻¹ g|`; a single fibre below `c` makes the sum below `c |γ|`. -/
theorem card_fiber_eq_of_le {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ] (π : Ω → γ)
    {c : ℕ} (hle : ∀ g : γ, (univ.filter fun ω => π ω = g).card ≤ c)
    (hcard : Fintype.card Ω = c * Fintype.card γ) (g : γ) :
    (univ.filter fun ω => π ω = g).card = c := by
  by_contra hne
  have hlt : (univ.filter fun ω => π ω = g).card < c := lt_of_le_of_ne (hle g) hne
  have h1 : Fintype.card Ω = ∑ g, (univ.filter fun ω => π ω = g).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
  have h2 : ∑ g, (univ.filter fun ω => π ω = g).card < ∑ _g : γ, c :=
    sum_lt_sum (fun g _ => hle g) ⟨g, mem_univ _, hlt⟩
  rw [sum_const, card_univ, smul_eq_mul, mul_comm] at h2
  omega

/-- The `4`-to-`1` form of C5: fibres of size at most `c` and `|Ω| = c |γ|` give a map pushing
uniform to uniform. -/
theorem pushesUniform_of_card_fiber_le {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ]
    (π : Ω → γ) {c : ℕ} (hc : 0 < c) (hle : ∀ g : γ, (univ.filter fun ω => π ω = g).card ≤ c)
    (hcard : Fintype.card Ω = c * Fintype.card γ) : HardcoreBit.PushesUniform π :=
  pushesUniform_of_card_fiber π hc (card_fiber_eq_of_le π hle hcard)

/-! ### Bit strings as numbers -/

/-- The number with the given binary digits (most significant first). -/
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ :=
  (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- The digit fold with an arbitrary accumulator `a` contributes `a · 2^{|l|}`. -/
private theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
    ring

/-- The number read from `l` is below `2^{|l|}`. -/
private theorem listToNat_lt (l : List Bool) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, foldl_bits_eq, List.length_cons, pow_succ]
    cases c <;> simp <;> omega

/-- Lists of the same length reading as the same number are equal. -/
private theorem listToNat_inj : ∀ (l l' : List Bool), l.length = l'.length →
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 =
      l'.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 → l = l'
  | [], [], _, _ => rfl
  | c :: l, c' :: l', hlen, heq => by
    rw [List.foldl_cons, List.foldl_cons, foldl_bits_eq, foldl_bits_eq (a := 2 * 0 + _)] at heq
    have hlen' : l.length = l'.length := by simpa using hlen
    have h1 := listToNat_lt l
    have h2 := listToNat_lt l'
    rw [hlen'] at heq h1
    obtain ⟨hc, hl⟩ : c = c' ∧ l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 =
        l'.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
      cases c <;> cases c' <;> simp at heq ⊢ <;> omega
    subst hc
    rw [listToNat_inj l l' hlen' hl]

/-- A `k`-bit string reads as a number below `2^k`. -/
theorem bitsToNat_lt {k : ℕ} (b : Fin k → Bool) : bitsToNat b < 2 ^ k := by
  have := listToNat_lt (List.ofFn b)
  rwa [List.length_ofFn] at this

/-- Reading `k`-bit strings as numbers is injective. -/
theorem bitsToNat_injective {k : ℕ} : Function.Injective (bitsToNat (k := k)) := fun b b' h =>
  List.ofFn_injective (listToNat_inj _ _ (by simp) h)

/-- The bijection between `k`-bit strings and `Fin (2^k)` given by `bitsToNat`: a uniform
`k`-bit string is a uniform number below `2^k`. -/
noncomputable def bitsEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  Equiv.ofBijective (fun b => ⟨bitsToNat b, bitsToNat_lt b⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun b b' h => bitsToNat_injective (by simpa using congrArg Fin.val h), by simp⟩)

/-- The value of `bitsEquiv` is `bitsToNat`. -/
@[simp] theorem bitsEquiv_val {k : ℕ} (b : Fin k → Bool) : (bitsEquiv k b).val = bitsToNat b :=
  rfl

/-- A uniform `k`-bit string reads as a number below `m ≤ 2^k` with probability `m / 2^k`.

**Proof sketch.** Transport along `bitsEquiv` to the uniform distribution on `Fin (2^k)`,
where the event `{x < m}` has exactly `m` elements. -/
theorem uprob_bitsToNat_lt {m k : ℕ} (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin k → Bool => bitsToNat b < m) = m / 2 ^ k := by
  let e : {x : Fin (2 ^ k) // x.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.val, lt_of_lt_of_le y.2 hk⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [show (fun b : Fin k → Bool => bitsToNat b < m) = fun b => (bitsEquiv k b).val < m from rfl,
    uprob_comp_equiv (bitsEquiv k) (fun x : Fin (2 ^ k) => x.val < m), uprob, Fintype.card_fin,
    Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast
  rfl

/-- One rejection trial: `k` bits read as a number, accepted iff below `m`. -/
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m) :=
  if h : bitsToNat b < m then some ⟨_, h⟩ else none

/-- A trial yields `i` exactly when the bits read as `i`. -/
theorem uniformFromBits_eq_some_iff {m k : ℕ} (b : Fin k → Bool) (i : Fin m) :
    uniformFromBits m k b = some i ↔ bitsToNat b = i.val := by
  unfold uniformFromBits
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    exact fun h' => h (h' ▸ i.isLt)

/-- A trial fails exactly when the bits read as a number `≥ m`. -/
theorem uniformFromBits_eq_none_iff {m k : ℕ} (b : Fin k → Bool) :
    uniformFromBits m k b = none ↔ m ≤ bitsToNat b := by
  unfold uniformFromBits
  split_ifs with h
  · simp [h]
  · simp only [true_iff]
    exact not_lt.1 h

/-- Each value `i : Fin m` is hit by one trial with probability `1 / 2^k` (for `m ≤ 2^k`). -/
theorem uprob_uniformFromBits_eq_some {m k : ℕ} (hk : m ≤ 2 ^ k) (i : Fin m) :
    uprob (fun b : Fin k → Bool => uniformFromBits m k b = some i) = 1 / 2 ^ k := by
  have key := uprob_comp_equiv (bitsEquiv k)
    (fun x : Fin (2 ^ k) => x = ⟨i.val, lt_of_lt_of_le i.2 hk⟩)
  rw [OneWay.uprob_eq_one_div_card, Fintype.card_fin] at key
  have hiff : ∀ b : Fin k → Bool,
      uniformFromBits m k b = some i ↔ bitsEquiv k b = ⟨i.val, lt_of_lt_of_le i.2 hk⟩ := by
    intro b
    rw [uniformFromBits_eq_some_iff, Fin.ext_iff, bitsEquiv_val]
  rw [OneWay.uprob_congr hiff, key]
  push_cast
  rfl

/-- One trial fails with probability `1 - m / 2^k` (for `m ≤ 2^k`). -/
theorem uprob_uniformFromBits_none {m k : ℕ} (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin k → Bool => uniformFromBits m k b = none) = 1 - m / 2 ^ k := by
  rw [OneWay.uprob_congr fun b => (uniformFromBits_eq_none_iff b).trans not_lt.symm, uprob_not,
    uprob_bitsToNat_lt hk]

/-- Partition of an event by the value of a map: the probability that `f ω` satisfies `S` is
the sum over `b ∈ S` of the probabilities of the fibres `{f = b}`. -/
theorem uprob_comp_eq_sum_fiber {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] (f : Ω → β)
    (S : β → Prop) [DecidablePred S] :
    uprob (fun ω => S (f ω)) = ∑ b ∈ univ.filter S, uprob (fun ω => f ω = b) := by
  simp_rw [uprob_eq_card_filter, ← sum_div]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := f) (s := univ.filter fun ω => S (f ω))
    (t := univ.filter S) (fun ω hω => by simpa using hω)]
  push_cast
  refine sum_congr rfl fun b hb => ?_
  have : (univ.filter fun ω => S (f ω)).filter (fun ω => f ω = b) =
      univ.filter fun ω => f ω = b := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    rw [h]
    exact (mem_filter.1 hb).2
  rw [this]

/-! ### The first hit of independent draws (C4) -/

/-- The first of the `T` draws `xs 0, …, xs (T-1)` satisfying `E`, if any: the general form of
the rejection sampler (lemma C4 of the Chapter 2 inventory; `SamplePrime`
[PS10, Algorithm 50.16] is `firstHit Prime` on `n`-bit numbers). -/
def firstHit {α : Type*} (E : α → Prop) [DecidablePred E] {T : ℕ} (xs : Fin T → α) : Option α :=
  (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none

section FirstHit

variable {α : Type*} (E : α → Prop) [DecidablePred E] {T : ℕ}

/-- No hit exactly when no draw satisfies `E`. -/
theorem firstHit_eq_none_iff (xs : Fin T → α) : firstHit E xs = none ↔ ∀ t, ¬ E (xs t) := by
  unfold firstHit
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- A hit satisfies `E`. -/
theorem firstHit_eq_some_imp {xs : Fin T → α} {a : α} (h : firstHit E xs = some a) : E a := by
  unfold firstHit at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  by_cases hE : E (xs t)
  · rw [if_pos hE, Option.some.injEq] at ht
    exact ht ▸ hE
  · rw [if_neg hE] at ht
    exact absurd ht (Option.noConfusion)

variable [Fintype α]

/-- `T` independent uniform draws all miss `E` with probability `(1 - Pr[E])^T`
(C4, the failure probability of `SamplePrime` [PS10, Lemma 51.17]). -/
theorem uprob_firstHit_none [Nonempty α] (T : ℕ) :
    uprob (fun xs : Fin T → α => firstHit E xs = none) = (1 - uprob E) ^ T := by
  rw [OneWay.uprob_congr fun xs => firstHit_eq_none_iff E xs,
    OneWay.uprob_pi_forall fun a => ¬ E a, Fintype.card_fin, uprob_not]

/-- The first hit is uniform on `E` conditioned on existence: any two elements of `E` are the
first hit with the same probability (C4, [PS10, Lemma 51.17], "`p` is uniform in `Π_n`").

**Proof sketch.** The transposition `s = swap a a'` of `α` preserves `E` (both points lie in
`E`), hence commutes with `firstHit`: `firstHit E (s ∘ xs) = s <$> firstHit E xs`
(`List.map_findSome?`). Applying `s` coordinatewise is a bijection of the draw space
(`uprob_comp_equiv`), and it maps the event `{first hit = a}` onto `{first hit = a'}`. -/
theorem firstHit_uniform_of_some [DecidableEq α] (T : ℕ) {a a' : α} (ha : E a) (ha' : E a') :
    uprob (fun xs : Fin T → α => firstHit E xs = some a) =
      uprob (fun xs : Fin T → α => firstHit E xs = some a') := by
  have hE : ∀ x, E (Equiv.swap a a' x) ↔ E x := by
    intro x
    by_cases hx : x = a
    · subst hx
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => ha, fun _ => ha'⟩
    by_cases hx' : x = a'
    · subst hx'
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => ha', fun _ => ha⟩
    rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  have hmap : ∀ xs : Fin T → α,
      firstHit E (fun t => Equiv.swap a a' (xs t)) = (firstHit E xs).map (Equiv.swap a a') := by
    intro xs
    unfold firstHit
    rw [List.map_findSome?]
    congr 1
    funext t
    by_cases h : E (xs t)
    · simp [h, (hE _).2 h]
    · simp [h, mt (hE _).1 h]
  rw [← uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin T => Equiv.swap a a')
    (fun xs => firstHit E xs = some a')]
  refine OneWay.uprob_congr fun xs => ?_
  show firstHit E xs = some a ↔ firstHit E (fun t => Equiv.swap a a' (xs t)) = some a'
  rw [hmap, Option.map_eq_some_iff]
  constructor
  · intro h
    exact ⟨a, h, Equiv.swap_apply_left a a'⟩
  · rintro ⟨x, hx, hxa⟩
    have hxa' : x = a :=
      (Equiv.swap a a').injective (hxa.trans (Equiv.swap_apply_left a a').symm)
    rw [← hxa']
    exact hx

/-- Falling back to a default element `d ∈ E` when no draw hits makes the first-hit sampler
a total sampler within `(1 - Pr[E])^T` of the uniform distribution on `E` (C4 in the form
consumed by the collections and `SamplePrime`, [PS10, Lemma 51.17]).

**Proof sketch.** Let `f = (1 - Pr[E])^T` be the no-hit probability (`uprob_firstHit_none`)
and `q` the common probability of `{first hit = a}` for `a ∈ E` (`firstHit_uniform_of_some`);
the events `{first hit = a}` (`a ∈ E`) and `{no hit}` partition the draw space, so
`|E| q + f = 1`. For a test set `S`, `Pr[getD d ∈ S] = |S ∩ E| q + [d ∈ S] f` and the ideal
probability is `|S ∩ E| / |E| = |S ∩ E| q + (|S ∩ E| / |E|) f`; both lie in
`[|S ∩ E| q, |S ∩ E| q + f]`, so they differ by at most `f`. Sub-obligations: additivity of
`uprob` over the fibres of `firstHit` (`uprob_eq_card_filter` and
`Finset.card_eq_sum_card_fiberwise`), `Fintype.sum_option`, and `uprob` on the subtype
`{a // E a}` as a count (`uprob_eq_card_filter`). -/
theorem statClose_firstHit [DecidableEq α] [Nonempty α] (T : ℕ) {d : α} (hd : E d) :
    StatClose (fun xs : Fin T → α => (firstHit E xs).getD d) (fun e : {a // E a} => (e : α))
      ((1 - uprob E) ^ T) := by
  classical
  intro S
  have hsome : ∀ a, E a → uprob (fun xs : Fin T → α => firstHit E xs = some a) =
      uprob (fun xs : Fin T → α => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E T ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin T → α => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin T → α)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  -- the law of `firstHit`: `none` with probability `f`, each `a ∈ E` with probability `q`
  have hdec : ∀ S' : Option α → Prop, uprob (fun xs : Fin T → α => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ T else 0) +
        uprob (fun xs : Fin T → α => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E T]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have h1 := hdec fun o => S (o.getD d)
  simp only [Option.getD_none, Option.getD_some] at h1
  have htot := hdec fun _ => True
  simp only [uprob_true, if_true, and_true] at htot
  have hideal : uprob (fun e : {a // E a} => S e.val) =
      ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card := by
    rw [uprob, Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter E S), Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
  rw [h1, hideal]
  -- arithmetic: with `N = |E|`, `M = |E ∩ S|`, `q N = 1 - f`, the difference is `f ([d ∈ S] - M/N)`
  have hN : (0 : ℝ) < (univ.filter E).card := by
    exact_mod_cast card_pos.2 ⟨d, by simpa using hd⟩
  have hMN : ((univ.filter fun a => E a ∧ S a).card : ℝ) ≤ (univ.filter E).card := by
    exact_mod_cast card_le_card fun a ha => by
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha.1
  have hf0 : (0 : ℝ) ≤ (1 - uprob E) ^ T := pow_nonneg (by linarith [uprob_le_one E]) T
  have hq : uprob (fun xs : Fin T → α => firstHit E xs = some d) =
      (1 - (1 - uprob E) ^ T) / (univ.filter E).card := by
    rw [eq_div_iff hN.ne']
    linarith
  rw [hq]
  have hr0 : (0 : ℝ) ≤ ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card :=
    div_nonneg (Nat.cast_nonneg _) hN.le
  have hr1 : ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card ≤ 1 :=
    (div_le_one hN).2 hMN
  have hrw : (1 - (1 - uprob E) ^ T) / (univ.filter E).card *
      ((univ.filter fun a => E a ∧ S a).card : ℝ) =
      (1 - (1 - uprob E) ^ T) *
        (((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card) := by
    ring
  rw [hrw]
  generalize ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card = r at hr0 hr1 ⊢
  generalize (1 - uprob E) ^ T = f at hf0 ⊢
  by_cases hSd : S d
  · rw [if_pos hSd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [if_neg hSd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

end FirstHit

/-! ### Rejection sampling of `Fin m` -/

/-- `T` rejection trials of `k` bits each; the first accepted value. Uniform on `Fin m`
conditioned on `some`; `none` with probability `(1 - m/2^k)^T`. The sampler of the uniform
position `i ∈ [m]` of [PS10, Theorem 35.1] and of the residues of [PS10, §2.6–§2.12]. -/
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m) :=
  (List.finRange T).findSome? fun t => uniformFromBits m k (b t)

/-- The rejection sampler fails exactly when every trial fails. -/
theorem rejectionSample_eq_none_iff (m k T : ℕ) (b : Fin T → Fin k → Bool) :
    rejectionSample m k T b = none ↔ ∀ t, uniformFromBits m k (b t) = none := by
  unfold rejectionSample
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The rejection sampler is the first hit of the event `{x < m}` among the `T` numbers read
from the trials (embedding `Fin m` into `Fin (2^k)`). -/
theorem map_rejectionSample_eq_firstHit {m k T : ℕ} (hk : m ≤ 2 ^ k) (b : Fin T → Fin k → Bool) :
    (rejectionSample m k T b).map (fun i : Fin m => (⟨i.val, lt_of_lt_of_le i.2 hk⟩ : Fin (2 ^ k))) =
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) := by
  unfold rejectionSample firstHit
  rw [List.map_findSome?]
  congr 1
  funext t
  simp only [Function.comp, uniformFromBits, bitsEquiv_val]
  split_ifs <;> rfl

/-- Lemma C4 for the rejection sampler: conditioned on success the output is uniform — any two
values of `Fin m` are output with the same probability ([PS10, Theorem 35.1], the uniform
position; [PS10, Lemma 51.17]).

**Proof sketch.** By `map_rejectionSample_eq_firstHit` the event `{output = i}` is the event
`{firstHit {x < m} = i}` for the numbers read from the trials; reading is a bijection of
each trial's bits onto `Fin (2^k)` (`bitsEquiv`, applied coordinatewise by
`Equiv.piCongrRight`), and `firstHit_uniform_of_some` gives the symmetry between `i` and
`j`. -/
theorem rejectionSample_uniform_of_some (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some i) =
      uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some j) := by
  have _ := hm
  let toBig : Fin m → Fin (2 ^ k) := fun i => ⟨i.val, lt_of_lt_of_le i.2 hk⟩
  have hinj : Function.Injective toBig := fun x y h =>
    Fin.ext (show (toBig x).val = (toBig y).val from congrArg Fin.val h)
  have key : ∀ (b : Fin T → Fin k → Bool) (i : Fin m), rejectionSample m k T b = some i ↔
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) = some (toBig i) := by
    intro b i
    rw [← map_rejectionSample_eq_firstHit hk, Option.map_eq_some_iff]
    constructor
    · intro h
      exact ⟨i, h, rfl⟩
    · rintro ⟨x, hx, hxi⟩
      rw [hinj hxi] at hx
      exact hx
  have e : ∀ i : Fin m, uprob (fun b : Fin T → Fin k → Bool =>
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) = some (toBig i)) =
      uprob (fun xs : Fin T → Fin (2 ^ k) =>
        firstHit (fun x : Fin (2 ^ k) => x.val < m) xs = some (toBig i)) := fun i =>
    uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k)
      (fun xs => firstHit (fun x : Fin (2 ^ k) => x.val < m) xs = some (toBig i))
  rw [OneWay.uprob_congr fun b => key b i, OneWay.uprob_congr fun b => key b j, e i, e j]
  exact firstHit_uniform_of_some _ T i.2 j.2

/-- The rejection sampler fails with probability exactly `(1 - m/2^k)^T` (C4, the no-hit
probability; [PS10, Lemma 51.17] with `Pr[E] = m/2^k`). -/
theorem uprob_rejectionSample_none (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = none) =
      (1 - (m : ℝ) / 2 ^ k) ^ T := by
  have _ := hm
  rw [OneWay.uprob_congr fun b => rejectionSample_eq_none_iff m k T b,
    OneWay.uprob_pi_forall fun c : Fin k → Bool => uniformFromBits m k c = none,
    Fintype.card_fin, uprob_uniformFromBits_none hk]

/-- With `k` chosen so that `2^k ≤ 2m` (the smallest `k` with `m ≤ 2^k`), every trial fails
with probability at most `1/2`, so `T` trials fail with probability at most `2^{-T}`: the
choice of `T = n` in the campaign's honest samplers. -/
theorem uprob_rejectionSample_none_le_half_pow (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k)
    (h2 : 2 ^ k ≤ 2 * m) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = none) ≤ (1 / 2 : ℝ) ^ T := by
  rw [uprob_rejectionSample_none m k T hm hk]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hm' : (m : ℝ) ≤ 2 ^ k := by exact_mod_cast hk
  have h2' : (2 : ℝ) ^ k ≤ 2 * m := by exact_mod_cast h2
  apply pow_le_pow_left₀
  · rw [sub_nonneg, div_le_one h2k]
    exact hm'
  · have : (1 / 2 : ℝ) ≤ m / 2 ^ k := by
      rw [div_le_div_iff₀ (by norm_num) h2k]
      linarith
    linarith

/-- `(1 - 1/m)^m ≤ 1/2` for `m ≥ 1`: `m` trials each failing with probability `1 - 1/m`
all fail with probability at most `1/2` (the dyadic form of "`(1 - 1/m)^m ≈ e^{-1}`").

**Proof sketch.** Bernoulli's inequality `one_add_mul_le_pow` gives `(1 + 1/m)^m ≥ 2`, and
`(1 - 1/m)^m (1 + 1/m)^m = (1 - 1/m²)^m ≤ 1`, so `(1 - 1/m)^m ≤ 1/(1 + 1/m)^m ≤ 1/2`. -/
theorem one_sub_inv_pow_le_half (m : ℕ) (hm : 0 < m) : (1 - 1 / (m : ℝ)) ^ m ≤ 1 / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℝ := 1 / m with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hm']
    exact_mod_cast hm
  have hb : 1 + (m : ℝ) * x ≤ (1 + x) ^ m := one_add_mul_le_pow (by linarith) m
  have hmx : (m : ℝ) * x = 1 := by
    rw [hx]
    field_simp
  rw [hmx] at hb
  have hprod : (1 - x) ^ m * (1 + x) ^ m ≤ 1 := by
    rw [← mul_pow]
    have : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
    rw [this]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : (0 : ℝ) < (1 + x) ^ m := by positivity
  calc (1 - x) ^ m = (1 - x) ^ m * (1 + x) ^ m / (1 + x) ^ m := by field_simp
    _ ≤ 1 / (1 + x) ^ m := by gcongr
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- Fallback-to-default makes a total sampler within `(1 - m/2^k)^T` of uniform: the form of
C4 consumed by Theorem 35.1 (uniform position), the collections (`SampleClose`) and the
Chapter 4 simulators.

**Proof sketch.** Let `f = (1 - m/2^k)^T` (`uprob_rejectionSample_none`) and `q` the common
probability of `{output = i}` (`rejectionSample_uniform_of_some`); the `m + 1` events
`{output = i}`, `{output = none}` partition the coin space, so `m q + f = 1`. For a test set
`S ⊆ Fin m`, `Pr[getD d ∈ S] = |S| q + [d ∈ S] f` and `|S| / m = |S| q + (|S|/m) f`; both lie
in `[|S| q, |S| q + f]`. Alternatively: `map_rejectionSample_eq_firstHit`, the coordinatewise
bijection `bitsEquiv`, and `statClose_firstHit` on `Fin (2^k)` with `E = {x < m}`, transported
along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` (`StatClose.comp_equiv_right`,
`StatClose.map`). -/
theorem statClose_rejectionSample (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (d : Fin m) :
    StatClose (fun b : Fin T → Fin k → Bool => (rejectionSample m k T b).getD d) (id : Fin m → Fin m)
      ((1 - (m : ℝ) / 2 ^ k) ^ T) := by
  have _ := hm
  let toBig : Fin m → Fin (2 ^ k) := fun i => ⟨i.val, lt_of_lt_of_le i.2 hk⟩
  let g : Fin (2 ^ k) → Fin m := fun x => if h : x.val < m then ⟨x.val, h⟩ else d
  let e : Fin m ≃ {x : Fin (2 ^ k) // x.val < m} :=
    { toFun := fun i => ⟨toBig i, i.2⟩
      invFun := fun x => ⟨x.1.val, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hE : uprob (fun x : Fin (2 ^ k) => x.val < m) = m / 2 ^ k := by
    rw [← uprob_bitsToNat_lt hk, ← uprob_comp_equiv (bitsEquiv k) (fun x : Fin (2 ^ k) => x.val < m)]
    rfl
  have h := (((statClose_firstHit (fun x : Fin (2 ^ k) => x.val < m) T (d := toBig d) d.2).comp_equiv_left
    (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k)).map g).comp_equiv_right e
  rw [hE] at h
  have h' : StatClose (fun b : Fin T → Fin k → Bool =>
      g ((firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t))).getD (toBig d)))
      (fun i : Fin m => g (toBig i)) ((1 - (m : ℝ) / 2 ^ k) ^ T) := h
  have hX : (fun b : Fin T → Fin k → Bool =>
      g ((firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t))).getD (toBig d))) =
      fun b => (rejectionSample m k T b).getD d := by
    funext b
    rw [← map_rejectionSample_eq_firstHit hk]
    cases rejectionSample m k T b with
    | none => simp [g, toBig, d.2]
    | some i => simp [g, i.2]
  have hY : (fun i : Fin m => g (toBig i)) = id := by
    funext i
    simp [g, toBig, i.2]
  rw [hX, hY] at h'
  exact h'

/-! ### Total samplers from samplers that are uniform conditioned on success -/

/-- A sampler `S : Ω → Option γ` that is uniform conditioned on success (any two values are
output with the same probability) and fails with probability at most `f`, made total by a
default `d`, is within `f` of the uniform distribution on `γ`: the common argument of
`statClose_firstHit`, `statClose_rejectionSample` and `statClose_permFromCoins` (lemma C4 in
its abstract form; [PS10, Lemma 51.17] for `SamplePrime`, [PS10, Protocol 120.6] for
`π ← S_n`).

**Repair (run-3 audit P2-1):** added so that the permutation sampler has a `StatClose` form
in this file instead of in each consumer.

**Proof sketch.** With `p = Pr[S = none]`, `q = Pr[S = some d]` (the common value of
`Pr[S = some a]`) and `G = |γ|`, the `G + 1` events `{S = some a}`, `{S = none}` partition the
seed space (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`), so `p + q G = 1`; for a test
set `T` with `M = |T|`, `Pr[getD d ∈ T] = [d ∈ T] p + q M` and `M / G = q M + (M / G) p`,
whose difference is `p ([d ∈ T] - M/G)`, of absolute value at most `p ≤ f`. -/
theorem statClose_getD_of_uniform_of_some {Ω γ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype γ]
    [DecidableEq γ] (S : Ω → Option γ)
    (huni : ∀ a a' : γ, uprob (fun ω => S ω = some a) = uprob (fun ω => S ω = some a'))
    {f : ℝ} (hf : uprob (fun ω => S ω = none) ≤ f) (d : γ) :
    StatClose (fun ω => (S ω).getD d) (id : γ → γ) f := by
  classical
  intro T
  -- the law of `S`: `none` with probability `p`, each `a : γ` with the common probability `q`
  have hdec : ∀ S' : Option γ → Prop, uprob (fun ω => S' (S ω)) =
      (if S' none then uprob (fun ω => S ω = none) else 0) +
        uprob (fun ω => S ω = some d) * (univ.filter fun a => S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber S S', sum_filter, Fintype.sum_option]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · simp [hSa, huni a d]
    · simp [hSa]
  have h1 := hdec fun o => T (o.getD d)
  simp only [Option.getD_none, Option.getD_some] at h1
  have htot := hdec fun _ => True
  simp only [uprob_true, if_true, filter_true, card_univ] at htot
  have hideal : uprob (fun a : γ => T (id a)) = ((univ.filter T).card : ℝ) / Fintype.card γ := by
    rw [uprob_eq_card_filter]
    rfl
  rw [h1, hideal]
  -- arithmetic: with `q G = 1 - p`, the difference is `p ([d ∈ T] - M/G)`
  have hG : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨d⟩
  have hMG : ((univ.filter T).card : ℝ) ≤ Fintype.card γ := by
    exact_mod_cast card_le_univ _
  have hp0 : 0 ≤ uprob (fun ω => S ω = none) := uprob_nonneg _
  have hq : uprob (fun ω => S ω = some d) =
      (1 - uprob (fun ω => S ω = none)) / Fintype.card γ := by
    rw [eq_div_iff hG.ne']
    linarith
  rw [hq]
  have hrw : (1 - uprob (fun ω => S ω = none)) / Fintype.card γ * ((univ.filter T).card : ℝ) =
      (1 - uprob (fun ω => S ω = none)) * (((univ.filter T).card : ℝ) / Fintype.card γ) := by
    ring
  rw [hrw]
  have hr0 : (0 : ℝ) ≤ ((univ.filter T).card : ℝ) / Fintype.card γ :=
    div_nonneg (Nat.cast_nonneg _) hG.le
  have hr1 : ((univ.filter T).card : ℝ) / Fintype.card γ ≤ 1 := (div_le_one hG).2 hMG
  generalize ((univ.filter T).card : ℝ) / Fintype.card γ = r at hr0 hr1 ⊢
  generalize uprob (fun ω => S ω = none) = p at hp0 hf ⊢
  by_cases hTd : T d
  · rw [if_pos hTd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [if_neg hTd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/Ensembles.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
-- `NonUniform` is not used here. It replaces, for downstream files, the former import of the
-- facade `TCSlib.Complexity.Randomized`: `ZeroKnowledge/ThreeColoring/SimulatorMachine.lean`
-- uses `NUPPT.Uniform.advice_eq` and reaches `NonUniform` only through this file (gate 03a,
-- finding 12). Drop it once that file imports `NonUniform` itself.
import TCSlib.Complexity.Randomized.NonUniform
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensembles and computational indistinguishability

The asymptotic notion of [PS10, §3.1]: *ensembles* of probability distributions over
`{0,1}^{ℓ(n)}` and *computational indistinguishability* `{X_n} ≈ {Y_n}` against non-uniform
PPT distinguishers, with the three properties the rest of chapters 3 and 4 use over and over:
closure under efficient operations (Lemma 71.5), the hybrid lemma (Lemma 71.6) and the
prediction lemma (Lemma 73.8).

Foundation decision D6: an ensemble is a family of samplers `X n : σ n → (Fin (ℓ n) → Bool)`
from arbitrary finite nonempty seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`); every
length is a syntactic polynomial `Complexity.PolyExpr` (D9). "Efficiently samplable" is the
distribution-level predicate `Ensemble.Samplable`: a polynomial-time sampler from `s n`
uniform bits whose output law is exactly `X n` (`StatClose … 0`). The headline form of
Definition 69.4 gives the distinguisher the input `1^n` (`Ensemble.Indist`, D5); the literal
form `Ensemble.IndistLit` (the distinguisher receives the sample `t` only, activation at
parameter `|t| = ℓ n`) is stated next to it with the bridges `Indist.toLit` and
`IndistLit.toIndist` (injective, i.e. non-constant, `ℓ`; for constant `ℓ` the two forms
coincide as well, by point tests, which is not formalized), never unified silently.

Every asymptotic statement is proved by instantiating a concrete reduction of
`TCSlib.Cryptography.Pseudorandom.Indistinguishability` [Gar26, §3.2] at each `n`, exhibiting
the reduction as a `Complexity.NUPPT` by the closure catalogue of
`TCSlib.Complexity.Randomized.Closure`, and finishing with negligible-function arithmetic
(`not_negligible_iff`, the "infinitely many `n` with `1/p(n)`" idiom of the text,
`not_negligible_iff_exists_polyExpr`).

**Deviation:** `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n`
(literal form `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the
constant case by point tests, not formalized).

The machine constructions and the probability bookkeeping behind the proofs (the negated,
padded-image and multicopy reductions as `NUPPT`s, coin-splitting bijections, the exactness
transfer `StatClose … 0` through `copies`) live in the sibling file
`TCSlib.Cryptography.Asymptotic.EnsemblesLemmas` (inner namespace `EnsembleLemmas`), which
exists only to keep this file within the repository's size limit.

**Repair (run-3 audit P2-2):** `Ensemble` carries the field `nonempty` (an empty seed type is
not a distribution), which restores the frozen shapes of `prediction_lemma` and
`Ensemble.NextBitUnpredictable.pseudorandom` (`NextBit.lean`); the nonemptiness instances
of `predict_eq` are discharged automatically for ensemble seeds and machine coins.

## Main definitions

* `TCSlib.Cryptography.Ensemble` — an ensemble over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3];
  `Ensemble.uniform` — the uniform ensemble `{U_{ℓ(n)}}`.
* `TCSlib.Cryptography.Ensemble.Samplable` — efficiently samplable (distribution level, D6).
* `TCSlib.Cryptography.Ensemble.Indist`, `TCSlib.Cryptography.Ensemble.IndistLit` —
  computational indistinguishability [PS10, Definition 69.4], headline and literal forms;
  `TCSlib.Cryptography.Distinguishes`, `TCSlib.Cryptography.Ensemble.DistinguishesWith` —
  "`D` distinguishes with probability `ε` / `μ(·)`".
* `TCSlib.Cryptography.Ensemble.Pseudorandom` — indistinguishable from uniform
  [PS10, Definition 74.1].
* `TCSlib.Cryptography.Ensemble.push` — the image ensemble `{M(X_n)}` under an `NUPPT`;
  `TCSlib.Cryptography.Ensemble.copies` — `t(n)` independent copies.
* `TCSlib.Cryptography.mixEnsemble` — the sampler of `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8].

## Main results

* `TCSlib.Cryptography.Ensemble.Indist.refl`, `Indist.symm`, `Indist.trans` — `≈` is an
  equivalence relation (transitivity is the two-step hybrid lemma, [PS10, §3.1.1]).
* `TCSlib.Cryptography.Ensemble.Indist.push` — closure under efficient operations
  [PS10, Lemma 71.5].
* `TCSlib.Cryptography.hybrid_lemma` — the hybrid lemma [PS10, Lemma 71.6], concrete.
* `TCSlib.Cryptography.Ensemble.Indist.copies` — polynomially many copies (the multicopy
  corollary of the hybrid lemma, [Gar26, Lemma 3.3]).
* `TCSlib.Cryptography.predict_eq` — predicting is distinguishing, the identity behind
  [PS10, p. 73 ("show this!") and Lemma 73.8].
* `TCSlib.Cryptography.prediction_lemma` — the prediction lemma [PS10, Lemma 73.8].
* `TCSlib.Cryptography.not_negligible_iff_exists_polyExpr` — "for infinitely many `n`,
  advantage `≥ 1/p(n)`" is non-negligibility [PS10, §3.1, the ubiquitous contradiction idiom].
* `TCSlib.Cryptography.pairwise_sampling_ineq` — the pairwise-independent sampling
  inequality [PS10, Appendix A, p. 189].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.1: Definitions 69.3, 69.4; §3.1.1: Lemmas 71.5, 71.6, 73.8; §3.2.1: Definition 74.1;
  Appendix A, p. 189.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Definition 3.4, Lemmas 3.2 and 3.3), Theorem 2.4.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Ensembles -/

/-- An **ensemble** of probability distributions over `{0,1}^{ℓ(n)}` [PS10, Definition 69.3]:
at each `n` a sampler `X n` from a finite seed type `σ n` (uniformly distributed seeds) into
the `ℓ(n)`-bit strings, the distribution `X_n` being the pushforward of the uniform seed. The
length `ℓ` is a syntactic polynomial (D9).

**Deviation:** each `X_n` is the pushforward of the uniform distribution on a finite nonempty
seed set, so its probabilities are rational (not necessarily dyadic: seeds `Fin 3` give mass
`1/3`; the efficiently samplable ensembles, `Samplable`, are the dyadic ones, D6), and it lives
on strings of the fixed length `ℓ(n)` that Definition 69.4 requires (Definition 69.3 allows
arbitrary distributions over `{0,1}^*`). Every ensemble of chapters 3 and 4 is of this form;
the non-dyadic ideal distributions (primes, `Z_q`, permutations) appear only inside
experiments, approximated by the rejection samplers of `Asymptotic/Sampling.lean` (D6, D10).

**Repair (run-3 audit P2-2):** the field `nonempty` was added to the frozen structure of
DESIGN.md §2.11. An empty seed type is not a distribution (every event has probability `0`),
and without the field `NextBitUnpredictable` was vacuous for an empty-seed ensemble that is
not pseudorandom, so `prediction_lemma` and `NextBitUnpredictable.pseudorandom` needed ad hoc
nonemptiness hypotheses. Machine coin types `Fin k → Bool` and every seed type of the campaign
are nonempty, so constructions fill the field by instance resolution. -/
structure Ensemble (ℓ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- Seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- Seed types are nonempty: the sampler defines a probability distribution. -/
  [nonempty : ∀ n, Nonempty (σ n)]
  /-- The sampler at parameter `n`. -/
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)

attribute [instance] Ensemble.fintype Ensemble.nonempty

namespace Ensemble

variable {ℓ : PolyExpr}

/-- The uniform ensemble `{U_{ℓ(n)}}` [PS10, §3.2.1]: seeds are the strings themselves. -/
def uniform (ℓ : PolyExpr) : Ensemble ℓ where
  σ n := Fin (ℓ.eval n) → Bool
  X _ := id

/-- **Efficiently samplable** ensemble (distribution level, D6): there is a syntactic
polynomial `s` and a polynomial-time sampler `S` such that at every `n` the law of
`S(⟨1^n, r⟩)` for `s(n)` uniform bits `r` (padded or truncated to `ℓ(n)` bits) is exactly the
law of `X n` (`StatClose … 0`). This is the "efficiently sample" of [PS10, p. 72, Example];
the multicopy lemma that assumes it is [Gar26, Lemma 3.3] (`Indist.copies`). -/
def Samplable (X : Ensemble ℓ) : Prop :=
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool =>
      padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0

/-- **Computational indistinguishability** `{X_n} ≈ {Y_n}` [PS10, Definition 69.4], headline
form: for every non-uniform PPT `D`, the advantage
`|Pr[t ← X_n : D(1^n, t) = 1] − Pr[t ← Y_n : D(1^n, t) = 1]|` is a negligible function of
`n`. (The text's "there exists a negligible `ε` with advantage `< ε(n)` for all `n`" is
equivalent, `indist_iff_exists_negligible`.)

**Deviation:** `D` receives `1^n` in addition to the sample (D5); the literal form is
`IndistLit`, and the two are related by `Indist.toLit` and `IndistLit.toIndist`. -/
def Indist (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))

/-- **Computational indistinguishability, literal form** [PS10, Definition 69.4]: the
distinguisher receives the sample `t` only, i.e. is activated at parameter `|t| = ℓ(n)`
(`D_{|t|}(t)` in the machine-sequence reading of [PS10, Definition 26.8]). -/
def IndistLit (X Y : Ensemble ℓ) : Prop :=
  ∀ D : NUPPT, Negligible fun n =>
    distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))

/-- A **pseudorandom ensemble** [PS10, Definition 74.1]: indistinguishable from the uniform
ensemble `{U_{ℓ(n)}}`. -/
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)

/-- The image ensemble `{M(X_n)}` of [PS10, Lemma 71.5]: at parameter `n`, draw a seed of `X`
and coins for `M`, run `M(1^n, X_n)` and pad or truncate the output to `ℓ'(n)` bits. The
output length `ℓ'` is an explicit syntactic polynomial so that the padding is itself
polynomial-time (`polyTimeComputable_unaryPoly`). The padding (`padFin`: `false`-padding or
truncation) is lossless when `M` outputs exactly `ℓ'(n)` bits, the only case Definition 69.4
can type, and lossy otherwise (`[1]` and `[1, 0]` both pad to `[1, 0, …]`): variable-length
outputs (ciphertexts, views, transcripts) are not ensembles of this kind. -/
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ' where
  σ n := X.σ n × M.Coins n
  X n z := padFin (ℓ'.eval n) (M.runAt n (List.ofFn (X.X n z.1)) z.2)

/-- The blockwise bijection `{0,1}^{q·ℓ} ≃ ({0,1}^ℓ)^q` (private copy of the frozen
`FunFamily.blocks` of `Asymptotic/OneWay.lean`, which this file does not import). -/
private def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- `t(n)` independent copies of `X_n`, concatenated into one `t(n)·ℓ(n)`-bit string: the
ensemble `{X_n^{(1)} ‖ ⋯ ‖ X_n^{(t(n))}}` of the multicopy corollary of the hybrid lemma
[PS10, Lemma 71.6; Gar26, Lemma 3.3]. -/
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ) where
  σ n := Fin (t.eval n) → X.σ n
  X n s := (blocks (t.eval n) (ℓ.eval n)).symm (TCSlib.Cryptography.copies (t.eval n) (X.X n) s)

/-- Unfolding of `copies`: bit `i` of the concatenation is bit `i mod ℓ` of copy `i / ℓ`
(through `finProdFinEquiv`). -/
theorem copies_X (t : PolyExpr) (X : Ensemble ℓ) (n : ℕ) (s : Fin (t.eval n) → X.σ n)
    (i : Fin (t.eval n * ℓ.eval n)) :
    (X.copies t).X n s i = X.X n (s (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 :=
  rfl

/-- The uniform ensemble is efficiently samplable: `s := ℓ` and the sampler returns its coins
(`pairSndD` of `⟨1^n, r⟩`). Non-vacuity of `Samplable` (the case `U_n` of D6). -/
theorem uniform_samplable (ℓ : PolyExpr) : (uniform ℓ).Samplable := by
  refine ⟨ℓ, pairSndD, polyTimeComputable_pairSndD, fun n => ?_⟩
  have h : (fun r : Fin (ℓ.eval n) → Bool =>
      padFin (ℓ.eval n) (pairSndD (NUPPT.advInput n (List.ofFn r)))) = (uniform ℓ).X n := by
    funext r
    simp [NUPPT.advInput, padFin_ofFn, uniform]
  rw [h]
  exact StatClose.refl _

end Ensemble

/-! ### The "distinguishes with probability" notations of Definition 69.4 -/

/-- `D` **distinguishes** the distributions `X` and `Y` **with probability `ε`**
[PS10, p. 70, after Definition 69.4]: `|Pr[t ← X : D(t) = 1] − Pr[t ← Y : D(t) = 1]| > ε`. -/
def Distinguishes {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) (ε : ℝ) : Prop :=
  ε < distAdv X Y D

/-- `D` **distinguishes the ensembles** `{X_n}` and `{Y_n}` **with probability `μ(·)`**
[PS10, p. 70]: for all `n`, `D` distinguishes `X_n` and `Y_n` with probability `μ(n)`. -/
def Ensemble.DistinguishesWith {ℓ : PolyExpr} (X Y : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ) :
    Prop :=
  ∀ n, Distinguishes (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) (μ n)

/-- The text's form of Definition 69.4 — "there exists a negligible `ε` with advantage
`< ε(n)` for all `n`" — is equivalent to the frozen form "the advantage is negligible"
[PS10, Definition 69.4]: the advantage lies in `[0, 1]`, so one direction is `Negligible.mono`
and the other takes `ε(n) := advantage(n) + 2^{-n}`. -/
theorem Ensemble.indist_iff_exists_negligible {ℓ : PolyExpr} (X Y : Ensemble ℓ) :
    X.Indist Y ↔ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) < ε n := by
  constructor
  · intro h D
    refine ⟨fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) + (2 : ℝ)⁻¹ ^ n,
      (h D).add negligible_two_pow_neg, fun n => ?_⟩
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
    linarith
  · intro h D
    obtain ⟨ε, hε, hlt⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) := abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hlt n).le.trans (le_abs_self _)

/-- **The contradiction idiom of the text** [PS10, §3.1, Lemma 71.5's proof and passim]:
"assume for contradiction that there is a polynomial `p` such that for infinitely many `n` the
advantage is at least `1/p(n)`" is exactly non-negligibility (`not_negligible_iff`), with the
polynomial a syntactic `PolyExpr` with positive values.

**Proof sketch.** (⇒) `not_negligible_iff` gives an exponent `c`; take `p := (n+1)^c`
(`PolyExpr.normal 1 c`), which is positive and dominates `n^c`. (⇐) `p(n) ≤ C(n+1)^c`
(`PolyExpr.eval_le`) and `(n+1)^c ≤ 2^c n^c`, so `p(n) ≤ n^{c+1}` once `n ≥ C·2^c`; the
exponent `c + 1` witnesses `not_negligible_iff`. -/
theorem not_negligible_iff_exists_polyExpr {μ : ℕ → ℝ} :
    ¬ Negligible μ ↔ ∃ p : PolyExpr, (∀ n, 0 < p.eval n) ∧
      ∀ n₀, ∃ n ≥ n₀, 1 / (p.eval n : ℝ) ≤ |μ n| := by
  rw [not_negligible_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨.normal 1 c, fun n => by simp [PolyExpr.eval_normal], fun n₀ => ?_⟩
    obtain ⟨n, hn, h⟩ := hc (max n₀ 1)
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ h⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
    rw [PolyExpr.eval_normal]
    push_cast
    rw [one_mul]
    exact one_div_le_one_div_of_le (pow_pos (by linarith) c)
      (pow_le_pow_left₀ (by linarith) (by linarith) c)
  · rintro ⟨p, hp, h⟩
    obtain ⟨C, c, hC⟩ := p.eval_le
    refine ⟨c + 1, fun n₀ => ?_⟩
    obtain ⟨n, hn, hμ⟩ := h (max n₀ (C * 2 ^ c + 1))
    refine ⟨n, le_trans (le_max_left _ _) hn, le_trans ?_ hμ⟩
    have hn' : C * 2 ^ c + 1 ≤ n := le_trans (le_max_right _ _) hn
    have key : p.eval n ≤ n ^ (c + 1) := by
      calc p.eval n ≤ C * (n + 1) ^ c := hC n
        _ ≤ C * (2 * n) ^ c := by gcongr; omega
        _ = C * 2 ^ c * n ^ c := by rw [mul_pow, mul_assoc]
        _ ≤ n * n ^ c := by gcongr; omega
        _ = n ^ (c + 1) := by ring
    have hpos : (0 : ℝ) < p.eval n := by exact_mod_cast hp n
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast key)

/-! ### Properties of computational indistinguishability [PS10, §3.1.1] -/

/-- **Reflexivity of `≈`** (non-vacuity of `Indist`): every ensemble is indistinguishable
from itself, the advantage being identically zero. -/
theorem Ensemble.Indist.refl {ℓ : PolyExpr} (X : Ensemble ℓ) : X.Indist X := by
  intro D
  have h : (fun n => distAdv (X.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun _ => (0 : ℝ) := by
    funext n
    simp [distAdv]
  rw [h]
  exact negligible_zero

/-- **Symmetry of `≈`**: the advantage is symmetric in the two distributions. -/
theorem Ensemble.Indist.symm {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) : Y.Indist X := by
  intro D
  have e : (fun n => distAdv (Y.X n) (X.X n) (D.distinguisher n (ℓ.eval n))) =
      fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) :=
    funext fun n => abs_sub_comm _ _
  rw [e]
  exact h D

/-- **Bridge from the `1^n` form to the literal form** of Definition 69.4: if `{X_n} ≈ {Y_n}`
against distinguishers receiving `1^n`, then also against distinguishers receiving the sample
only [PS10, Definition 69.4; D5].

**Proof sketch.** A literal distinguisher `D` activated at parameter `ℓ(n)` is, as a function
of `n`, the activation of the machine `B := NUPPT.exists_reparam D ℓ` (advice
`D.advice (ℓ n)`, coins `D.coins.subst ℓ`), whose `runAtL n t r` equals `D.runAtL (ℓ n) t r`;
`B` ignores `1^n`. The coin types `B.Coins n` and `D.Coins (ℓ n)` correspond along
`PolyExpr.eval_subst` (`finCongr`), so the acceptance probabilities of
`B.distinguisher n (ℓ n)` and `D.distinguisher (ℓ n) (ℓ n)` agree
(`EnsembleLemmas.acceptProb_reparam`); hence the two advantage functions are equal and `h B`
gives negligibility. -/
theorem Ensemble.Indist.toLit {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) :
    X.IndistLit Y := by
  intro D
  obtain ⟨B, hBc, -, hB⟩ := D.exists_reparam ℓ
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_reparam hBc hB, EnsembleLemmas.acceptProb_reparam hBc hB]

/-- **Bridge from the literal form to the `1^n` form** for injective `ℓ` (every ensemble of
the text): if `{X_n} ≈ {Y_n}` against literal distinguishers, then also against distinguishers
receiving `1^n` [PS10, Definition 69.4; D5].

The hypothesis `hℓ` excludes only constant `ℓ`: a `PolyExpr` has natural-number coefficients,
so `ℓ.eval` is constant or strictly increasing. For constant `ℓ ≡ L` the two forms coincide as
well (not formalized, no consumer): the `2^L` point tests `t ↦ [t = t₀]` are advice-free
literal distinguishers, so `IndistLit` makes `Σ_{t₀} |Pr[X_n = t₀] − Pr[Y_n = t₀]|`, hence the
statistical distance of `X_n` and `Y_n`, negligible, and that bounds every distinguisher
(`distAdv_le_of_statClose`). So D5's "`D` receives `1^n`" costs nothing for ensembles.

**Proof sketch.** `ℓ.eval` is monotone (`PolyExpr.eval_mono`) and injective, hence strictly
increasing, so `n ≤ ℓ n` for all `n`. Let `φ m := n` if `m = ℓ n` (`Classical.choose` of the
preimage, unique by injectivity) and `φ m := 0` off the image; then `φ m ≤ m`, so
`NUPPT.exists_reparam_advice D φ .var` gives a machine `B` with coins `D.coins.subst var =
D.coins` that at parameter `m = ℓ n` runs `D` at parameter `φ m = n` on its first
`D.coinLen n` coins, with the advice `⟨1^n, D.advice n⟩` hard-wired at length `ℓ n`. Hence
`B.distinguisher (ℓ n) (ℓ n)` and `D.distinguisher n (ℓ n)` have equal advantages after
discarding the unread coins (`EnsembleLemmas.acceptProb_reparam_advice`: the coin split
`EnsembleLemmas.coinsEquiv` built on `Fin.appendEquiv`, then
`EnsembleLemmas.acceptProb_coins_fst`), and `h B` gives negligibility. -/
theorem Ensemble.IndistLit.toIndist {ℓ : PolyExpr} {X Y : Ensemble ℓ}
    (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y := by
  classical
  intro D
  have hsm : StrictMono ℓ.eval := ℓ.eval_mono.strictMono_of_injective hℓ
  have hle : ∀ n, n ≤ ℓ.eval n := fun n => hsm.id_le n
  let φ : ℕ → ℕ := fun m => if hm : ∃ n, ℓ.eval n = m then hm.choose else 0
  have hφ : ∀ m, φ m ≤ PolyExpr.var.eval m := by
    intro m
    simp only [φ, PolyExpr.eval_var]
    split_ifs with hm
    · exact (hle _).trans_eq hm.choose_spec
    · exact Nat.zero_le _
  have hφn : ∀ n, φ (ℓ.eval n) = n := by
    intro n
    have hm : ∃ n', ℓ.eval n' = ℓ.eval n := ⟨n, rfl⟩
    simp only [φ, dif_pos hm]
    exact hℓ hm.choose_spec
  obtain ⟨A, hAc, hA⟩ := D.exists_reparam_advice φ .var hφ
  refine (h A).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  have hle' : D.coinLen (φ (ℓ.eval n)) ≤ D.coinLen (PolyExpr.var.eval (ℓ.eval n)) := by
    rw [hφn, PolyExpr.eval_var]
    exact D.coins.eval_mono (hle n)
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle',
    EnsembleLemmas.acceptProb_reparam_advice hAc hA (ℓ.eval n) hle', hφn]

/-- **Closure under efficient operations** [PS10, Lemma 71.5]: if `{X_n} ≈ {Y_n}` then for every
non-uniform PPT `M` (and every explicit output length `ℓ'`), `{M(X_n)} ≈ {M(Y_n)}`.

**Proof sketch.** Fix a distinguisher `D` of the image ensembles. The machine
`D' := EnsembleLemmas.exists_pushRed M D ℓ'` (coins `M.coins + D.coins`, advice
`combineAdvice (M.advice n) (D.advice n)`, built as `NUPPT.ofPolyTime` of a raw function of
the layout `⟨⟨⟨1^n, t⟩, α⟩, r⟩` as in `NUPPT.exists_seq`) runs `M` on `t` with the first
`M.coins n` coins, pads the result to `ℓ'(n)` bits *inside the layout*, where `1^n` is
available (`NUPPT.exists_comp` sees only `y`, gate 03a finding 3; the padding is
`EnsembleLemmas.polyTimeComputable_padL`, a typed cut `pairTakePoly ℓ'` of the output
followed by `0^{ℓ'(n)}`), and hands it to `D` with the remaining coins. Its distinguisher at
`n` is the concrete `sunglassRed P (D.distinguisher n (ℓ' n))` with
`P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` up to the coin split
`EnsembleLemmas.coinsEquiv` (`Fin.appendEquiv`), so by `acceptProb_bind`
(`EnsembleLemmas.acceptProb_pushRed`) its acceptance probabilities on `X_n`, `Y_n` are those
of `D` on `pushSampler P (X.X n) = (X.push M ℓ').X n` and `(Y.push M ℓ').X n`. Hence the
advantage function of `D` on the images is that of `D'` on `X, Y`, negligible by `h D'`. -/
theorem Ensemble.Indist.push {ℓ ℓ' : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) :
    (X.push M ℓ').Indist (Y.push M ℓ') := by
  intro D
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_pushRed M D ℓ'
  refine (h B).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold distAdv
  rw [EnsembleLemmas.acceptProb_pushRed hBc hB (X := X.X n),
    EnsembleLemmas.acceptProb_pushRed hBc hB (X := Y.X n)]
  rfl

/-- **The hybrid lemma** [PS10, Lemma 71.6], at one parameter: if `D` distinguishes `X^0` and
`X^m` with advantage `ε` then some consecutive pair `X^i, X^{i+1}` (`i < m`) is distinguished
by `D` with advantage at least `ε / m`. (The text indexes `X^1, …, X^m` and loses the factor
`m` where `m − 1` steps would do; harmless.) This is the concrete `exists_hybrid_gap` applied to
the acceptance probabilities `g_i = Pr[t ← X^i : D(t) = 1]`. All hybrids share one seed type
`σ` (`X : ℕ → σ → γ`); hybrids with seeds of different shapes are first embedded into a
common product seed. -/
theorem hybrid_lemma {σ γ ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (X : ℕ → σ → γ) (D : γ → ρ → Bool) :
    ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i + 1)) D := by
  obtain ⟨i, hi, h⟩ := exists_hybrid_gap (fun i => acceptProb (X i) D) hm
  exact ⟨i, hi, h⟩

/-- **Transitivity of `≈`** [PS10, §3.1.1, "Transitivity – The Hybrid Lemma"]: the two-step
case of the hybrid lemma. The advantage between `X` and `Z` is at most the sum of the
advantages between `X, Y` and `Y, Z` (triangle inequality), and sums of negligible functions
are negligible. -/
theorem Ensemble.Indist.trans {ℓ : PolyExpr} {X Y Z : Ensemble ℓ} (h₁ : X.Indist Y)
    (h₂ : Y.Indist Z) : X.Indist Z := by
  intro D
  refine ((h₁ D).add (h₂ D)).mono ⟨0, fun n _ => ?_⟩
  have h0 : 0 ≤ distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) +
      distAdv (Y.X n) (Z.X n) (D.distinguisher n (ℓ.eval n)) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg h0]
  unfold distAdv
  rw [abs_abs]
  exact abs_sub_le _ _ _

/-- **Polynomially many copies** (the multicopy corollary of the hybrid lemma,
[PS10, Lemma 71.6; Gar26, Lemma 3.3]): if `{X_n} ≈ {Y_n}` and both ensembles are efficiently
samplable, then `t(n)` independent copies remain indistinguishable for every syntactic
polynomial `t`.

The samplability hypotheses are those of [Gar26, Lemma 3.3]'s uniform reduction, which
samples the other copies (D6). Against non-uniform distinguishers they can be dropped: hard-wire
the hybrid index and the other `t(n) − 1` copies that keep the gap as advice
(`NUPPT.exists_withAdvice`). That form is not proved, since no consumer needs copies of a
non-samplable ensemble (gate 03a, finding 2).

**Proof sketch.** Fix a distinguisher `D` of the `t(n)`-fold products. At each `n` with
`t(n) > 0`, `exists_multicopyRed_ge` (through the block bijection `blocks`) gives a hybrid
index `k_n < t(n)` such that the concrete reduction `multicopyRed (X.X n) (Y.X n) (t n) k_n D'`
(sample `k_n` copies of `Y`, `t(n) − k_n − 1` copies of `X`, plant the challenge at position
`k_n`, call `D` once) has advantage at least `ε(n) / t(n)`; the index is chosen per `n`
(`choose`; for `t(n) = 0` any index, both products being the one-point distribution,
`EnsembleLemmas.distAdv_eq_zero_of_subsingleton`) and `1^{k_n}` is hard-wired into the
advice (`NUPPT.exists_withAdvice`). The reduction is the `NUPPT` of
`EnsembleLemmas.exists_copiesRed`: the `Samplable` evaluators of `X` and `Y` are run on the
`t(n)` chunks of fresh coins by the state loop `EnsembleLemmas.CopiesLoop`
(`polyTimeComputable_iterateEmit`, coins cut by `pairTakePoly`/`pairDropPoly`, the challenge
planted at the hard-wired position), and `D` is called through `NUPPT.exists_seq`. The laws
of the sampled copies equal the ideal `X.X n`, `Y.X n` (`StatClose … 0`, lifted to the product
by `EnsembleLemmas.statClose_copies` and `StatClose.prod`), so the acceptance probabilities
coincide exactly (`EnsembleLemmas.acceptProb_multicopyRed_congr`). Hence
`distAdv ((X.copies t).X n) ((Y.copies t).X n) D ≤ t(n) · distAdv (X.X n) (Y.X n) B_n` with
the reduction `B` independent of `n` up to the advice, and `t(n) ≤ C (n+1)^c`
(`PolyExpr.eval_le`) makes the right-hand side negligible
(`EnsembleLemmas.negligible_polyExpr_mul`, from `Negligible.mul_pow` and
`Negligible.const_mul`); `Negligible.mono` concludes. -/
theorem Ensemble.Indist.copies {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) :
    (X.copies t).Indist (Y.copies t) := by
  classical
  obtain ⟨sX, SX, hSX, hXc⟩ := hX
  obtain ⟨sY, SY, hSY, hYc⟩ := hY
  intro D
  -- the distinguisher of `t(n)`-tuples behind `D`
  obtain ⟨D', hD'⟩ : ∃ D' : ∀ n, (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) → D.Coins n → Bool,
      ∀ n v r, D' n v r = D.distinguisher n ((PolyExpr.mul t ℓ).eval n)
        ((EnsembleLemmas.blocks (t.eval n) (ℓ.eval n)).symm v) r := ⟨_, fun _ _ _ => rfl⟩
  have hadv : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) := by
    intro n
    have e : ∀ Z : Ensemble ℓ, acceptProb ((Z.copies t).X n)
        (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) =
        acceptProb (TCSlib.Cryptography.copies (t.eval n) (Z.X n)) (D' n) := by
      intro Z
      refine OneWay.uprob_congr fun z => ?_
      rw [hD']
      exact Iff.rfl
    unfold distAdv
    rw [e, e]
  -- the hybrid index at each `n` (any index when `t(n) = 0`)
  have hex : ∀ n, ∃ k, k ≤ t.eval n ∧ (0 < t.eval n → k < t.eval n ∧
      distAdv (TCSlib.Cryptography.copies (t.eval n) (X.X n))
        (TCSlib.Cryptography.copies (t.eval n) (Y.X n)) (D' n) / t.eval n ≤
        distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) k (D' n))) := by
    intro n
    by_cases ht : 0 < t.eval n
    · obtain ⟨k, hk, hge⟩ := exists_multicopyRed_ge (X.X n) (Y.X n) ht (D' n)
      exact ⟨k, hk.le, fun _ => ⟨hk, hge⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h' => absurd h' ht⟩
  choose k hk using hex
  obtain ⟨B, hBc, hB⟩ := EnsembleLemmas.exists_copiesRed D hSX hSY sX sY ℓ t k fun n => (hk n).1
  -- the machine's advantage is the concrete reduction's advantage
  have hBadv : ∀ n, distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) =
      distAdv (X.X n) (Y.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
    intro n
    have hlen : B.coinLen n = (t.eval n * sX.eval n + t.eval n * sY.eval n) + D.coinLen n := by
      simp [NUPPT.coinLen, hBc]
    obtain ⟨e, he⟩ : ∃ e : ((Fin (t.eval n) → Fin (sX.eval n) → Bool) ×
        (Fin (t.eval n) → Fin (sY.eval n) → Bool)) × D.Coins n ≃ B.Coins n,
        ∀ c, e c = EnsembleLemmas.coinsEquiv hlen
          (EnsembleLemmas.coinsEquiv rfl ((EnsembleLemmas.blocks _ _).symm c.1.1,
            (EnsembleLemmas.blocks _ _).symm c.1.2), c.2) :=
      ⟨((((EnsembleLemmas.blocks _ _).symm.prodCongr (EnsembleLemmas.blocks _ _).symm).trans
        (EnsembleLemmas.coinsEquiv rfl)).prodCongr (Equiv.refl _)).trans
          (EnsembleLemmas.coinsEquiv hlen), fun _ => rfl⟩
    have hpt : ∀ (z : Fin (ℓ.eval n) → Bool) c, B.distinguisher n (ℓ.eval n) z (e c) =
        multicopyRed
          (fun r : Fin (sX.eval n) → Bool => padFin (ℓ.eval n) (SX (NUPPT.advInput n (List.ofFn r))))
          (fun r : Fin (sY.eval n) → Bool => padFin (ℓ.eval n) (SY (NUPPT.advInput n (List.ofFn r))))
          (t.eval n) (k n) (D' n) z c := by
      intro z c
      rw [he]
      simp only [NUPPT.distinguisher, NUPPT.runAt_eq, EnsembleLemmas.ofFn_coinsEquiv, hB,
        multicopyRed, hD']
    have hdist : ∀ Z : Ensemble ℓ, acceptProb (Z.X n) (B.distinguisher n (ℓ.eval n)) =
        acceptProb (Z.X n) (multicopyRed (X.X n) (Y.X n) (t.eval n) (k n) (D' n)) := by
      intro Z
      rw [← EnsembleLemmas.acceptProb_coins_equiv e, ← EnsembleLemmas.acceptProb_multicopyRed_congr
        (hXc n) (hYc n)]
      congr 1
      funext z c
      exact hpt z c
    unfold distAdv
    rw [hdist, hdist]
  -- the hybrid bound at each `n`
  have hbound : ∀ n, distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) ≤
      (t.eval n : ℝ) * distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := by
    intro n
    rw [hBadv, hadv]
    by_cases ht : 0 < t.eval n
    · obtain ⟨-, hk2⟩ := (hk n).2 ht
      have htR : (0 : ℝ) < t.eval n := by exact_mod_cast ht
      rw [div_le_iff₀ htR] at hk2
      linarith
    · have ht0 : t.eval n = 0 := Nat.eq_zero_of_not_pos ht
      have hsub : Subsingleton (Fin (t.eval n) → Fin (ℓ.eval n) → Bool) := by
        rw [ht0]
        infer_instance
      rw [EnsembleLemmas.distAdv_eq_zero_of_subsingleton]
      exact mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  refine (EnsembleLemmas.negligible_polyExpr_mul t (h B)).mono ⟨0, fun n _ => ?_⟩
  have h₁ : (0 : ℝ) ≤ distAdv ((X.copies t).X n) ((Y.copies t).X n)
      (D.distinguisher n ((PolyExpr.mul t ℓ).eval n)) := abs_nonneg _
  have h₂ : (0 : ℝ) ≤ distAdv (X.X n) (Y.X n) (B.distinguisher n (ℓ.eval n)) := abs_nonneg _
  rw [abs_of_nonneg h₁, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) h₂)]
  exact hbound n

/-! ### Distinguishing versus predicting [PS10, p. 73, Lemma 73.8] -/

/-- The sampler of the prediction experiment `b ← {0,1}; t ← X^b_n` [PS10, Lemma 73.8]: output
the bit `b` together with a sample of `X¹_n` if `b = 1` and of `X⁰_n` otherwise (both seeds are
drawn; the unused one is ignored). -/
def mixEnsemble {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (n : ℕ) :
    Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool) :=
  fun z => (z.1, if z.1 then X₁.X n z.2.2 else X₀.X n z.2.1)

/-- **Predicting is distinguishing** — the identity behind [PS10, p. 73 ("any such predictor
would be a valid distinguisher (show this!)") and the proof of Lemma 73.8]: for samplers
`X⁰, X¹` and any `D` (used as a predictor of the bit `b` in `b ← {0,1}; t ← X^b`),
`Pr[D(t) = b] = 1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. In particular a predictor with
success `1/2 + δ` is a distinguisher with advantage `2δ`, and conversely.

**Repair (run-3 audit P2-2):** the seed types and the coin type carry `Nonempty` instances
(with an empty `ρ`, `σ₀` or `σ₁` the left-hand side is the probability over an empty space,
`0`, while the right-hand side is `1/2`); for ensemble seeds (`Ensemble.nonempty`) and machine
coins (`Fin k → Bool`) they are found by instance resolution.

**Proof sketch.** Split on `b` (`uprob_bool_prod` after regrouping the sample space): for
`b = 1` the event is `D(X¹) = 1`, for `b = 0` it is `D(X⁰) ≠ 1`, whose probability is
`1 − Pr[D(X⁰) = 1]` (`uprob_not`); the unused seed is an ignored uniform coordinate
(`acceptProb_fst`, `acceptProb_snd`). -/
theorem predict_eq {ℓ : ℕ} {σ₀ σ₁ ρ : Type*} [Fintype σ₀] [Fintype σ₁] [Fintype ρ]
    [Nonempty σ₀] [Nonempty σ₁] [Nonempty ρ]
    (X₀ : σ₀ → (Fin ℓ → Bool)) (X₁ : σ₁ → (Fin ℓ → Bool)) (D : (Fin ℓ → Bool) → ρ → Bool) :
    uprob (fun z : (Bool × (σ₀ × σ₁)) × ρ =>
        D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) =
      1 / 2 + (acceptProb X₁ D - acceptProb X₀ D) / 2 := by
  rw [← uprob_comp_equiv (Equiv.prodAssoc Bool (σ₀ × σ₁) ρ).symm, uprob_bool_prod]
  have hA : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₀ c.1.1) c.2 = false) =
      1 - acceptProb X₀ D := by
    rw [← acceptProb_fst (τ := σ₁) X₀ D, acceptProb, ← uprob_not]
    congr 1
    funext c
    simp
  have hB : uprob (fun c : (σ₀ × σ₁) × ρ => D (X₁ c.1.2) c.2 = true) = acceptProb X₁ D := by
    rw [← acceptProb_snd (τ := σ₀) X₁ D]
    rfl
  simp only [Equiv.prodAssoc_symm_apply, Bool.false_eq_true, if_false, if_true]
  rw [hA, hB]
  ring

/-- **The prediction lemma** [PS10, Lemma 73.8]: if a non-uniform PPT `D` distinguishes
`{X⁰_n}` and `{X¹_n}` with probability `μ(n)` for infinitely many `n`, then there is a
non-uniform PPT `A` with `Pr[b ← {0,1}; t ← X^b_n : A(1^n, t) = b] > 1/2 + μ(n)/2` for
infinitely many `n`.

**Repair (run-3 audit P2-2):** the ad hoc hypotheses `h₀ h₁ : ∀ n, Nonempty (X.σ n)` of the
run-2 statement were dropped; they are the field `Ensemble.nonempty`, and the frozen shape of
DESIGN.md §2.11 is restored.

**Proof sketch.** By `predict_eq` at each `n`, `D` itself predicts with probability
`1/2 + (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2` and the negated machine `D'` (output `[true]`
iff `D`'s output is not `[true]`: `EnsembleLemmas.exists_negRed`, i.e. `NUPPT.exists_comp`
with the FP-level `polyTimeComputable_ite` on `pairEq`) predicts with probability
`1/2 − (Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]) / 2`. On the infinite set of `n` where
`μ(n) < |Pr[D(X¹) = 1] − Pr[D(X⁰) = 1]|`, the sign of the difference is positive infinitely
often or negative infinitely often (pigeonhole on an infinite set, no advice needed); take
`A := D` in the first case and `A := D'` in the second. The seed-space reindexing between the
experiment of the statement and `predict_eq` is `uprob_comp_equiv`. -/
theorem prediction_lemma {ℓ : PolyExpr} (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ : ℕ → ℝ)
    (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n))) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1 / 2 + μ n / 2 <
      uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
        A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1 := by
  -- the signed advantage of `D`
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, ∀ n, δ n = acceptProb (X₁.X n) (D.distinguisher n (ℓ.eval n)) -
      acceptProb (X₀.X n) (D.distinguisher n (ℓ.eval n)) := ⟨_, fun _ => rfl⟩
  have hkey : ∀ n, distAdv (X₀.X n) (X₁.X n) (D.distinguisher n (ℓ.eval n)) = |δ n| := fun n => by
    rw [hδ]
    exact abs_sub_comm _ _
  -- predicting is distinguishing, for any machine `A`
  have hpred : ∀ (A : NUPPT) n, (uprob fun z : (Bool × (X₀.σ n × X₁.σ n)) × A.Coins n =>
      A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1) =
      1 / 2 + (acceptProb (X₁.X n) (A.distinguisher n (ℓ.eval n)) -
        acceptProb (X₀.X n) (A.distinguisher n (ℓ.eval n))) / 2 := fun A n =>
    predict_eq (X₀.X n) (X₁.X n) (A.distinguisher n (ℓ.eval n))
  by_cases hpos : ∀ n₀, ∃ n ≥ n₀, μ n < δ n
  · -- the difference is positive infinitely often: `D` itself predicts
    refine ⟨D, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hpos n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, ← hδ]
    linarith
  · -- otherwise it is negative infinitely often: the negated machine predicts
    push_neg at hpos
    obtain ⟨n₁, hn₁⟩ := hpos
    have hneg : ∀ n₀, ∃ n ≥ n₀, μ n < -δ n := by
      intro n₀
      obtain ⟨n, hn, hlt⟩ := h (max n₀ n₁)
      refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
      have h1 := hn₁ n (le_trans (le_max_right _ _) hn)
      rw [hkey] at hlt
      rcases le_or_gt 0 (δ n) with h0 | h0
      · rw [abs_of_nonneg h0] at hlt
        linarith
      · rw [abs_of_neg h0] at hlt
        exact hlt
    obtain ⟨A, hAc, hA⟩ := EnsembleLemmas.exists_negRed D
    refine ⟨A, fun n₀ => ?_⟩
    obtain ⟨n, hn, hlt⟩ := hneg n₀
    refine ⟨n, hn, ?_⟩
    rw [hpred, EnsembleLemmas.acceptProb_negRed hAc hA, EnsembleLemmas.acceptProb_negRed hAc hA]
    have := hδ n
    linarith

/-! ### The pairwise-independent sampling inequality [PS10, Appendix A, p. 189] -/

/-- **Pairwise-independent sampling inequality** [PS10, Appendix A, p. 189]: for pairwise
independent bits `X_1, …, X_m`, each `true` with probability `p`, and `ε > 0`,
`Pr[|∑ᵢ X_i / m − p| ≥ ε] ≤ 1 / (4 ε² m)`. The concrete lemma is
`HardcoreBit.chebyshev_pairwise_ident` [Gar26, Theorem 2.4], restated with the empirical mean.

**Deviation:** the text states the inequality for real random variables with `|X_i| ≤ 1` and
mean `μ` with the bound `(1 − μ²)/(m ε²)`; here the variables are bits (the only case used in
the campaign) and the bound is the variance bound `p(1−p) ≤ 1/4` of the concrete layer. Bits
satisfy the text's hypothesis, and `1/4 > 1 − p²` exactly when `p > √3/2`, so for such `p`
this bound is weaker than the text's (at `p = 1` the text gives `0`); the variance form
`p(1−p)/(m ε²)` would imply both. -/
theorem pairwise_sampling_ineq {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι]
    {X : ι → Ω → Bool} (hX : HardcoreBit.PairwiseIndep X) {p : ℝ}
    (hp : ∀ i, uprob (fun ω => X i ω = true) = p) {ε : ℝ} (hε : 0 < ε)
    (hm : 0 < Fintype.card ι) :
    uprob (fun ω => ε ≤ |(∑ i, HardcoreBit.ind (X i ω)) / Fintype.card ι - p|) ≤
      1 / (4 * ε ^ 2 * Fintype.card ι) := by
  have hm' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hm
  refine le_of_eq_of_le ?_ (HardcoreBit.chebyshev_pairwise_ident hX hp hε hm)
  apply OneWay.uprob_congr
  intro ω
  rw [show (∑ i, HardcoreBit.ind (X i ω)) / (Fintype.card ι : ℝ) - p =
      (∑ i, HardcoreBit.ind (X i ω) - p * Fintype.card ι) / Fintype.card ι by
        field_simp, abs_div, abs_of_pos hm', le_div_iff₀ hm']

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Negligible.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Negligible and noticeable functions

A function of the security parameter is negligible when it eventually falls below every
inverse polynomial, and noticeable when it eventually stays above some inverse
polynomial. Security definitions allow an adversary negligible success; hardness
amplification starts from a noticeable failure probability. The two notions are not
complementary: a function can be neither.

The functions here take real values and the conditions bound `|μ n|`, so that
differences of probabilities can be fed in directly. [Gar26] restricts to values in
`[0, 1]`; on such functions the definitions agree.

## Main definitions

* `Negligible μ`: for every `c`, eventually `|μ n| < 1 / n^c`.
* `Noticeable μ`: for some `c`, eventually `μ n > 1 / n^c`.

## Main results

* `Negligible.add`, `Negligible.mul`, `Negligible.const_mul`, `Negligible.mono`: closure.
* `Negligible.mul_pow`: a negligible function times a polynomial is negligible.
* `negligible_two_pow_neg`: `2^{-n}` is negligible; `negligible_zero`: so is the constant `0`.
* `Noticeable.not_negligible`: noticeable functions are not negligible.
* `not_negligible_sub`: a non-negligible function minus a negligible one is
  non-negligible.
* `exists_not_negligible_not_noticeable`: some function is neither.
* `not_negligible_iff`: a function is non-negligible exactly when it exceeds some
  inverse polynomial infinitely often.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 (Definitions 1.3 and 1.4, Exercise 1.1) and
  Exercises 2.1 and 2.2.
-/

namespace TCSlib.Cryptography

/-- A function `μ` of the security parameter is negligible when for every `c` there is
`n₀` with `|μ n| < 1 / n^c` for all `n ≥ n₀`. [Gar26, Definition 1.4], for real-valued
functions bounded in absolute value; on `[0, 1]`-valued functions this is the source's
definition. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c

/-- A function `μ` is noticeable when there are `c` and `n₀` with `μ n > 1 / n^c` for all
`n ≥ n₀`. [Gar26, Definition 1.3]. -/
def Noticeable (μ : ℕ → ℝ) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, 1 / (n : ℝ) ^ c < μ n

variable {μ ν : ℕ → ℝ}

/-- A function eventually dominated in absolute value by a negligible one is negligible.
Technical glue. -/
theorem Negligible.mono (hμ : Negligible μ) (h : ∃ n₀, ∀ n ≥ n₀, |ν n| ≤ |μ n|) :
    Negligible ν := by
  intro c
  obtain ⟨n₀, h₀⟩ := h
  obtain ⟨n₁, h₁⟩ := hμ c
  exact ⟨max n₀ n₁, fun n hn =>
    (h₀ n (le_of_max_le_left hn)).trans_lt (h₁ n (le_of_max_le_right hn))⟩

/-- The sum of two negligible functions is negligible. [Gar26, Exercise 1.1(1)–(2)].

**Proof sketch.** Bound each by `1 / n^(c+1)` eventually; their sum is below
`2 / n^(c+1) ≤ 1 / n^c` once `n ≥ 2`. -/
theorem Negligible.add (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n + ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ (c + 1)
  obtain ⟨n₂, h₂⟩ := hν (c + 1)
  refine ⟨max (max n₁ n₂) 2, fun n hn => ?_⟩
  have hn₁ : n ≥ n₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by linarith) c
  have key : 2 * (1 / (n : ℝ) ^ (c + 1)) ≤ 1 / (n : ℝ) ^ c := by
    have hinv : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
    have ha : 0 < 1 / (n : ℝ) ^ c := by positivity
    rw [pow_succ, ← one_div_mul_one_div]
    nlinarith
  calc |μ n + ν n| ≤ |μ n| + |ν n| := abs_add_le _ _
    _ < 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_lt_add (h₁ n hn₁) (h₂ n hn₂)
    _ ≤ 1 / (n : ℝ) ^ c := by linarith

/-- The product of two negligible functions is negligible. [Gar26, Exercise 1.1(3) and
Exercise 2.1].

**Proof sketch.** Eventually `|ν n| < 1` (the bound for `c = 0`), so
`|μ n ν n| ≤ |μ n| < 1 / n^c`. -/
theorem Negligible.mul (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n * ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ c
  obtain ⟨n₂, h₂⟩ := hν 0
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have hν1 : |ν n| < 1 := by simpa using h₂ n (le_of_max_le_right hn)
  rw [abs_mul]
  calc |μ n| * |ν n| ≤ |μ n| * 1 := mul_le_mul_of_nonneg_left hν1.le (abs_nonneg _)
    _ < 1 / (n : ℝ) ^ c := by rw [mul_one]; exact h₁ n (le_of_max_le_left hn)

/-- A negligible function times the polynomial `n^d` is negligible. Used whenever a
hybrid argument multiplies an advantage by a polynomial number of hybrids. [Gar26,
§1.2, "any polynomial function of a negligible function is still negligible"].

**Proof sketch.** Given `c`, use the bound for `c + d`. -/
theorem Negligible.mul_pow (hμ : Negligible μ) (d : ℕ) :
    Negligible (fun n => (n : ℝ) ^ d * μ n) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ (c + d)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by linarith) d
  rw [abs_mul, abs_of_pos hpos]
  calc (n : ℝ) ^ d * |μ n| < (n : ℝ) ^ d * (1 / (n : ℝ) ^ (c + d)) :=
        mul_lt_mul_of_pos_left (h₀ n (le_of_max_le_left hn)) hpos
    _ = 1 / (n : ℝ) ^ c := by
        rw [pow_add]; field_simp

/-- A constant multiple of a negligible function is negligible. [Gar26, §1.2].

**Proof sketch.** For `n ≥ |a|`, `|a μ n| ≤ |n μ n|`, and `n μ n` is negligible by
`Negligible.mul_pow`. -/
theorem Negligible.const_mul (hμ : Negligible μ) (a : ℝ) :
    Negligible (fun n => a * μ n) := by
  refine (hμ.mul_pow 1).mono ⟨⌈|a|⌉₊, fun n hn => ?_⟩
  have ha : |a| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [abs_mul, abs_mul, pow_one, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

/-- The function `2^{-n}` is negligible. [Gar26, §1.2, Example after Definition 1.4].

**Proof sketch.** `n^c < 2^n` for all large `n`. -/
theorem negligible_two_pow_neg : Negligible (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro c
  have ht := tendsto_pow_const_div_const_pow_of_one_lt c (r := (2 : ℝ)) one_lt_two
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hlt : (n : ℝ) ^ c < 2 ^ n :=
    (div_lt_one (by positivity)).mp (h₀ n (le_of_max_le_left hn))
  show |(2 : ℝ)⁻¹ ^ n| < 1 / (n : ℝ) ^ c
  rw [abs_of_pos (by positivity), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt (pow_pos (by linarith) c) hlt

/-- The constant zero function is negligible: `|0| = 0 < 1 / n^c` for every `n ≥ 1`. Technical
glue (the advantage of a distinguisher between two equal distributions). Added by the
Pass–shelat campaign (gate 03a, ruling G3-7a), which moved it here from
`Asymptotic/Ensembles.lean` under its unchanged full name. -/
theorem negligible_zero : Negligible fun _ : ℕ => (0 : ℝ) := by
  intro c
  refine ⟨1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-- A noticeable function is not negligible. [Gar26, §1.2].

**Proof sketch.** With the noticeability exponent `c`, at any `n` past both thresholds
`1 / n^c < μ n ≤ |μ n| < 1 / n^c`. -/
theorem Noticeable.not_negligible (hμ : Noticeable μ) : ¬ Negligible μ := by
  intro hneg
  obtain ⟨c, n₀, h₀⟩ := hμ
  obtain ⟨n₁, h₁⟩ := hneg c
  have a := h₀ (max n₀ n₁) (le_max_left _ _)
  have b := h₁ (max n₀ n₁) (le_max_right _ _)
  linarith [le_abs_self (μ (max n₀ n₁))]

/-- A function is non-negligible exactly when there is `c` such that `|μ n| ≥ 1 / n^c`
for infinitely many `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"]. -/
theorem not_negligible_iff :
    ¬ Negligible μ ↔ ∃ c : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, 1 / (n : ℝ) ^ c ≤ |μ n| := by
  simp only [Negligible, not_forall, not_exists, not_lt, exists_prop]

/-- If `μ` is not negligible and `ν` is negligible then `μ - ν` is not negligible.
[Gar26, §2.2.2, footnote 3 (exercise)].

**Proof sketch.** Otherwise `μ = (μ - ν) + ν` would be negligible. -/
theorem not_negligible_sub (hμ : ¬ Negligible μ) (hν : Negligible ν) :
    ¬ Negligible (fun n => μ n - ν n) := by
  intro h
  exact hμ (by simpa using h.add hν)

/-- Some function into `[0, 1]` is neither negligible nor noticeable: `2^{-n}` at even
`n` and `n^{-3}` at odd `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"].

**Proof sketch.** The values lie in `[0, 1]` directly. At odd `n` the value is `1 / n^3`,
so the bound for `c = 3` fails infinitely often and `μ` is not negligible
(`not_negligible_iff`). At even `n` the value is `2^{-n}`, which is eventually below every
`1 / n^c` (`negligible_two_pow_neg`), so `μ` is not noticeable. -/
theorem exists_not_negligible_not_noticeable :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n ∧ μ n ≤ 1) ∧ ¬ Negligible μ ∧ ¬ Noticeable μ := by
  refine ⟨fun n => if n % 2 = 0 then (2 : ℝ)⁻¹ ^ n else 1 / (n : ℝ) ^ 3, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs with h
    · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact ⟨by positivity, div_le_one_of_le₀ (one_le_pow₀ hn) (by positivity)⟩
  · refine not_negligible_iff.mpr ⟨3, fun n₀ => ⟨2 * n₀ + 1, by omega, ?_⟩⟩
    dsimp only
    rw [if_neg (by omega)]
    exact le_abs_self _
  · rintro ⟨c, n₀, h₀⟩
    obtain ⟨n₁, h₁⟩ := negligible_two_pow_neg c
    have h := h₀ (2 * max n₀ n₁) (by omega)
    have h' := h₁ (2 * max n₀ n₁) (by omega)
    dsimp only at h h'
    rw [if_pos (by omega)] at h
    rw [abs_of_pos (by positivity)] at h'
    linarith

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.InformationTheory.Extractors

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical closeness of samplers and of distributions

The ch. 2–4 layer measures the distance between two samplers from uniform seeds by test sets
(`StatClose`, `Asymptotic/Sampling.lean`). The information-theory layer measures the distance
between two finite distributions by distinguishers (`EpsClose`,
`InformationTheory/Extractors.lean`).
On a finite sample space the two agree: two samplers are `δ`-close exactly when the laws they push
the uniform seed distribution to are `δ`-close. This closes duplication-ledger item DL-4.

## Main definitions

None.

## Main results

* `uprob_comp_eq_probTrue_map`: the probability that a test accepts a sample is its acceptance
  probability under the sampler's law.
* `statClose_iff_epsClose_map`: `StatClose X Y δ` iff `EpsClose δ` between the laws of `X`
  and `Y`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 181.1 (`ε`-closeness) and §2.4.2 (statistical closeness of samplers, the device of
  the ch. 2–4 layer's decision D10).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {σ τ γ : Type*} [Fintype σ] [Fintype τ] [Nonempty σ] [Nonempty τ] [Fintype γ]
  [DecidableEq γ]

/-- The probability that the test `D` accepts `X s` for a uniform seed `s` is the acceptance
probability of `D` under the law of `X` (the uniform distribution pushed forward along `X`). -/
theorem uprob_comp_eq_probTrue_map (X : σ → γ) (D : γ → Bool) :
    uprob (fun s => D (X s) = true) = ((FinDist.uniform σ).map X).probTrue D := by
  rw [uprob_comp_eq_sum_map X (fun g => D g = true), FinDist.probTrue]

/-- **Statistical closeness of samplers is closeness of their laws:** on a finite sample space,
`StatClose X Y δ` (every test set moves by at most `δ`) holds exactly when the laws of `X` and
`Y` are `δ`-close as finite distributions (every distinguisher has advantage at most `δ`).
[PS10, Def 181.1]

**Proof sketch.** A distinguisher `D` is the test set `{g | D g = true}`, and a test set `T` is
the distinguisher `decide ∘ T`; in both directions `uprob_comp_eq_probTrue_map` turns the
probability over seeds into the acceptance probability under the law. -/
theorem statClose_iff_epsClose_map (X : σ → γ) (Y : τ → γ) (δ : ℝ) :
    StatClose X Y δ ↔ EpsClose δ ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  constructor
  · intro h D
    rw [← uprob_comp_eq_probTrue_map, ← uprob_comp_eq_probTrue_map]
    exact h fun g => D g = true
  · intro h T
    classical
    have hX : uprob (fun s => T (X s)) = uprob (fun s => decide (T (X s)) = true) := by simp
    have hY : uprob (fun t => T (Y t)) = uprob (fun t => decide (T (Y t)) = true) := by simp
    rw [hX, hY, uprob_comp_eq_probTrue_map X (fun g => decide (T g)),
      uprob_comp_eq_probTrue_map Y (fun g => decide (T g))]
    exact h _

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 proper is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

**As-built note (2026-11-05, gate 03l; the sketch above is unchanged).** The `pairSplitAt`
machine (`Randomized/Build/PairSplit.lean`) uses one work tape, not two: the parser stores `u`,
and the copy scan of `b` doubles each bit while the work head walks across the stored `u`. Its
buffered aligned parser is public (`Turing.PairParse`) and is shared by the `unaryMul` machine
(`Randomized/Build/UnaryMul.lean`), which stores `u` and replays it once per symbol of `v`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

**As-built erratum (2026-11-05, gate 03l, minor 2; the frozen text above is unchanged).** The
machine of `polyTimeComputable_iterateFind` (`Randomized/Build/IterateFind.lean`, with
`Randomized/Build/IterateFindHost.lean` and the public host `TuringMachine/Build/ModuleHost.lean`)
departs from steps 1–5 and 7 as follows. The frozen signatures and decisions are unchanged.
- *Step 1: the guard and the invariant.* The guard tests the **new** point:
  `stepF x w := if |g (pairSndD w)| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`. The guard
  on the old length written above does not close `Inv`: for `x = []`, `P = var` and
  `g s = true :: s`, the word `⟨[], []⟩` satisfies `Inv`, passes the guard `0 ≤ 0`, and steps to
  `⟨[], [true]⟩`, which does not. The machine's invariant is the actual-pair invariant
  `Inv x w := ∃ s, w = pairEncode x s ∧ |s| ≤ P|x|`, which, unlike `pairFstD w = x ∧ …`, excludes
  malformed words and gives the length bound `|w| ≤ 2|x| + 2 + P|x|` that the budget needs.
  (`Repetition.lean`'s `guardedStep` is the same step; its `LoopInv` is the pure invariant above,
  not the machine's.)
- *Steps 2–3: the gluing.* No transition is redirected. A release flag halts each clean-call
  module one silent step after its first positive exit, and the run is cut at its first halt
  (the clean-module contract `Turing.ModuleHost.Clean`, `clean_install`, `clean_emit`). The
  modules are padded to a common bank of tapes and run in one finite host with states
  `Fin 3 ⊕ Σ i, (M i).State` over five modules (copier, startup install `x ↦ ⟨x, x⟩`, verdict
  install, step install, payload emit): the anchor `inl 0`, the branch `inl 1` and the halt
  `inl 2`. This host is now the public clean-module host `Turing.ModuleHost.hostTM`
  (`machine-library-design.md` §14, row H14), harvested on 2026-11-05 from `ClassNP/SAT.lean`'s
  private module layer and this machine's copy of it.
- *Step 4: the startup.* The input is copied onto tape 0 by a two-state copier (`copyTM`: copy and
  turn, then rewind both heads), not by a one-state scan and `timed_rewind`.
- *Step 5: the budget.* Every request has length at most `2n + 6 + P n`, and the common budget is
  `T n = A·(2n + 7 + P n)^D` (`IterateFind.lean`), with `A` and `D` collected from the modules'
  budgets and the fuel machine.
- *Step 7.* `iterate`'s counter test is `R|x| ≤ |cnt|` (`StateLoop.IterLoop.acc`), not `lenEq`.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): the
   source's p.p.t. prover writes at most `t(|x|)` bits. Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges /
    colour permutations); one-iteration ZK, `n`-fold protocols get soundness only (sequential
    composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no
    source protocol attains them under D8/D10; GI is `StatZK` with negligible δ, and
    `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}`
    (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least"; Lemma 50.15: "`N > 2`
    composite" should be odd composite.
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary.
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for every protocol whose hiding is only computational: with `|z| ≥ 2^n` the
    distinguisher, whose input (the view) contains `z`, may run in time `2^n`, invert the OWP on
    `n`-bit inputs and open the unopened commitments. So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (deferred); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | The `j`-th block of `c` bits of a coin string, `(r.drop (j * c)).take c`, stated three times: `coinSlice` (`ZeroKnowledge/GraphIsomorphism.lean`, ch. 2–4), `Authentication.coinBlock` (`Authentication/Lamport.lean`, prong A), `Protocol.phaseSlice` (`Composability/SequentialZK.lean`, prong C) | found by the Lamport worker and the maintainer | Before the ch. 5–8 statement gate: one copy in a shared upstream module, with its length lemma, used by all three. |
| DL-7 | `List.ofFn (padFin ℓ w) = w` for `|w| = ℓ`: `Authentication.ofFn_padFin_of_length` (`Lamport.lean`) is the equal-length case of ch. 2–4's `ofFn_padFin_of_le` (`Asymptotic/Collections.lean`); `Composability.length_eval_of_length` (`CCA2Scheme.lean`) repeats the step inline | found by the Lamport worker | Before the ch. 5–8 statement gate: use `ofFn_padFin_of_le (le_of_eq h)`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, six copies plus an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`; with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
