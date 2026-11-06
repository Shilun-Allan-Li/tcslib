# Gate 03b: review of the external auditor's findings

## Summary

- **Verdicts.** Of the 14 findings, 12 are **true**, 1 is **partly true** (#1) and 1 (#14) is
  **true but now resolved**: the auditor could not check it, and I did; the repair holds. None is
  false.
- **Severity.** Keep **#1 as a major, not a blocker**.
  - The gap in the interface is real, and the counterexample is a valid model of every field.
  - But the consequence the auditor feared does not occur in the code. The formal Algorithm 104.3
    (`tdpBitScheme`, `Asymptotic/PublicKey.lean`, pack 03d) does not use `HardCore`'s evaluator.
    It takes a separate `Collection.PredEvaluator`, whose `spec` already holds on every decodable
    string (PublicKey.lean:529–540), and its correctness is proved (:679–693).
  - So the auditor's blocker trigger is not met: no statement in ch. 2–4 or ch. 5–8 is false
    because of #1.
  - The cost is debt: two local patches already exist (`PredEvaluator` in ch. 2–4;
    `SamplerCanonical` and `hspec` in ch. 5–8's OT). In addition, the "text's reading" of
    Thm 104.4 carries an evaluator `E` that cannot be derived for a general `T`.
- **Other severity changes.** Only one: split #12. Item (c), the undisclosed copies, becomes
  **minor**, because `policy.md` requires a human approval or a removal. Items (a), (b) and (d)
  stay notes.
- **Recommended fix for #1.** Canonical decoding: one new field,
  `Collection.encD_decD : decD i w = some x → encD i x = w`.
  - I checked every decoder in ch. 2–4: `decodeFin`, `expDec`, `decodeDistinctPrimes`,
    `rsaDec`, `rabinDec`, `blumDec` and `glPad`'s. All are already canonical, so each instance
    needs only a short lemma. No existing field, statement or proof changes.
  - It makes `PredEvaluator`, OT's `SamplerCanonical` and OT's `hspec` derivable.
  - **This needs the user's ruling** (Q1), because `Collection` is cited by ch. 5–8.
- **Missed by the auditor (most important).** Prong B's Proposition 161.5
  (`otProtocol_simulators`, `otProtocol_hbcSecure`, `ObliviousTransfer.lean:395, :427`) **cannot
  be proved as stated**.
  - Take any trapdoor permutation with a hard-core bit, and let its sampler output `f_i(u)` for a
    uniform `u`. The result still satisfies every hypothesis, `SamplerCanonical` included.
  - Bob's view contains his sampler coins, so he learns `h(u) = h(f⁻¹(y_{1−b}))` and with it
    `a_{1−b}`.
  - This is the "enhanced trapdoor permutation" gap that the auditor raised as note #7, but the
    note does not say that ch. 5–8 already depends on it.
  - It belongs to gate 06B, not 03b, and needs a ruling there (Q3). No fix for #1 repairs it.
- **Pending packs.**
  - **03d, 03f1 and 03f2 must wait** for the #1 fix: their files hold the consumer `PredEvaluator`
    (03d) and the `Collection` instances (03f1, 03f2).
  - 03c, already in triage, has the `Collection.glPad` instance and must coordinate.
  - **03g, 03h, 03i, 03j, 03k and 03l are unaffected** under the recommended options.

## How this was checked

- **Code.** I read every Lean reference at `a3c5fa8b` in `wt-g03`. Downstream code was read at
  the heads of the sibling worktrees:
  - prong A `2d7b5441`;
  - prong B `1cf007d1`;
  - prong C `aa71d0e7`;
  - prong D `6ea900ae`;
  - S2b `afe5982f`.
- **Uses.** Every use of `Collection`, `PermCollection`, `TrapdoorCollection`, `HardCore`,
  `PredEvaluator`, `sample_spec`, `inv_spec`, `eval_spec` and `ofString` was found by grep. Every
  `Collection` instance was enumerated. I read each decoder against its encoder.
- **Source.** The source checks used the pdftotext extracts `wt-g03/blueprint/src/references/
  pass-shelat-2010-ch2.raw.md` (and ch3, ch4), and `scratchpad/source-pdf/ch5-8.txt` for §5.8 and
  §6.2.4.
- **Not done.** No Lean was built or run. The Lean sketches below are unchecked.

## Overview

| # | Auditor | Verdict | Proposed severity | Fix kind | Gate-03 packs touched | ch. 5–8 touched | Ruling? |
|---|---|---|---|---|---|---|---|
| 1 | major | partly true | **major** (not blocker) | new field + lemmas (option A) | 03b, 03c, 03d, 03f1, 03f2 | OT (B): patches become derivable; Claim 172.a (C): unchanged | **yes (Q1)** |
| 2 | minor | true | minor | docstring (D5, `FunFamily`, module) | 03b only | none | no |
| 3 | minor | true († resolved) | minor | docstring | 03b only | none | no |
| 4 | minor | true | minor | docstring (sketches) | 03b only | none | no |
| 5 | note | true | note | optional docstring | 03b only | none | no |
| 6 | note | true | note | docstring + DESIGN §5 entry 17 | 03b only | none | no |
| 7 | note | true, but its consequence was missed | note for 03b; **blocker for 06B** | none here; statement change in prong B | none | OT (B) | **yes, at 06B (Q3)** |
| 8 | note | true | note | DESIGN §5 line; optional bridge | 03b only | none | no |
| 9 | note | true (the rewording overshoots slightly) | note | docstring + DESIGN §5 entry 16 | 03b only | none | no |
| 10 | note | true | note | docstring | 03b only | none | no |
| 11 | note | true (not re-derived) | note | none | none | none | no |
| 12 | note | true; a third copy exists | (a), (b), (d) note; **(c) minor** | attribute approvals; ledger; a file split | 03b only, if done as proposed | none | **yes (Q2)** |
| 13 | note | true | note | new non-vacuity lemmas + `Checks.lean` prints | 03b only | none | no |
| 14 | note | true; **resolved here** | closed | none | none | none | no |

---

## #1 (major): the collection interface pins its string algorithms only up to decoding

**The claim.**
- `eval` is specified on canonical encodings and on sampled strings, the `HardCore` evaluator only
  on canonical encodings, and `Inv` only up to decoding.
- A lenient `decD` therefore lets a collection satisfy every field while the sampler's and `Inv`'s
  outputs are strings on which `H` (and `eval`) misbehave.

**Check: partly true.**

- **The fields are as the auditor says.**
  - `Collections.lean:143`: `eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x`.
  - `Collections.lean:152–155`: `sample_spec` gives "`∃ x, decD … (sample.runAt …) = some x ∧
    eval ⟨i, ·⟩ = f i x`". This is membership *up to decoding*.
  - `Collections.lean:209`: `HardCore`'s first clause is
    `∀ i x, H (pairEncode i (F.encD i x)) = [h i x]`, canonical encodings only.
  - `Collections.lean:274–275`: `inv_spec : … decD _ (inv.runAt n (pairEncode t (encD _ y)) s) =
    some ((perm _).symm y)`, decode level.
  - `Collections.lean:284–288`: `inv_preimage` is decode level.
  - Nothing requires `decD` to be canonical. Only `decD_encD` (:127) is required.
- **The counterexample is a valid model of every field.** I re-derived each clause:
  - `decD_encD`, `f_perm` (with `f i x = false :: f₀ i x = encD (perm x)`) and `eval_spec` on
    `false :: …` hold.
  - `sample_spec` holds on `true :: w₀`, from `T₀.sample_spec`.
  - `inv_spec` holds.
  - `SampleClose` holds: the decoded laws are equal.
  - Hardness holds. One small omission in the auditor's reduction: the `T₀`-inverter must also
    prepend `false` to `y` before calling the `T`-inverter, and then drop the first output bit.
  - `HardCore h` holds. Its evaluator `H ⟨i, b :: w⟩ = [H₀⟨i,w⟩.headD false ⊕ b]` is correct on
    `false :: …`.
  - The variant (`Inv` emits `true ::`, and `eval ⟨i, true :: w⟩ := []`) is also a model.
    `eval ⟨i, Inv(t, y)⟩ = [] ≠ y`, while `inv_preimage` still holds.
- **But "Algorithm 104.3 built on `T` decrypts every ciphertext to the flipped bit" does not apply
  to the code.** The auditor did not have `PublicKey.lean` (see their Limitations).
  - `tdpBitScheme` (PublicKey.lean:671) takes `E : T.toCollection.PredEvaluator h`. It does not
    take `HardCore`'s `H`.
  - `PredEvaluator.spec` (:540) is `∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x]`.
    This is exactly the auditor's own "lenient" fix for `HardCore`. Its docstring (:529–533)
    already says why: "the outputs of the sampler and of the trapdoor inverter need not be
    canonical".
  - The flipped `H` of the counterexample is **not** a `PredEvaluator`. A valid one exists,
    `H' ⟨i, b :: w⟩ := H₀ ⟨i, w⟩`, and with it `tdpBitScheme.correct` holds. The field is proved,
    with no `sorry`, at :679–693, from `evalSampled`, `inv_spec` and `E.spec`.
  - Thm 104.4 (`tdpBitScheme_singleBitSecure`, :826) and prong C's Claim 172.a
    (`Composability/PublicKey.lean:430`) both carry `E`.
- **No consumer evaluates `f_i` on `Inv`'s output** (grep for `eval … inv.runAt`). The variant is
  latent. It would bite PS10 §5.8's trapdoor signatures (inventory Claim-148.b, *optional*, not
  implemented in prong A).
- **Where the infidelity sits.** The auditor places it in Def 41.1 (3). It is more precisely in
  **(2)** ("returns a uniformly random *element* of `D_i`": the formal version accepts any
  string that decodes) and in **Def 56.1 (6)** ("computes `f⁻¹(y)`": the formal version only
  requires the output to decode).
  - Clause (3), "on input `i, x ∈ D_i` computes `f_i(x)`", is about the element's own
    representation. `eval_spec` is faithful to it.
  - The inventory row Def-41.1 should be reworded to match.

**Severity: keep major; not a blocker.** Under the 03a guide, the blocker condition ("a downstream
statement would build on a wrong definition") is not met: every consumer that computes on produced
strings carries a patch. It stays major for three reasons:
1. **Fitness for use (brief item 5).** The interface cannot express its own consumers without
   per-consumer patches. Two patches exist already: `PredEvaluator` in ch. 2–4, and
   `SamplerCanonical` plus `hspec` in prong B's OT.
2. **A headline is conditional on undischargeable data.** "The text's reading of Thm 104.4",
   `TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure` (PublicKey.lean:944), still
   needs `E : (T.glPad m henc).toCollection.PredEvaluator T.glBit`.
   - `exists_glBitCollEvaluator` (`HardCoreGLColl.lean:141`) only gives `H` on
     `⟨encD x, ofFn ρ⟩`. For a lenient `T`, `E` would have to canonicalize `T`'s encoding, which
     need not be efficient.
   - So "TDPs ⇒ single-bit PKE" is not derivable from `T.OneWay` alone. The docstring of
     `TrapdoorCollection.OneWay.glPad_hardCore` (`HardCore.lean:973–975`, "satisfiable from
     trapdoor permutations alone") overstates this.
3. **The debt is open-ended.** The next consumer (e.g. Claim-148.b) has to patch again.

**Repair options.**

| | Option | What changes in ch. 2–4 | Instances to re-prove | Gate-03 packs | ch. 5–8 patches |
|---|---|---|---|---|---|
| **A (recommended)** | **Canonical decoding**: new field `encD_decD : ∀ i w x, decD i w = some x → encD i x = w` | One field and derived lemmas in `Collections.lean`; optional E-free corollary in `PublicKey.lean` | One short decoder lemma per instance (list below); existing `sample_spec`/`inv_spec` proofs and sorried stubs unchanged | 03b, 03c (`glPad`), 03f1, 03f2, 03d (optional corollary) | OT: `SamplerCanonical` becomes a theorem (drop `hcanon`); `hspec` is implied by the canonical spec; Claim 172.a unchanged |
| B | **Canonical outputs**: `sample_spec` and `inv_spec` restated as string equalities (`sample.runAt … = encD _ x`, `inv.runAt … = encD _ (perm⁻¹ y)`); `HardCore` unchanged; `PredEvaluator.spec` weakened to canonical encodings | Two fields restated; `evalSampled` derived; `PredEvaluator` restated (03d) | Re-prove `sample_spec` for `toCollection` (trivial), `factoringCollection` (`samplePairOut_eq_encode` already gives it) and `glPad`. Restate the four **sorried** stubs `expSampler_spec`, `rsaSampler_spec`, `rabinSampler_spec`, `blumSampler_spec`. `rsaInv_spec` (proved: drop its final decode step), `blumInv_spec` (sorried: restate), `TrapdoorCollection.glPad` | 03b, 03c, 03d, 03f1, 03f2 | OT: `SamplerCanonical` is the field (drop `hcanon`); `hspec` weakens to canonical encodings; Claim 172.a: same statement, `E`'s type changes meaning |
| C | **Named hypothesis**: `def Collection.Canonical F : Prop := ∀ i w x, F.decD i w = some x → F.encD i x = w`, with instance lemmas, carried by consumers | Predicate + derived lemmas under `(hc : F.Canonical)`; Thm 104.4's text reading takes `hc` in place of `E` | The same decoder lemmas as A, but as stand-alone theorems; no instance *definition* changes | 03b, 03d; 03c/03f1/03f2 only gain lemmas, which can follow their audits | OT: `hcanon` becomes `hc : T.Canonical` |
| D | **Keep the interface** (auditor's option iii): document the decode-level reading as a deviation, and accept the debt | Docstrings on `Collection`/`sample_spec`, `HardCore`, `TrapdoorCollection`/`inv_spec`, `inv_preimage`; fix `HardCore.lean:973–975`; a DESIGN §5 line | none | 03b, 03c (docstring) | Unchanged; each patch should cite the new deviation |

**Not recommended:** the auditor's lenient alternative, i.e. strengthening `eval_spec` *and*
`HardCore`'s first clause to every decodable string.
- It breaks `Collection.OneWay.glPad_hardCore` (`HardCore.lean:884`) for collections with lenient
  decoders. The Goldreich–Levin evaluator `⟨i, ⟨a, b⟩⟩ ↦ ip(pad a, b)` reads the *raw* first
  component `a`.
- To be right on every `a` that decodes to `x`, it would have to compute `encD x` from `a`. That
  requires an efficient canonicalizer, which no hypothesis supplies.
- So Goldreich–Levin for collections would need a new hypothesis, i.e. a statement change in
  03c's file.

**Why A.**
- A is the auditor's primary fix.
- Every ch. 2–4 decoder is already canonical:
  - `decodeFin` (`Collections.lean:353`): `w = ofFn x`.
  - `expDec` (`DiscreteLog.lean:208–210`): an exact-width numeral below `m`.
  - `decodeDistinctPrimes` (`Concrete.lean:455–461`): `pairDecode` must succeed, because
    `decodeFin m [] = none` for `m = max |i| 2 ≥ 2`; then two `decodeFin` blocks and
    `natToBits_bitsToNat`.
  - `rsaDec` (`RSA.lean:235–241`): an exact-width numeral below `N` and coprime to it, or the
    single canonical string at an invalid index.
  - `rabinDec` (`Rabin.lean:400–403`) and `blumDec` (:687–692): the same pattern.
  - `glPad`'s decoder (`HardCore.lean:735–739`): `pairDecode`, then `F.decD`, then `decodeFin`.
- So A changes no existing statement or proof and adds no `sorry`.
- Canonical decoding also matches the text's inversion game. A lenient decoder only makes the
  adversary's task easier, i.e. hardness stronger than the text's, so nothing is lost.
- Under A, any `H` correct on canonical encodings is correct on every decodable string. Hence:
  - `PredEvaluator` follows from `HardCore`;
  - the E-free "TDPs ⇒ single-bit PKE" follows from `hT.glPad_hardCore` and
    `exists_glBitCollEvaluator`;
  - OT's `SamplerCanonical` follows from `sample_spec`.
- C carries the same lemmas without touching the instance definitions. It is the right choice
  only if the user wants 03f1/03f2 to proceed unblocked.

**A, Lean-level sketch** (unchecked).

```lean
-- Collections.lean, in `structure Collection`, after `decD_encD`:
  /-- Decoding is canonical: a string decodes only if it is the encoding of its value, so the
  sampler's outputs (`sample_spec`) and the trapdoor inverter's (`inv_spec`) are encodings
  [PS10, Definitions 41.1 (2), 56.1 (6): "an element of `D_i`", "computes `f_i^{-1}(y)`"]. -/
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w

-- derived API (Collections.lean)
theorem Collection.decD_eq_some_iff (F) {i w x} : F.decD i w = some x ↔ w = F.encD i x
theorem Collection.sample_eq_encD (F) (n) (r : F.gen.Coins n) (s : F.sample.Coins n) :
    ∃ x, F.sample.runAt n (F.index n r) s = F.encD _ x
theorem Collection.eval_of_decD (F) {i w x} (h : F.decD i w = some x) :
    F.eval (pairEncode i w) = F.f i x
theorem Collection.HardCore.evaluator {F h} (hh : F.HardCore h) :
    ∃ H, PolyTimeComputable H ∧ ∀ i w x, F.decD i w = some x → H (pairEncode i w) = [h i x]
theorem TrapdoorCollection.inv_eq_encD (T) (n) (r) (y) (s) :
    T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s = T.encD _ ((T.perm _).symm y)
/-- String-level sanity for Def 56.1 (6) (the lemma #1 and #13 ask for). -/
theorem TrapdoorCollection.eval_inv (T) (n) (r) (y) (s) :
    T.eval (pairEncode (T.index n r) (T.inv.runAt n (pairEncode (T.trap n r) (T.encD _ y)) s)) =
      T.encD _ y

-- PublicKey.lean (03d), non-breaking additions
noncomputable def Collection.HardCore.predEvaluator {F h} (hh : F.HardCore h) : F.PredEvaluator h
theorem TrapdoorCollection.OneWay.exists_glPad_singleBitSecure {T} (m) (henc) (hT : T.OneWay) :
    ∃ E : (T.glPad m henc).toCollection.PredEvaluator T.glBit,
      ((T.glPad m henc).tdpBitScheme E).SingleBitSecure
```

**A, the instance obligations** (the new field only):
- `FunFamily.toCollection` (`Collections.lean`, 03b): `((decodeFin_eq_some_iff w x).1 h).symm`.
  Move the private lemma (:406) above `toCollection`.
- `Collection.glPad` (`HardCore.lean`, 03c): by `glPadDecode_eq_some` (`HardCoreLemmas`; used,
  not changed), `F.encD_decD` and `decodeFin`. `PermCollection.glPad` and
  `TrapdoorCollection.glPad` inherit it through `{ … with }`.
- `expCollection` (`DiscreteLog.lean`, 03f1): `expEnc_of_expDec`. `dlCollection` and
  `fullDLCollection` inherit it. This needs `natToList w.length (listToNat w) = w`, a new
  additive lemma in `Arithmetic.lean` (03b).
- `factoringCollection` (`Factoring.lean`, 03f2): via `encodeDistinctPrimes_of_decode`, which
  belongs beside `decodeDistinctPrimes` in `Concrete.lean` (03f1). It could also live in
  `Factoring.lean`, to leave 03f1 untouched.
- `rsaTrapdoor` (`RSA.lean`, 03f2): `rsaEnc_of_rsaDec`, two branches. `rsaCollection` inherits it.
- `rabinCollection` and `rabinBlumTrapdoor` (`Rabin.lean`, 03f2): `rabinEnc_of_rabinDec` and
  `blumEnc_of_blumDec`.
- Goldreich–Levin for collections: `glPad_hardCore`, `goldreich_levin_coll` and the
  Perm/Trapdoor variants are unchanged. They gain the derivable evaluator.

**A, the bookkeeping.**
- DESIGN §2.10's frozen signature gains the field. Add a §5 line.
- The `Collection` docstring states it.
- `Collections.lean` is at 973 lines, and A adds about 50. Split it first, *upstream* (see #12d),
  so that no importer changes.
- Per PLAN, re-sync ch. 5–8 in the same PR:
  - prong B: drop `hcanon`. `SamplerCanonical` keeps its name as a proved lemma, so no name
    breaks. `hspec` may stay; it is now implied by the canonical spec.
  - prong C: nothing changes; `E` remains valid data.
- Pack 03b then needs a short delta re-check: the new field and the derived lemmas.

**Ripple.**
- Gate-03 packs whose files A touches:
  - 03b (`Collections.lean`, `Arithmetic.lean`);
  - 03c (`HardCore.lean`: the `glPad` field, and the :973–975 docstring);
  - 03d (`PublicKey.lean`: the optional corollary, and the `PredEvaluator` docstring);
  - 03f1 (`DiscreteLog.lean`, `Concrete.lean`);
  - 03f2 (`Factoring.lean`, `RSA.lean`, `Rabin.lean`).
- Gate-03 files that use `Collection` but do not change: 03i (`HardCoreGLColl`,
  `HardCoreLemmas`, `GoldreichLevinDomain`). They consume `Collection` but construct none, and an
  added field does not affect them.
- ch. 5–8 files that use the affected declarations:
  - `SecureComputation/ObliviousTransfer.lean` (prong B): `TrapdoorCollection`,
    `toCollection.HardCore`, and `sample_spec`/`inv_spec`/`f_perm` in `otProtocol_outV`
    (:176–181);
  - `Composability/PublicKey.lean` (prong C): `PredEvaluator` and `tdpBitScheme`.
  - Prongs A and D and S2b do not use them.

**Ruling: yes (Q1).** `Collection`, `HardCore` and `TrapdoorCollection` are on the ch. 5–8
interface list (S1 note), so their change needs the user's ruling.

---

## #2 (minor): `ofString` is "the textbook `f`" only for length-regular `f`

**Check: true.**
- `OneWay.lean:189–192` truncates and pads with `false`: `f _ x i := (f (List.ofFn x)).getD i
  false`.
- `ofString`'s own docstring (:187–188) says "exact when … `LengthRegular`". Three other places
  say it unconditionally:
  - DESIGN D5 (DESIGN.md:79–80);
  - the module docstring (OneWay.lean:28–30);
  - `FunFamily`'s docstring (:86–88).
- `false` padding identifies `y` with `y ++ [false]`, so it is not injective across lengths.
- **Context the auditor did not have.** The one in-repo use of `ofString` on a non-length-regular
  function is `fUniversal = ofString (fUniversalStr c) univOutLen` (`Universal.lean:247–248`,
  pack 03h). I checked that the lossy padding does not hurt Thm 63.1's reduction there:
  - The relevant output is `pairEncode α (true :: g(x''))`. The pairing prefix is
    self-delimiting.
  - `g` is length-regular at the fixed code `α`, and a timed-out answer differs at the first bit
    after the separator.
  - So `pad(f(x')) = pad(f(x))` forces `g(x'') = g(x)`.
  - 03h may confirm this.

**Severity: agree, minor.**

**Fix.** Docstring only. Add "(exact for length-regular `f`, `ofFn_ofString_f`; otherwise the
`false`-padding is lossy)" to D5, the module docstring and `FunFamily`'s docstring.
- The auditor's alternative, marker padding in `ofString`, is **not recommended**. It changes the
  meaning of `fUniversal` and `not_strongOneWay_id`, and would touch 03h's files.

**Ripple.**
- The docstring fix touches 03b only.
- The alternative would touch 03h (`Universal.lean`, `UniversalPadding.lean:130–139`).
- ch. 5–8: none. Prong A's `lamportOWF` is a direct `FunFamily`.

**Ruling: no.**

---

## #3 (minor): attribution

**Check: true. The auditor's † is resolved.**
- `OneWay.lean:874` reads "`[PS10, §2.12 and Theorem 79.4]`".
- The extract has §2.10 "One-way Permutations" with Def 55.1 (collection form) at ch2.raw:1477,
  §2.11 "Trapdoor Permutations" at :1527, and §2.12 "Rabin collection" at :1575.
- PS10 has no numbered single-permutation definition. Thm 79.4 ("Let `f` be a one-way
  permutation", ch3.raw:539) uses the informal single form.
- `Collections.lean:200–201` (`HardCore`, "used by Lemma 84.1, Algorithm 104.3, Theorem 126.4")
  and :24–25 (module docstring, "Lemma 84.1, Theorem 104.4 and Theorem 126.4") both list 126.4.
  The source's 126.4 proof uses "a one-way permutation with a hard-core predicate" (ch4.raw:784),
  i.e. a single OWP. The code agrees: `Commitment.lean:637, :885` uses `HardCore P.toFunFamily`.
  DESIGN §7 item 47 says the same.
- Also: the two docstrings disagree with each other ("Algorithm 104.3" against "Theorem 104.4").

**Severity: agree, minor.**

**Fix.** Docstring only.
- `OneWayPermutation`: "[PS10, §2.10, Definition 55.1, single-function form, as used in Theorems
  79.4 and 126.4]".
- Drop 126.4 from both `HardCore` lists and make them agree.

**Ripple.** 03b only. `PermFamily` and `OneWayPermutation` are used in `Commitment.lean` (03e) and
`HardCorePermutation.lean` (03i), but only their docstrings change.

**Ruling: no.**

---

## #4 (minor): two sketches describe constructions the code does not perform

**Check: true.**
- **`owfFamily_strongOneWay`.**
  - The sketch at `Collections.lean:924–935` describes:
    - padding by `blockMap`/`unaryPoly`/`pairTakePoly L`;
    - a length check "`polyTimeComputable_lenEq`, `_ite`" on `A'`'s answer.
  - The code does neither:
    - `owfFamily_easy` (:699–715) uses `polyTimeComputable_padStr L`;
    - `collInvRaw` (:722–727) drops `gen.coins(|u|)` bits, with no length check.
  - The missing check is harmless: a wrong-length answer already fails `g`'s typed experiment.
- **`weak_to_strong`.**
  - The sketch's advice is `⟨A'.advice n, ⟨1^{m n}, ⟨1^{T n}, …⟩⟩⟩` (OneWay.lean:596).
  - The implementation is `⟨A'.advice n, 1^{kk}⟩` (:641–646, "*Implementation.*").
- `policy.md:241–242`: "A sketch that describes a proof the code no longer performs is worse than
  no sketch."

**Severity: agree, minor.**

**Fix.** Rewrite both sketches to the implemented reductions. For `weak_to_strong`, fold the
"Implementation" paragraph into the sketch and remove the obsolete advice and coin layout.

**Ripple.** 03b only. `OneWayYao` (03h) is cited by name and does not change.

**Ruling: no.**

---

## #5 (note): `perm` and `f_perm` hold at every index string

**Check: true.**
- `Collections.lean:242–244`.
- With `eval_spec`, `eval ⟨i, ·⟩` permutes the finite set `encD i (D i)` at every `i`.
- The existing instances handle junk indices with a one-element domain and a canonical string:
  - `rsaDec`'s invalid branch (`RSA.lean:241`);
  - `blumDec`'s invalid branch (`Rabin.lean:692`).

**Severity: agree, note.**

**Fix.** Optional one-line docstring: "at indices outside `Gen`'s range, `D i` may be a
one-element domain".

**Ripple.** None.

**Ruling: no.**

---

## #6 (note): P3-5 is benign, and the two classes coincide

**Check: true.**
- Take `Gen'(1^n) := ⟨i, ⟨i, t⟩⟩`. Then `trap = ⟨i, t⟩`, and the formal inverter receives
  `⟨⟨i, t⟩, encD y⟩`, which is the text's `Inv((i, t), y)`.
- The trapdoor never reaches the adversary: `invProbAt` gives it `⟨i, f_i(x)⟩` only
  (`Collections.lean:188`).
- The converse direction is immediate.

**Severity: agree, note.**

**Fix.** Replace the candidate-based justification (`Collections.lean:262–267`, and DESIGN §5
entry 17) with the general argument.

**Ripple.** None. `RSA.lean:485` and `Rabin.lean:353` repeat the deviation and may keep it.

**Ruling: no.**

---

## #7 (note for 03b): the hardness predicates cannot express "enhanced" trapdoor permutations

**Check: true as stated. The consequence the auditor did not reach is serious.**
- The auditor wrote "if ch. 5–8 formalizes it … should state an enhanced-hardness predicate rather
  than cite `TrapdoorCollection.OneWay`". ch. 5–8 has formalized it and does cite it:
  `otProtocol_simulators (hT : T.OneWay) (hHC : T.toCollection.HardCore h) (hcanon :
  SamplerCanonical T)` (`ObliviousTransfer.lean:395–397`), and `otProtocol_hbcSecure` (:427).
- See "Missed" item M1 for the counterexample. The theorem cannot be proved unless trapdoor
  permutations do not exist, and `SamplerCanonical` does not help.

**Severity.**
- For 03b: agree, a note. No ch. 2–4 definition needs to change. The enhanced predicate can be
  stated in prong B.
- For gate 06B: a **blocker** on `otProtocol_simulators` and `otProtocol_hbcSecure`.

**Fix.** In prong B, not here (Q3).

**Ripple.** None in gate 03. ch. 5–8: `SecureComputation/ObliviousTransfer.lean`, and anything
built on Prop 161.5 (Yao, Thm 163.7, which is still to be stated).

**Ruling: yes, at gate 06B (Q3).**

---

## #8 (note): the parameter-`n` direct products; Claim 38.2's parameters are not registered

**Check: true. The auditor's † is resolved.**
- The source's `A` runs `A₀` "`2nm²p(n)` times" (ch2.raw:797), with threshold `1/(2m²p(n))`
  (:805).
- The code uses `T(n) + 1 = 2n·m(n)·n^c + 1` (`yaoRounds`, OneWay.lean:427) and Garg's
  threshold.
- Both choices are declared in `weak_to_strong`'s docstring (:580–583) and in the module
  docstring (:46–51).
- DESIGN §5 entry 6 (DESIGN.md:966) records `m = 2nq(n)` and the rejection-sampled position only.

**Severity: agree, note.**

**Fix.**
- Add one DESIGN §5 line: parameter-`n` adversaries for Thms 35.1 and 35.2, and Claim 38.2's
  `T` and threshold.
- The bridge lemma (`StrongOneWay` with strictly increasing `inLen` ⇒ an `ofString`-form OWF) is
  optional. Recommend deferring it.

**Ripple.** None.

**Ruling: no.**

---

## #9 (note): `WorstCaseOneWayLit`'s vacuity is wider than declared

**Check: true.**
- The counterexample is `inLen = outLen = const 1`, `f n b = b ⊕ [n odd]`.
- It is `Easy`, and it is invertible given `1^n`, so `WorstCaseOneWay` fails.
- The literal machine is activated at parameter `outLen n = 1` for every `n`, so its behaviour on
  `y` cannot depend on the parity of `n`. Hence no literal inverter exists, and the literal form
  holds.
- The declared deviation (`OneWay.lean:169–174`; DESIGN §5 entry 16) says "every
  length-shrinking family". This family does not shrink.
- **The auditor's rewording overshoots slightly.** "Satisfied vacuously by any family whose output
  length does not determine `n` (constant `outLen`)" is not true as an implication. The 1-bit
  identity (`inLen = outLen = 1`, `f n b = b`) has constant `outLen`, yet is literally invertible.

**Severity: agree, note.**

**Fix.** Docstring + DESIGN §5 entry 16: "When `outLen` is constant, so that `|f(x)|` does not
determine `n`, the literal form can hold for families that are trivially invertible given `1^n`
(e.g. the constant family, or `f n b = b ⊕ [n odd]` on one bit). `toParam` applies exactly when
`outLen` is non-constant (for `PolyExpr`, injective ⇔ non-constant)."
- The `PolyExpr` claim holds: the constructors are `const`, `var`, `add`, `mul` and `pow`
  (`PolyExpr.lean:67–72`), so the coefficients are nonnegative.

**Ripple.** None.

**Ruling: no.**

---

## #10 (note): `Permutations.lean` parameters

**Check: true.**
- The parameters are as stated: `permBits n = Nat.size n` (:432) and `permTrials n = 2·n·n`
  (:439).
- Failure is at most `n·(1 − 1/(2n))^{2n²} ≤ n·2^{−n}`.
- The docstring slip is real. "`n ≤ 2^k ≤ 2n`" is unconditional at :28, :78 and :426, while
  `two_pow_permBits_le` needs `0 < n` (:452), and `2^{size 0} = 1 > 0`.

**Severity: agree, note.**

**Fix.** Add "for `n ≥ 1`" at the three places. The auditor counts two; :426 is a third.

**Ripple.** None. `permBits` is used by the ZK files (03g, 03k), but only the docstrings change.

**Ruling: no.**

---

## #11 (note): `ArithmeticFP`

**Check: true as far as I checked.**
- I confirmed the nine fields (`Arithmetic.lean:230–249`) and the absence of an instance.
- The code cites "[PS10, p. 33 and §2.6.5]" (:217; module docstring :22, :68), not a numbered
  remark. So the auditor's † on "Remark 33.2" is not an attribution defect:
  - the source has no numbered Remark 33.2;
  - "(33.2)" is an equation in Theorem 33.5's proof (ch2.raw:541);
  - "Rem-33.2" is only an inventory label.
- I did not re-derive the degenerate-input checks (modulus 0, `b = 0`).

**Severity: agree, note.**

**Fix.** None.

**Ripple.** None.

**Ruling: no.**

---

## #12 (note → split): policy hygiene

**Check: true. One addition.**
- **(a)** The 15 `@[simp]` lemmas are exactly as listed:
  - `OneWay.lean:357, 361, 431, 435, 878`;
  - `Collections.lean:304`;
  - `Permutations.lean:135, 139`;
  - `Arithmetic.lean:88, 254, 266, 271, 276, 320, 325`.
  - `policy.md:67`: "None carries `@[simp]` unless a gate approves it."
- **(b)** The `NUPPT` lemmas live in `Collections.lean:294–315` and :574–606.
  - Prong C uses them by their `_root_` names (`Composability/PublicKey.lean:276–321`), so a move
    keeps them working if the target file is imported by `Collections.lean`.
- **(c)** `ptc_comp` (:642) and `decodeFin_eq_some_iff` (:406) are private copies.
  - Neither is in `briefs/pass-shelat-ch5-8/duplication-ledger.md`.
  - **Missed: a third copy.** A public `GGMRed.decodeFin_eq_some_iff` exists at
    `GGMReductionEval.lean:163` (pack 03j).
  - Making the `Collections.lean` copy public in `TCSlib.Cryptography` would collide with it
    inside `namespace GGMRed` (the DL-3 kind of ambiguity).
- **(d)** `Collections.lean` has 973 lines. Fix A of #1 pushes it over 1000.

**Severity.**
- (a), (b) and (d) stay **notes**.
- (c) becomes **minor**: `policy.md:124–133` requires "every instance of duplicated proved material
  must be human-approved". This needs an action (approval or removal), even though it does not
  block.

**Fix.**
- (a) Gate 03b approves the 15 lemmas in its resolution record. They are field and unfolding
  equations of this pack's own definitions. Removing them would need a replay, and could break
  `simp` calls in files of 03c, 03f1, 03f2 and 03h.
- (b), (d) One upstream split, before #1's field lands. Create `Asymptotic/CollectionsHelpers.lean`
  (or `Complexity/Randomized/RunLength.lean`, which avoids 03a's files) for:
  - `NUPPT.withIndexParam`, `length_runAt_le`, `runLenPoly` and their lemmas;
  - `splitCoins` and its three lemmas;
  - `ofFn_padFin_of_le` and `padFin_append_true_injective`.

  `Collections.lean` imports it. All names are unchanged, so no importer changes:
  `UniversalPadding.lean`, `HardCoreGLColl.lean`, `GGMReductionEval.lean` and prong A's
  `Lamport.lean` (DL-7) keep compiling.
- (c) Replace `ptc_comp` by `hg.comp hf` inline. For `decodeFin_eq_some_iff`, add a ledger entry
  (DL-9): one public copy goes into `Adversary.lean`, beside `decodeFin_ofFn` and
  `length_eq_of_decodeFin_eq_some`, in the ch. 2–4 cleanup PR, deleting both copies. That PR
  touches 03a's and 03j's files after the gate, not now.

**Ripple.** As proposed, 03b only. Removing the `@[simp]` attributes instead would touch unknown
files, pending a replay. Moving `decodeFin_eq_some_iff` now would touch 03a and 03j.

**Ruling: yes (Q2)**, for (c) by policy, and for (a) as a gate approval.

---

## #13 (note): non-vacuity coverage

**Check: true.**
- `audits/pass-shelat/Checks.lean:26–27` prints only `not_strongOneWay_id` and
  `StrongOneWay.weak`.
- No `¬ … WeakOneWay`, `¬ … WorstCaseOneWay` or `¬ Collection.OneWay` exists anywhere (grep), and
  there is no string-level TDP check.

**Severity: agree, note.**

**Fix.**
- Add `not_weakOneWay_id`, `not_worstCaseOneWay_id` and `not_toCollection_oneWay_id` (via
  `toCollection_invProbAt`), with their `#print axioms` lines.
- Under fix A of #1, also print `TrapdoorCollection.eval_inv`.

**Ripple.** 03b and the shared `Checks.lean`. The additions are additive.

**Ruling: no.**

---

## #14 (note): the canonical default pair of `factoringCollection`

**Check: true that the bundle could not show it. Checked here, and it holds.**
- `samplePairOut` (`Factoring.lean:463–467`) outputs `encodeDistinctPrimes m
  (DistinctPrimes.default hm)` on failure.
- `samplePairOut_eq_encode` (:472–477, proved) shows that every output is
  `encodeDistinctPrimes m z`.
- `factoringSampler_spec` (:549–567) uses it.
- Under fix A of #1, `factoringCollection`'s new field needs `decodeDistinctPrimes` to be
  canonical. It is (see #1). The default pair is the canonical encoding.

**Severity.** Closed; no action.

**Ripple.** None.

**Ruling: no.**

---

## What the auditor missed

- **M1. Prong B's Proposition 161.5 cannot be proved as stated** (see #7).
  - **The construction.** Let `T` be any trapdoor collection with hard-core `h` and canonical
    outputs: every ch. 2–4 candidate qualifies, or any `T` under fix A. Define `T'` to be `T` with
    `sample' (i; s) := eval ⟨i, sample (i; s)⟩`, a uniform machine by composition. Then:
    - `sample'` outputs `encD (perm u)` for `u` close to uniform. So `SampleClose`,
      `SamplerCanonical` and `sample_spec` hold.
    - `OneWay` and `HardCore h` do not involve the sampler, so they are `T`'s.
    - `hspec` concerns `H` and `decD`, which are unchanged.
  - **The attack.** Bob's view contains his random tape (`ZeroKnowledge/Interaction.lean:349–350`,
    `View.r` at :256), including the coins `s` behind `y_{1−b}`.
    - A distinguisher recomputes `w₀ = sample(i; s) = encD u` and `[h u] = H ⟨i, w₀⟩`.
    - In the real view, `z_{1−b} ⊕ h(u) = a_{1−b}`, because Alice inverts `y_{1−b} = encD (perm u)`.
    - In the simulated view, `z_{1−b}` is a fresh coin.
    - So the advantage is `1/2` at every `n` with `a_{1−b} = 1`. The same holds for any simulator,
      since its output cannot depend on `a_{1−b}`.
  - **Why the source is not affected.** The source samples `y_j ← {0,1}^n` (ch5-8.txt, Protocol
    160.4): the domain is `{0,1}^n` and the coins are the element itself. The deviation "random
    elements, not random strings" (`ObliviousTransfer.lean:37–43`) is what opens the gap.
  - Gate 06B must re-state the proposition (Q3).
- **M2. The in-layer patch `Collection.PredEvaluator`** (`PublicKey.lean:529–540`, 03d) already
  addresses #1 for Algorithm 104.3. As a consequence:
  - the "text's reading" of Thm 104.4 (:944–949) carries an `E` that cannot be derived for
    lenient `T`;
  - `TrapdoorCollection.OneWay.glPad_hardCore`'s docstring (`HardCore.lean:973–975`) overclaims
    (03c's file). It should say "…, given a predicate evaluator for the padded collection
    (derivable when decoding is canonical)", or the overclaim disappears under fix A.
- **M3. The auditor's lenient fix breaks Goldreich–Levin for collections** (see #1, "Not
  recommended").
- **M4. The infidelity is in Def 41.1 (2) and Def 56.1 (6), not (3)** (see #1). The inventory row
  Def-41.1 ("(3) is only partly faithful") should be reworded.
- **M5. `fUniversal` is the in-repo instance of #2.** The lossy padding is harmless there; 03h may
  confirm.
- **M6. A third copy of `decodeFin_eq_some_iff`** (`GGMRed`, 03j), and its namespace-collision
  constraint (#12c).
- **M7. #1's fix and #12(d) interact.** Split `Collections.lean` upstream first.
- **M8. The † items are all resolved against the extract:**
  - Claim 38.2's printed parameters (#8);
  - "Remark 33.2" (#11);
  - the §-numbers (#3).

## Pending packs: which wait, which are unaffected

The pending packs are 03d, 03f1, 03f2, 03g, 03h, 03i, 03j, 03k and 03l.

- **Must wait for the #1 resolution** (under options A or B; under C only 03d waits; under D none
  wait):
  - **03d.** `PublicKey.lean` holds the consumer: `PredEvaluator`, `tdpBitScheme` and
    `glPad_tdpBitScheme_singleBitSecure` (the E-free corollary, docstrings). It pins after F-1
    anyway.
  - **03f1.** `DiscreteLog.lean` (`expCollection`'s new field) and `Concrete.lean` (the
    `decodeDistinctPrimes` lemma, unless it is placed in `Factoring.lean`).
  - **03f2.** `Factoring.lean`, `RSA.lean` and `Rabin.lean`: the field proofs for four
    constructors.
  - Also **03c** (not pending, in triage): `HardCore.lean`'s `Collection.glPad` field and the
    :973–975 docstring. Coordinate this with 03c's own resolution, which already has a major (the
    PRG interface) and #3 on `glPad`.
- **Unaffected by 03b's fixes** under the recommended options:
  - **03g** (3-colouring ZK): no collection, `ofString` or `OneWay` use. `permBits` is touched by
    #10 in docstrings only.
  - **03h** (`OneWayLemmas`, `OneWayYao`, `Universal*`, `CollectionsLemmas`): `CollectionsLemmas`
    has no `Collection` reference. #2 is a docstring fix, and the split in #12(d) keeps names and
    imports.
    - It would be affected only if #2's marker padding were chosen.
  - **03i** (Goldreich–Levin files): they use `Collection` but construct none. Fix A's `glPad`
    proof uses `glPadDecode_eq_some` without changing it.
    - It would be affected only if the `glPad` canonicity lemma were placed in
      `HardCoreLemmas.lean`. Keep it in `HardCore.lean`.
  - **03j** (`GGMReduction*`, `PRFLemmas`, `MultiMessageLemmas`, `PublicKeyLemmas`):
    `PublicKeyLemmas` has no `Collection` reference.
    - It would be affected only if `decodeFin_eq_some_iff` were deduplicated now, rather than in
      the cleanup PR.
  - **03k** (graph-isomorphism ZK, encodings): no use.
  - **03l** (`Build/*`): no use.
- 03a (closed) would be touched only if #12(b) moved the `NUPPT` lemmas into 03a's files.
  Recommend a new file instead.

## Questions for the user

**Q1 (#1). How should the collection interface pin the strings its algorithms produce?**
1. **(Recommended) Canonical decoding.** Add the field `Collection.encD_decD : decD i w = some x →
   encD i x = w`.
   - *Cost:* one short decoder lemma per instance: `toCollection`, `glPad`, `expCollection`,
     `factoringCollection`, `rsaTrapdoor`, `rabinCollection`, `rabinBlumTrapdoor`. No existing
     proof changes and no new `sorry`. `Collections.lean` must be split first.
   - 03d, 03f1 and 03f2 wait; 03c coordinates.
   - ch. 5–8: OT drops `hcanon`, and Claim 172.a is unchanged.
   - *Gain:* `PredEvaluator`, `SamplerCanonical` and `hspec` become derivable, and "TDPs ⇒
     single-bit PKE" becomes E-free.
2. **Canonical outputs.** Restate `sample_spec` and `inv_spec` as string equalities, and weaken
   `PredEvaluator` to canonical encodings.
   - *Cost:* re-prove three instance samplers and two inverters, and restate five sorried stubs
     (03c, 03f1, 03f2). Restate `PredEvaluator` (03d). OT's `hspec` weakens. The same packs wait.
   - *Gain:* closest to the text's wording; decoders stay free.
3. **A named hypothesis `Collection.Canonical`**, carried by consumers.
   - *Cost:* the same lemmas as option 1, but no instance definition changes, so 03f1 and 03f2
     need not wait. Every consumer threads `hc`, and Thm 104.4's text reading takes `hc`.
4. **Keep the interface and document the decode-level reading as a deviation.**
   - *Cost:* docstrings only. The debt stays open: Thm 104.4's text reading keeps the
     undischargeable `E`, and each future consumer (e.g. Claim-148.b) must patch again. This needs
     your explicit acknowledgment for the major to close.

**Q2 (#12). Undisclosed copies and `@[simp]`.**
1. **(Recommended)** Inline `ptc_comp` now. Record `decodeFin_eq_some_iff` (copies in
   `Collections.lean` and `GGMReductionEval.lean`) as ledger DL-9, paid back in the ch. 2–4
   cleanup PR with one public copy in `Adversary.lean`. Gate 03b approves the 15 `@[simp]` lemmas.
   - *Cost:* a ledger line and a one-line edit; no replay risk.
2. Deduplicate both now, and also drop the 15 `@[simp]` attributes.
   - *Cost:* touches 03a's and 03j's files during the gate, and needs a replay. Proofs elsewhere
     may break.
3. Accept both copies as ledger debt, and approve the attributes.
   - *Cost:* a second ledger line for a trivial copy.

**Q3 (#7 / M1; for gate 06B, prong B). Proposition 161.5 cannot be proved as stated. How should it
be re-stated?**
1. **(Recommended) Add an enhanced hard-core hypothesis**, stated in prong B and declared as a
   deviation (Goldreich, *Foundations* vol. 2, App. C.1): `h(f⁻¹(Sample(i; s)))` is unpredictable
   from `⟨i, s⟩`.

   ```lean
   def EnhancedHardCore (T : TrapdoorCollection) (h : ∀ i, T.D i → Bool) : Prop :=
     ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n,
       uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n × A.Coins n =>
         A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
           h _ ((T.perm _).symm ((T.decD _ (T.sample.runAt n (T.index n r) z.1)).getD default)))
         ≤ 1 / 2 + ε n
   ```

   - *Cost:* a statement change in ch. 5–8 only. No candidate is proved enhanced.
2. **Restrict to samplers that return their coins** (domain `{0,1}^ℓ`, the source's
   `y ← {0,1}^n`).
   - *Cost:* RSA and Rabin no longer instantiate Prop 161.5; this is literal to the source.
3. **Put the enhanced predicate in the ch. 2–4 layer** (`Collections.lean`) as new interface.
   - *Cost:* reopens 03b's scope, and needs a new delta audit.
