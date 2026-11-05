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
