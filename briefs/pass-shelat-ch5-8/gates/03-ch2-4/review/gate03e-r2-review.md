# Gate 03e, round 2 (closing round): review of the external auditor's findings

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03e-r2-findings.md`: 0 blockers, 2 majors (#1, #2), 5 minors (#3–#7), plus 27 resolution-row verdicts.
- **Pack:** `03e-pack-r2.md`, with `resolutions-03e-r1.md`, `evidence-r2/03e/repair.diff.txt` and `evidence/e2/`.
- **Code at the pin:** worktree `scratchpad/wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2`. Its Lean files equal those of the audited pin `e79397ea` (`git diff 0c348ff9 e79397ea -- TCSlib` is empty). Lean line numbers below refer to it; Lean paths are under `TCSlib/Cryptography/ZeroKnowledge/` unless qualified.
- **Records:** read at the pin `e79397ea` (what the auditor saw) and at the branch head `ee6a8d02`.
  - The five audited Lean files, `Asymptotic/Sampling.lean`, `policy.md` and `resolutions-03e-r1.md` are unchanged from the pin to the head.
  - #203 (clean-up part 1) changed only `ThreeColoring/Machines.lean` in `ZeroKnowledge/`, and DESIGN §2.4/§2.6. **No finding is affected by #203.**
  - #205 (03a round 2, docstrings in `PPT.lean`, `Adversary.lean`, `Ensembles.lean`) does not affect any finding either.
  - DESIGN lines shifted after the pin. D8 is at 136 (pin) / 137 (head); §5 item 8 at 1009 / 1045; §5 item 11 at 1019 / 1055; §7 item 51 at 1254 / 1292. The text of those items is unchanged.
- **Downstream code read:** prong C `scratchpad/wt-prong-c` at `9e6f08bb` (`Composability/SequentialZK.lean`).
- **Source:** `blueprint/src/references/pass-shelat-2010-ch4.raw.md` (pp. 116–117, 119, 121–122), checked against the auditor's quotations.
- **Not done:** no Lean was built or run (`CLAUDE.md` forbids `lean`, and no probe was essential). The `Iff.rfl`/`rfl` lemmas below are definitional. The two case lemmas in §2 are uncompiled sketches.

## Summary

- **Verdicts: 6 true (#1, #2, #4, #5, #6, #7), 1 partly true (#3), 0 false.**
  - #3 is partly true. The contradiction inside `resolutions-03e-r1.md` (rows 5 and M8) is real. But the records the auditor could not see are all present at the pin, so the defect is stale resolution text, not missing record fixes. They are: the run-3 erratum, `SPINE-DESIGN.md`'s "Two limits", and the `inventory-ch5-8.md` Thm-175.1 row.
  - #5 and #7 are **understated** (§2, M3, M4).
- **No new theorem statement is false.** I agree with the auditor here. #4's two conclusions are weaker than their docstrings say, but they are provable and true as stated.
- **Severity: no change.** 2 majors, 5 minors.
  - **#1 stays major, narrowly.** No Lean statement or ch. 5–8 record depends on the error. But DESIGN §5 is the "Deviations register (docstring text, one line each)": its lines are meant to be copied into docstrings. Its item 11 and the frozen D8 both claim statistical ZK for 3COL, which is false here, not merely unproved. The record was also the declared object of a repair (M5).
  - **#2 stays major, because of `ProverBounded` alone.** The precedent is gate 04's F02 (major): a published definition that crosses into ch. 5–8 and is read through its body by consumers in other files. `Protocol.ProverBounded` is both.
    - It is the hypothesis of prong C's `ZK.seqRep`, `StatZK.seqRep`, … (`SequentialZK.lean:376–411`). Gate 06 integration deletes prong C's local copy in favour of this one.
    - Four ch. 2–4 files read it by definitional unfolding at 11 sites (M1).
    - `attempt` and `retry` alone would be **minor**, by gate 03l's precedent (Minor 3: readers in the same file, no ch. 5–8 reader). Prong C reaches `PerfectZKAbort` through `PerfectZKAbort.statZK`, not through these.
- **Fixes, in order of importance:**
  1. **#2:** add `Protocol.proverBounded_iff` (Interaction.lean, after :332), `AbortRetry.attempt_eq` (Defs.lean, after :308) and `AbortRetry.retry_eq` (after :318). Two optional case lemmas for `retry` are also given (§2).
     - Re-point the 11 consumer sites (M1) to `proverBounded_iff`.
     - Run a rule-10 seal (`attribute [local irreducible] TCSlib.Cryptography.Protocol.ProverBounded`) on the four consumer files, with controls.
     - Add prints for the new lemmas to `Checks.lean`. None of the new lemmas gets `@[simp]`.
  2. **#1:** add a dated erratum under D8 (the design is frozen) and rewrite DESIGN §5 item 11. GI is `StatZK` with negligible δ; 3COL is computational `ZK`.
  3. **#4 (ruling R-03e-r2-1):** add `LevinReduction L L3COL R R3COL f w p` to the conclusions of `zk_proof_of_witnessRelation` and `_of_owp`.
  4. **#7, #6, #5:** docstring and record corrections.
     - #7: `InteractiveProofs.lean:35–48, 113–118`, DESIGN §5 item 8.
     - #6: `Defs.lean:42–48`, DESIGN §7 item 51.
     - #5: `Interaction.lean:39–43`, plus the two `…Rep` docstrings in packs 03k and 03g.
  5. **#3:** delete the stale sentences in `resolutions-03e-r1.md` row 5 and M8. State the current counts: 21 `sorry` warnings in the 126-module closure, 18 outside the ZK files (17 `main`'s, 1 `NonUniform`).
  6. **For clean-up part 2, not for closure:** the tactic-level unfolds in the repair's new proofs (M2).
- **Rulings needed: one.**
  - **R-03e-r2-1 (#4)** changes two theorem statements (§5).
  - One more is conditional. If #2's lemmas are deferred to clean-up part 2 instead of landing before closure, that accepts debt on a ch. 5–8 interface and needs a ruling (R-03e-r2-2, §5). I recommend not deferring them.
  - Everything else is the maintainer's: records, docstrings, policy-mandated lemmas.
- **Overlap with clean-up part 2** (`briefs/pass-shelat-ch5-8/fills/cleanup-part2/brief-draft.md`): **none for the findings themselves.**
  - Part 2's items A–F and J do not mention `ProverBounded`, `attempt`, `retry` or `firstHit`.
  - Item J is gate 04 round 4's seal exclusions. Gate 04's ch. 2–4 seal set includes `ZeroKnowledge/Interaction.lean`'s **own** proofs (for example `pairFstD_encodeMsgs`). It does not include the consumers of `ProverBounded`, which are in `InteractiveProofs.lean`, `NP.lean`, `GraphIsomorphism.lean` and `ThreeColoring/Protocol.lean`.
  - There are only two contacts:
    - **Item C.** It adds `NUPPT.coinLen_eq`, `advInput_eq` and `runAtL_eq` and re-points only `Closure.lean`'s sites. Its re-point list should add `Defs.lean:291, :543` (new in this repair) and `InteractiveProofs.lean:449, :462` (M2).
    - **DL-13** deletes `negligible_const_zero` from `Defs.lean`, the file that gains `attempt_eq`/`retry_eq`. Expect a trivial file-level merge if both are in flight.
  - Recommendation: land #2 in the 03e closing repair now. Do not wait for part 2, which is issued only after gate 04 closes and #195 merges.

---

## 1. Major #1: the design record calls 3COL statistically zero-knowledge

### Verdict: **true**. Severity: **major (agree, narrowly)**.

**Evidence at the pin.**
- DESIGN D8, lines 135–137: "… `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated simulators, rejection-sampled permutations)."
- §5 item 11, line 1019: "GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges / colour permutations); …". The round 1 records fix (`e79397ea`) rewrote only the item's tail.
- The code says otherwise:
  - `col_zk : ZK (colProtocol Com ℓ) R3COL` (`ThreeColoring/Simulator.lean:764`, `sorry`). Its sketch (:735–763) uses `hC.multiHiding`, a computational step.
  - Only `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (`GraphIsomorphismZK.lean:561`) is statistical. It prints standard axioms (`evidence-repairs/03ac/checks-axioms.log`).
- The other records are right:
  - `inventory-ch4.md:207` says "ZK of the 3COL simulator (computational)".
  - The round 1 review (§2.1, "03g is unaffected, since 3-colouring is computational") says the same.
  - Prong C cites `ZK.seqRep` for 3COL.
  - A grep of `briefs/` and `TCSlib/Cryptography` finds the false claim only at DESIGN lines 136 and 1019.

**Counterexample: rebuilt and confirmed against the Lean definitions.**
- `Commitment.binding` (`Commitment.lean:115–117`) holds for all `n`, all `v₀ ≠ v₁` of length `n` and all `r₀, r₁` of length `ℓ(n)`.
- `colProver` (`ThreeColoring/Protocol.lean:408–424`) commits, for each vertex `i`, to `padColor n (π (c i))` with an `ℓ(n)`-bit block `rr i`, via `colCommit` = `multiCom`.
- Take `G_m`: `m ≥ 3` vertices and the sole edge {0, 1}. Take the colourings:
  - `c₀ = (0, 1, 0, 0, …)`;
  - `c₁ = (0, 1, 2, 0, …)`.

  Both are proper, so both are `R3COL` witnesses for `x_m = encGraph G_m` (`Language.lean:115`).
- Let `T` be the (inefficient) test on the encoded honest-verifier view: "some `v` of length `n`, and some `r, r'` of length `ℓ(n)`, satisfy `Com⟨v, r⟩ = msgAt com 0` and `Com⟨v, r'⟩ = msgAt com 2`".
  - Under `c₀`, `T` holds always: take `v = pad(π 0)` with the real blocks.
  - Under `c₁`, `T` never holds. Binding forces `v = pad(π(c₁ 0))` and `v = pad(π(c₁ 2))`. Since `π` and `padColor` are injective, that gives `c₁ 0 = c₁ 2`, a contradiction.
  - Colour permutations preserve both facts.
- A simulator gets only `(x_m, z)`, so its value `q` on `T` is the same for both witnesses. Hence `δ(m²) ≥ max(1 − q, q) ≥ 1/2` for all `m ≥ 3`, and `δ` is not negligible.
- So `StatZK (colProtocol Com ℓ) R3COL δ` with negligible `δ` is **false** for every `Commitment`, not just unproved.

**Why major and not minor.**
- §5's heading says its lines are docstring text, so a worker copying item 11 would write a false docstring.
- D8 is a frozen foundation decision that ch. 5–8 planners read. Under it, a ch. 7 plan would reach for `StatZK.seqRep` on 3COL (error `Q·δ`), which cannot exist.
- No Lean statement depends on it, so it is not a blocker.

**On the auditor's row verdicts.** Rows 2 and M5 fixed what they targeted: the phrase "`PerfectZKAbort` stated as the perfect form" is gone. The 3COL clause is a separate error that predates them. Round 1's auditor and review both missed it, and it sits in the same sentence. "Not resolved" for rows 2/M5 is defensible only under the pack's "the fix introduces no new one". The work is the same either way.

**Fix** (records only; no ruling).
- **D8: an erratum, not an edit**, following the "as-built erratum; the frozen text above is unchanged" precedent of §2.6. Insert after line 140 (pin) / 141 (head):

  > **Erratum (2026-11-06, gate 03e round 2, finding 1; the frozen text above is unchanged).** Only GI is proved statistically (`gi_statZK`: `StatZK` with negligible δ, truncated simulator, rejection-sampled permutations). 3COL is proved computationally ZK (`col_zk`, by `Commitment.multiHiding`; the truncation and sampling errors are statistical terms inside a computational bound). It cannot be statistical: a perfectly binding commitment makes the real views of two colourings outside one colour-permutation orbit statistically far apart, and the simulator does not see the witness.

- **§5 item 11** (line 1019 pin / 1055 head), replacing the whole item:

  > 11. GI: statistical ZK with negligible δ (`gi_statZK`; truncated simulator, rejection-sampled permutations). 3COL: computational ZK (`col_zk`; `Commitment.multiHiding`, with the statistical errors of the truncated simulator and of the rejection-sampled edges and colour permutations absorbed); not statistical, since with a perfectly binding commitment two inequivalent colourings give statistically distinct views (gate 03e round 2, finding 1). One-iteration ZK; the `n`-fold protocols get soundness only (sequential composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no source protocol attains them under D8/D10; `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}` (gate 03e, finding 2; ruling G3-4).

- **Resolutions.** Record the correction in the round 2 resolutions (`resolutions-03e-r2.md`, rows #1 and r1-2/r1-M5). Do not rewrite round 1's rows; at most add "(3COL clause corrected in round 2, finding 1)" to rows 2 and M5.

**Ripple.**
- None in Lean, `Checks.lean`, or packs 03g/03k: `col_zk`'s docstring is already accurate.
- Ch. 5–8: none. Prong C and gate 06's to-do (`gates/06-ch5-8-statements/PLAN.md:55–59`) already treat 3COL as computational.

---

## 2. Major #2: the three new definitions lack their reading lemmas

### Verdict: **true, and understated** (M1). Severity: **major (agree; driven by `ProverBounded`)**.

**Policy.** `policy.md` §1, "Definitions land with their lemmas" (user, 2026-10-16), lines 55–71. Every new public `def` lands in the same PR, beside the definition, with:
- for a predicate, an `_iff` characterization;
- for any other definition, `<name>_eq` (by `rfl` where that holds) or case lemmas covering every input;
- no `@[simp]` without gate approval;
- each docstring stating its formula.

Also, "Consumers never unfold another file's definition."

**Confirmed at the pin.**
- The repair adds exactly three public definitions (grep of section A's added lines): `ProverBounded` (`Interaction.lean:331`), `AbortRetry.attempt` (`Defs.lean:305`) and `AbortRetry.retry` (`Defs.lean:314`).
- None has an `_iff`, an `_eq` or covering case lemmas.
- `ProverBounded.mono/.exists_complete/.pullback`, `attempt_poly`, `retry_poly`, `exists_retrySimulator` and `firstHit_map_getD_eq` do not characterize them, as the auditor says.
- The lint attestation cannot detect this. `style_lint.py` checks presence only, and `campaign_style_lint.py`'s check 8 accepts any lemma whose name contains the definition's name, so `ProverBounded.mono` and `attempt_poly` count as coverage. Gate 03l's review (§3) made the same point.
- No waiver or schedule covers it: I searched `duplication-ledger.md`, `QUEUE.md`, the decision log and the clean-up part 2 draft.

**Missed: consumers already read `ProverBounded` through its body (M1).** These 11 sites in 4 files outside `Interaction.lean` elaborate a `fun` or an application against the `def`, which is a definitional closure that a rule-10 seal would reject:

| File (pack) | Line | How |
|---|---|---|
| `InteractiveProofs.lean` (03e) | 236 | `hB x y r hist hy` (in `ProverBounded.exists_complete`) |
| `InteractiveProofs.lean` (03e) | 468–469 | `fun x y _ _ hxy => hp x y hxy` (`npProtocol_proverBounded`) |
| `NP.lean` (03e) | 278–280 | `intro x y r hist hxy` on the goal, `hB (f x) (w x y) r hist _` |
| `GraphIsomorphism.lean` (03k) | 927, 931, 937, 938 | `fun x y r hist _ => …` |
| `ThreeColoring/Protocol.lean` (03g) | 609 (×2), 616–617 | `fun x y r hist _ => …`, then `show ((colProverRep …).next …).length ≤ …` |
| `ThreeColoring/Protocol.lean` (03g) | 881 | `hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩` |

`ProverBounded.mono` (`Interaction.lean:335–337`) is in the same file and may stay as is. Prong C's `ZK.seqRep` fills will read it too, after gate 06 deletes its local copy (`SequentialZK.lean:346`).

**Lemmas to add.** All of them carry no `@[simp]`, and each docstring states its formula.

`Interaction.lean`, inside `namespace Protocol`, directly after the definition (after line 332):

```lean
/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
    π.ProverBounded R B ↔
      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
  Iff.rfl
```

(The explicit arguments follow the campaign's `hardCore_iff`, `PRG.easy_iff`.)

`Defs.lean`, inside `namespace AbortRetry` (`open EncodingMachines …` is in force), directly after `attempt` (after line 308):

```lean
/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
`inParam w`, argument `inArg w`, empty advice and coins
`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
        (S.coinLen (NUPPT.inParam w).length))) :=
  rfl
```

Directly after `retry` (after line 318):

```lean
/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
attempt `i` if `i < N`, and `[]` otherwise. -/
theorem retry_eq (S : NUPPT) (w : List Bool) :
    retry S w =
      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
          (NUPPT.inParam w).length then
        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
      else [] :=
  rfl
```

Optional, but they are the semantic form the auditor asked for ("exhaustive retry cases"). Together they cover every input. Uncompiled sketch:

```lean
/-- If attempt `i < |inParam w|` is the first that does not abort, `retry S w` is attempt `i`. -/
theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
  rw [retry_eq, h, if_pos hi]

/-- If all `|inParam w|` attempts abort, `retry S w = []`. -/
theorem retry_eq_nil {S : NUPPT} {w : List Bool}
    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
      (NUPPT.inParam w).length :=
    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
  rw [retry_eq, h', if_neg (lt_irrefl _)]
```

(`firstIdx_eq_of`, `firstIdx_eq_of_forall`: `EncodingMachines.lean:255, 263`.) The in-file reads `simp only [attempt, …]` (:569) and `simp only [retry, …]` (:370, :581) are allowed, since they are in the same file. They may switch to these lemmas.

**Not recommended: making `attempt`/`retry` private.** It would remove the obligation, but `attempt_poly`, `retry_poly` and `exists_retrySimulator` mention them, the module docstring lists them as main definitions, and `Checks.lean:441` prints `exists_retrySimulator`. That is an interface change for no gain over two `rfl` lemmas.

**Re-pointing** (the maintainer's job; no ruling):
- `InteractiveProofs.lean:236` → `(π.proverBounded_iff R B).1 hB x y r hist hy`.
- `:468–469` → `((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy`. `npProtocol` is the same file's definition.
- `NP.lean:278` → `rw [Protocol.proverBounded_iff] at hB ⊢` before the `intro`.
- `GraphIsomorphism.lean:927, 931, 937–938` and `ThreeColoring/Protocol.lean:609, 616` → `(Protocol.proverBounded_iff _ _ _).2 fun …`. The `show` at :617 becomes unnecessary.
- `ThreeColoring/Protocol.lean:881` → `(Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨…⟩`.
- Then run the rule-10 seal on the four files with `attribute [local irreducible] TCSlib.Cryptography.Protocol.ProverBounded`, with a control on the base text that must fail. This is the clean-up part 1 / gate 04 round 4 procedure.

**Evidence to add.** In `audits/pass-shelat/Checks.lean`, beside :425–427 and :440–441, add `#print axioms` for `Protocol.proverBounded_iff`, `AbortRetry.attempt_eq`, `AbortRetry.retry_eq` (and `retry_eq_attempt`, `retry_eq_nil` if added). Replay the modules downstream of the four touched files; the `sorry` counts must equal the base's.

**Ripple.**
- 03e: `Interaction.lean`, `Defs.lean`, `InteractiveProofs.lean`, `NP.lean`.
- 03k: `GraphIsomorphism.lean`. 03g: `ThreeColoring/Protocol.lean`. These are proof-only re-points; their statements are unchanged.
- `Checks.lean`.
- Prong C: add to gate 06's to-do (`PLAN.md:55–59`): "read `ProverBounded` through `Protocol.proverBounded_iff`".

---

## 3. Minors

| # | Verdict | Severity | Concrete fix | Ripple |
|---|---|---|---|---|
| 3 | **Partly true.** Two parts hold. (i) Row 5 says "**Fixed (records)**", then keeps the stale drafting sentence "The drafter found them missing: … still names `TuringMachine/Build/*` …". M8 says "#5 (c)'s record correction, which is not done". (ii) The counts: `evidence/e/replay.log` (round 1, 358 modules) has 25 warnings, 22 of them outside the ZK files (21 `main`'s including RecordTable's 4, plus 1 `NonUniform`). `evidence/e2/replay.log` (126 modules) has 21, 18 of them outside the ZK files (17 + 1). But the records the auditor calls "absent" **exist at the pin**, all committed in `dd492eac`: the erratum at `audits/pass-shelat/run3-audit-summary.md:17`, `SPINE-DESIGN.md:42–55` ("Two limits of the interaction model D8"), and `inventory-ch5-8.md:130` (the Thm-175.1 row). So #5(c) is done; only the resolution text is wrong. | minor (agree) | In `resolutions-03e-r1.md` row 5, delete from "The drafter found them missing" to the end of the cell, and add "(committed in `dd492eac`; the 22 are round 1's 358-module closure)". In row M8, replace "except #5 (c)'s record correction, which is not done (see #5)" with "#5 (c)'s record correction is done (`run3-audit-summary.md:17`, `dd492eac`)". In `resolutions-03e-r2.md`, state the current figures: 21 `sorry` warnings in the 126-module closure; 18 outside the ZK files (17 `main`'s, 1 `NonUniform`); 3 in 3-colouring. | records only |
| 4 | **True.** `zk_proof_of_witnessRelation` (`NP.lean:679–689`) and `_of_owp` (:698–709) return `f, w, p` with only `∀ N, N ≤ p.eval N` and the protocol facts. Their docstrings (:670–677, :691–696) say "there is a Levin reduction `(f, w)` … with length polynomial `p ≥ id`". The proof has `h : LevinReduction …` in hand (:688) and drops it. The statements are true and provable as stated, just weaker than described. The supplied-reduction forms (:584, :634) are fine. | minor (agree) | **Ruling R-03e-r2-1 (§5); recommended (A).** At :683 insert `LevinReduction L L3COL R R3COL f w p ∧` before `(∀ N, N ≤ p.eval N) ∧`. The proof at :689 becomes `exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩`. Insert the same conjunct at :703 (`_of_owp`; its proof at :709 is unchanged). Adjust `zk_proof_of_mem_NP`'s pattern at :737 to `obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := …`. `zk_proof_of_mem_NP_of_owp` (:751) is unchanged. | 03e only (no consumer outside `NP.lean`; ch. 5–8 does not cite Thm 124.1). 03g's Thm-124.1 inventory row notes the stronger form. Prints keep their names and still reach `sorryAx` (`col_zk`, `colRep_efficientProverProof`). |
| 5 | **True, and understated** (M3). `giProtocolRep` (`GraphIsomorphism.lean:556–560`, `rounds = 4·var`, prover first) and `colProtocolRep` (`ThreeColoring/Protocol.lean:500–504`, `4·var·var`) make the verifier the last mover. Their verifiers return the verdict on the complete history (`GraphIsomorphism.lean:546–551`, `ThreeColoring/Protocol.lean:493–496`). So the last "fourth move" is the verdict (`outV_eq_getLast_of_moverIsV`), and it is nonempty on accepting runs. The sentence also contradicts the verdict-convention sentence just above it (`Interaction.lean:35–37`: "the `n`-fold protocols read the verifier's last message as the verdict"). **Missed:** prong C does **not** follow "one dummy verifier message per iteration". `SequentialZK.lean:21–33` pads each phase with `k = rounds(|x|)` filler moves of both parties, the last filler carrying the verdict. | minor (agree) | Replace `Interaction.lean:39–43` with: "Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover, verifier, prover) is repeated under strict alternation by giving each iteration one additional verifier move, so that every iteration starts with the prover. In `giProtocolRep` and `colProtocolRep` that move is the empty message, except for the protocol's final move, which carries the verifier's verdict (the verdict convention above). The sequential repetition of [PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(\|x\|)` filler moves of both parties, its last filler again carrying the verdict." Same qualifier at `GraphIsomorphism.lean:554–555` (03k: "and an empty verifier message" → "and a verifier message, empty except for the final verdict") and at `ThreeColoring/Protocol.lean:497–498` (03g). | 03e docstring; 03k and 03g docstrings; prong C none (its own text is accurate) |
| 6 | **True.** `Defs.lean:42–48` and DESIGN §7 item 51 (pin :1254–1259) claim that the literal reading fails "for every protocol whose hiding is only computational". The auditor's fixed-value commitment protocol refutes the universal claim: its view is simulable exactly, for any `z`. For 3COL the claim holds, but only through the witness-separation argument of #1. Opening commitments alone is not a distinguisher; separating two witnesses is. That argument covers the source's own Prop 128.8, so a narrowed item 51 is still a genuine §7 source gap. | minor (agree) | Replace `Defs.lean:42–48` with: "The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e, note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the encoded view, which contains `z`. With `\|z\|` exponential in `ℓ(n)` it can open the perfectly binding commitments by exhaustive search. On a graph with two proper colourings outside one colour-permutation orbit, that tells the two real views apart with advantage 1, while the simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every `z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol. Protocols with exactly simulable views are not affected. For the same reason the distinguisher's advice is indexed by the parameter `\|x\|`, not by its input length." DESIGN §7 item 51 (pin :1254 / head :1292): replace "fails for every protocol whose hiding is only computational: … open the unopened commitments" with "fails for the 3-colouring protocol 127.5 of Proposition 128.8: with `\|z\|` exponential, the distinguisher, whose input (the view) contains `z`, opens the perfectly binding commitments by exhaustive search, and on a graph with two proper colourings outside one colour-permutation orbit it separates the two real views, which the witness-blind simulator cannot match". Keep the last sentence, adding "round 2, finding 6". | 03e docstring; DESIGN |
| 7 | **True, slightly understated** (M4). (a) With `s = 1`, the zero-message protocol whose verifier always outputs `[true]` and whose prover sends `[]` satisfies `InteractiveProofErr π L (fun _ => 1)` and `EfficientProverProofErr π L R (fun _ => 1)` for every `L` and `R`. I checked each field: the bound is 0, soundness is `0 ≤ uprob`, both parties are `NUPPT.ofPolyTimeUniform` of constants. So `InteractiveProofs.lean:46–47` ("So the proof systems hold only for languages of the text's class IP") is false for the explicit-error forms. The capping argument is sound for `InteractiveProof`. (b) Source p. 117: "the prover in the definition of an interactive proof need not be efficient". Only Def 119.5 (p. 119) has "P is p.p.t.". The same attribution appears in `InteractiveProofs.lean:113–114` (the auditor's :114), in the module text :35–38 ("The parties' efficiency (the text's "p.p.t.")"), and in DESIGN §5 item 8 (pin :1012–1013). `EfficientProverProof`'s docstring (:335–339) is correct. | minor (agree) | `InteractiveProofs.lean:35–36`: "The parties' efficiency (the text's "p.p.t.")" → "The verifier's efficiency (Definition 116.1's "p.p.t.", and the prover's for Definition 119.5)". `:46–48`: "So the proof systems hold only for …" → "So `InteractiveProof` (and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`) holds only for …"; then add after "… excluded —": "the explicit-error forms with a large error say little (with `s = 1` the zero-message, always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —". `:113–114`: "(the text's p.p.t. prover writes at most `t(\|x\|)` bits; the convention of ch. 6)" → "(Definition 116.1's prover need not be efficient; bounding its messages is the chosen normal form, harmless because a verifier of time `t(\|x\|)` reads at most `t(\|x\|)` bits of each message; the convention of ch. 6)". DESIGN §5 item 8: ": the source's p.p.t. prover writes at most `t(\|x\|)` bits" → ": for Definition 119.5 the source's p.p.t. prover writes at most `t(\|x\|)` bits; for Definition 116.1, whose prover is unbounded, it is a normal form (the verifier reads at most `t(\|x\|)` bits of each message)". | 03e docstrings; DESIGN |

### The round 1 rows (auditor's verdicts)

I agree with every row verdict except these:
- **Row 5 and M8:** *fixed* (the records are at the pin), with stale resolution text (#3 above). The auditor said *not resolved*.
- **Row 15:** *fixed*. `SPINE-DESIGN.md:42–55` at the pin holds exactly the two limits. The auditor said *recorded* because the file was not in the bundle.
- **Rows 2 and M5:** their own defect is fixed. #1 is a pre-existing error in the same item, which I accept as the reason for *not resolved* (§1).

Rows 1, 3, 8 and 9 are rightly *not resolved*: the repair introduced #2/#7, #4, #5 and #6 respectively.

---

## 4. Missed by the auditor

- **M1. `ProverBounded` is already read through its body** at 11 sites in 4 files (table in §2). This is the policy breach that `proverBounded_iff` must repair, and it is what makes #2 a major under gate 04's F02 precedent. It needs a seal, not only the lemma.
- **M2. Tactic-level unfolds in the repair's new proofs** (`Defs.lean`). These are out of the auditor's scope (tactic proofs) but against `policy.md` §1. All four are minor; recommended for clean-up part 2, not for closure.
  - `:409`, `firstHit_map_getD_eq`: `unfold firstHit`. `firstHit` is defined in `Asymptotic/Sampling.lean:451` (pack 03a, written 2026-10-28, after the rule) and has no `_eq` lemma. Add `firstHit_eq : firstHit E xs = (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none := rfl` beside it, and rewrite with it.
  - `:543`, `PerfectZKAbort.statZK`: `simp only [NUPPT.coinLen, …]`. Use item C's `NUPPT.coinLen_eq`.
  - `:291`, `perfectZK_zeroRounds`: `simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]`. Use item C's `advInput_eq` with `inArg_layout`/`inCoins_layout`.
  - `:563`: `simp [finProdFinEquiv]`, a Mathlib definition passed to `simp`. Use its `simps` lemmas instead (`finProdFinEquiv_apply_val`, `finProdFinEquiv_symm_apply`).

  The older `InteractiveProofs.lean:449, :462` (`simp [… NUPPT.advInput …]`) belong in the same item C list. A rule-10 seal does not catch `unfold`/`simp [def]`, so these need the syntactic scan of clean-up part 1 (`users.py`).
- **M3. #5 is broader.** The new sentence contradicts the verdict convention two lines above it, and its claim about ch. 7's fillers is false: prong C pads `k` moves of both parties per phase.
- **M4. #7 is broader.** The Def 116.1 / Def 119.5 misattribution is also in the module text (`InteractiveProofs.lean:35–38`), not only at :114.
- **M5. #3 is narrower.** The run-3 erratum, the SPINE-DESIGN limits and the inventory row are all at the pin. The bundle simply omitted them.

---

## 5. Rulings for the user (multiple choice; recommended option first)

**R-03e-r2-1. The witness-relation forms of Thm 124.1 drop their Levin reduction (#4).** `zk_proof_of_witnessRelation` and `_of_owp` say "there is a Levin reduction `(f, w)`", but they return only the maps and `p ≥ id`.
1. **Export the certificate (recommended).** Add `LevinReduction L L3COL R R3COL f w p ∧` to both conclusions (§3, #4).
   - *Cost:* two statement lines, one proof term, one destructuring pattern in `zk_proof_of_mem_NP`. No consumer outside `NP.lean`; the print names are unchanged.
   - *Benefit:* a consumer can pull further protocols back along the same maps and use `length_eq` and `witness`.
2. **Narrow the two docstrings** to "there are maps `f, w` and a polynomial `p ≥ id` (from the Levin reduction supplied by `h3`, not recorded)".
   - *Cost:* docstrings only. The returned maps cannot be reused as a reduction.

**R-03e-r2-2 (conditional: only if #2's lemmas are not landed before closure).**
1. **Land `proverBounded_iff`, `attempt_eq` and `retry_eq` and the 11 re-points in the 03e closing repair (recommended; then no ruling is needed).**
   - *Cost:* about 30 lines, a seal of four files, prints, a downstream replay.
2. **Close 03e with them scheduled in clean-up part 2** (as a new item beside C and J).
   - *Cost:* accepts a policy-§1 debt on a ch. 5–8 interface until part 2 lands, after gate 04 and #195. Gate 06's prong C re-sync must then wait for part 2, or read the definition through its body.

---

## 6. Ripple map

| Change | ch. 2–4 files (pack) | ch. 5–8 | `Checks.lean` |
|---|---|---|---|
| #1 | DESIGN D8 erratum, §5 item 11; `resolutions-03e-r2.md` | none | none |
| #2 | `Interaction.lean`, `Defs.lean`, `InteractiveProofs.lean`, `NP.lean` (03e); `GraphIsomorphism.lean` (03k); `ThreeColoring/Protocol.lean` (03g), proof-only | prong C reads via `proverBounded_iff` at gate 06 (`PLAN.md:55–59` to-do line) | prints for 3–5 new lemmas |
| #3 | `resolutions-03e-r1.md` rows 5, M8; `resolutions-03e-r2.md` | none | none |
| #4 | `NP.lean:679–709, 737` (03e); 03g's Thm-124.1 inventory note | none | names unchanged |
| #5 | `Interaction.lean:39–43` (03e); `GraphIsomorphism.lean:554–555` (03k); `ThreeColoring/Protocol.lean:497–498` (03g) | none | none |
| #6 | `Defs.lean:42–48`; DESIGN §7 item 51 | none | none |
| #7 | `InteractiveProofs.lean:35–48, 113–118`; DESIGN §5 item 8 | none | none |
| M2 | `Defs.lean:291, 409, 543, 563`; `InteractiveProofs.lean:449, 462`; `Sampling.lean` (03a, `firstHit_eq`) | none | print for `firstHit_eq` |

Pending packs: only 03g and 03k get changes (proof re-points and docstrings), and none of their statements change. 03a gets `firstHit_eq` only if M2 is taken up (part 2).

---

## 7. Proposed closing condition for gate 03e

The gate closes, without an external round 3, when a maintainer delta check at the closing repair's head confirms all of the following:

1. **#2:**
   - `Protocol.proverBounded_iff`, `AbortRetry.attempt_eq` and `AbortRetry.retry_eq` are present beside their definitions, unattributed, with formula docstrings (optionally also `retry_eq_attempt`, `retry_eq_nil`).
   - The 11 sites of M1 are re-pointed.
   - A rule-10 seal of `InteractiveProofs.lean`, `NP.lean`, `GraphIsomorphism.lean` and `ThreeColoring/Protocol.lean` on `Protocol.ProverBounded` passes, with failing controls.
   - The new lemmas print standard axioms in `Checks.lean`.
   - The downstream replay passes with `sorry` counts equal to the base's.
2. **#1:** the D8 erratum and the rewritten §5 item 11 are in DESIGN.
3. **#4:** done per R-03e-r2-1. Under option 1, the two statements carry `LevinReduction …`, and their prints still reach exactly `col_zk` and `colRep_efficientProverProof`.
4. **#5, #6, #7:** the docstring and DESIGN texts of §3 are in (including the 03k/03g qualifiers for #5).
5. **#3:** `resolutions-03e-r1.md` rows 5 and M8 are corrected, and `resolutions-03e-r2.md` records every round 2 finding with the current counts (21/18).
6. **M2:** listed in clean-up part 2 (item C's re-point list extended; a `firstHit_eq` item added). It is not a closing condition.

The result is 0 blockers and 0 majors, and the prong C re-syncs stay on gate 06's integration to-do. An external round 3 is needed only if the user wants the #4 statement change audited independently.
