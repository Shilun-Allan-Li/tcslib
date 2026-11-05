# Gate 04 (S2b): review of the auditor's findings, with resolution proposals

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/04-s2b/findings/gate04-s2b-findings.md`: 0 blockers, 2 majors (F01, F02), 4 minors (F03–F06).
- **Code:** worktree `wt-s2b` at `afe5982f612081bba2fbcec9ab41adcbbc118b13` (confirmed with `git rev-parse HEAD`). Line numbers refer to that commit unless a prong worktree is named. The F-1 baseline is `a3c5fa8b`.
- **Downstream code read:**
  - `wt-prong-a` at `2d7b5441` (`Authentication/`);
  - `wt-prong-b` at `c04d8a3a` (`SecureComputation/`, including `Yao.lean`);
  - `wt-prong-c` at `aa71d0e7` (`Composability/`);
  - `wt-prong-d` at `6ea900ae` (`Randomness/`).

  Prongs A–C branch from earlier S2b commits. Their `Games/{BitCodec, Machines, Bridges/*, Protocols, OracleComp}.lean` are byte-identical to `afe5982f`; only `Efficiency.lean` differs (no T2).
- **Method.** I did not build Lean. I did three things:
  - read every S2b proof that consumes another file's definition;
  - ran a script that lists every `unfold`/`simp`/`rw` argument naming a TCSlib definition from another file (scratch tools in `scratchpad/g04-review-tools/`);
  - ran the campaign lint's check 8 (`scripts/campaign_style_lint.py --check8b`) on `TCSlib/Cryptography` at the base `a3c5fa8b` and at the head, and diffed the two.

  Reads through `rfl`, `show` and term-mode definitional unfolding were found by hand. They are what the campaign's rule-10 seal (`attribute [local irreducible]`, `WORKFLOW.md` §"Standing rules") would reject.

## Summary

- **All six findings are true.** I agree with every severity: F01 and F02 are major; F03–F06 are minor.
- **F01 (`decodeIdx` checks only the length).**
  - Confirmed at `BitCodec.lean:60–61`.
  - The fix is a strict unary check with converse lemmas, about 60–90 lines in `BitCodec.lean`.
  - It re-proves one lemma (`decodeIdx_replicate`). No other proof in S2b or in any prong unfolds or reasons about `decodeIdx` or `decodeBitMove`.
  - No statement text changes. Every security notion that uses `bitCodec` quantifies over all NUPPT adversaries, and a coin-preserving post-processing (`exists_comp`) maps each adversary to one with the same computation under the other decoder. So no notion changes meaning.
  - The fix matters most for the efficiency fill. Without converse lemmas the fill cannot read `decodeBitMove` on arbitrary machine output without unfolding it (rule 10).
  - Ruling R-04-1 (light): it changes a T0 definition before the fill is issued.
- **F02 (missing defining equations): true, and understated.** The auditor names 5 consumer sites, in 4 proofs. I find 16 S2b proofs that read another file's TCSlib definitions:
  - the unfolds the auditor names;
  - B2 rewriting with `accept` and `advantage` (`Bridges/Experiments.lean:119,127`);
  - B1 unfolding `QueryImpl.ofComp` and reading `QueryTree.simulate` through `rfl`/`show` (`Bridges/QueryTree.lean:76–77,103–108`);
  - B4 reading `Party.exec`, `step`, `close`, `endWith` and `ExecOutcome.swap` through `rfl`/`show` (`Bridges/Strategies.lean:138–145`), and `simp [moverIsV]` although `moverIsV_true`/`_false` exist (`:163`);
  - `AllOutputs`, which S2b moved from `Hopping.lean` to `OracleComp.lean`. That move turned same-file reads in `Hopping.lean:85,88,168` and `Protocols.lean:238,262–268` into cross-file reads.

  The fix is about 75–85 equation lemmas (mostly `rfl`/`Iff.rfl`, about 450–510 lines with docstrings), with 16 proofs re-pointed. The full list is in §2.

  Prong B would also benefit:
  - at 9 sites that read ch. 2–4's `Protocol.transcriptWith`/`outP`/`outV`/`viewP`/`viewV` (`Interaction.lean`);
  - from 5 lemmas on its own `keyAt`, `garbledValues`, `inputKeys`, `tableAt` and `answersB`, which `Yao.lean` now reads through four private `rfl` copies and one `show`; these should become shared lemmas.

  Ruling R-04-2 decides scope (S2a and ch. 2–4 files would join the change set).
- **What the auditor missed (§5).** The most important miss is N1, proposed **major**:
  - **N1: T1/T2 do not cover the reductions they are cited for.** The auditor listed T1/T2's limitations but did not count them. They lack:
    - adversary input (`toCompOn`);
    - final state and finalization;
    - exact output;
    - a codec bridge to the PRF assumption's `toOracleAdversary`.

    Eight reduction sketches in prongs A and C cite T1 or T2 for reductions that need one of these:
    - Thm 135.4, Thm 137.2 and Thm 144.1 (two machines) in prong A;
    - Thm 168.2, Thm 170.4, Thm 175.9 and `padded_cpa` in prong C.

    Seven of the eight cite T1. Four of those seven need an oracle, which T1's handler cannot query.

    Ruling R-04-3: extend T0–T2 before the fill brief is issued (recommended).
  - **N2:** attestation 4 ran main's per-file `style_lint.py`, which has no check 8. The campaign lint's check 8 shows S2b adding 16 public definitions with no lemma (`workflow.md` §6: "a landing adds no name to it"). It also shows 8 more definitions that pass only by name (a bound or a single case, not an equation).
  - **Minor misses:**
    - N3: the `Strategies.lean` docstring promises results "stated in a later part of this file" that do not exist.
    - N4: `MultiMessageLemmas.take_drop_ofFn_blocks` duplicates `EnsembleLemmas.take_drop_ofFn_blocks` and is not in the duplication ledger.
    - N5: `simp [Option.elim]`, a core definition passed to `simp`, at `Protocols.lean:239`.
    - N6: T1's componentwise default disagrees with T2's joint default (folded into F03).
    - N7: there is no rule-10 seal evidence in the pack.
- **Rulings needed:** R-04-1 (F01), R-04-2 (F02 scope) and R-04-3 (N1). F03–F06 and N2–N7 are maintainer fixes.
- **Proposed closing condition:** F01 and F02 fixed, R-04-3 ruled (and applied if option 1), and the evidence refreshed (§7). Then a delta re-audit of `BitCodec.lean`, `Efficiency.lean` and the new lemmas.

---

## 1. F01 (major): `decodeIdx` checks only the length of the unary index

### Verdict: **true**. Severity: **major (agree)**.

**Evidence at `afe5982f`:**
- `BitCodec.lean:60–61`:
  `def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) := if h : iw.length < k then some ⟨iw.length, h⟩ else none`.
  The bits of `iw` are never read, so `decodeIdx 2 [false] = some ⟨1, _⟩`.
- What the documentation says:
  - module doc `:20–23`: a query is `⟨[false], ⟨1^i, x⟩⟩`, and "anything else, a malformed or wrong-length string, decodes to the all-`false` output";
  - `decodeBitMove`'s docstring `:73–75`: "anything else is the output `zeroBits dα`".
- With `din 1 = 1`, the word `pairEncode [false] (pairEncode [false] [false])` reaches `decodeIdx 2 [false] = some 1` and then `decodeFin 1 [false] = some _` (`:82–85`). So it decodes as `.query 1 _`, not as the default.
- The only lemmas are the forward round trips: `decodeIdx_replicate` (`:64`), `decodeBitMove_query` (`:105`) and `decodeBitMove_ret` (`:112`). Nothing characterizes what is accepted.

I agree with the auditor's scope remark. The alias still has length `i < k`, still costs one query, and the same move can be emitted canonically. So there is no cryptographic attack. The defect is that the decoder does not follow the grammar the shared codec publishes.

**Why major.** `bitCodec` is the codec of every prong's security games and of T0–T2. Two consequences follow:
- The efficiency fill's machine `B` must reproduce `decodeBitMove` on **arbitrary** raw output of `A` (`Efficiency.lean:120–123`). The fill brief's rule 10 forbids unfolding it.
- So the fill needs a complete characterization of `decodeBitMove`. With the current `decodeIdx`, no characterization in the documented terms is true (the alias is a counterexample).

So the documentation is materially misleading, and the API the fill needs cannot be stated. That is major under the gate 02 guide. It is not a blocker, because no statement builds on wrong mathematics (see "Effect" below).

### Fix (recommended): strict unary decoding, with converses

```lean
/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length `≥ k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i   -- re-proved

/-- Converse: exactly the unary codes decode, each to its index. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true

/-- Every other word is rejected. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true

/-- Converse of `decodeBitMove_query`: only the canonical query word decodes as that query. -/
theorem decodeBitMove_eq_query_iff {w : List Bool} {i : Fin k} {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))

/-- **The default:** a word that is neither a canonical query nor a canonical output decodes to
`zeroBits dα`. With `decodeBitMove_query` and `decodeBitMove_ret` this covers every input. -/
theorem decodeBitMove_of_not_canonical {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα)
```

- **The proofs live in `BitCodec.lean`.** They may unfold that file's own `decodeIdx`/`decodeBitMove`. They also use:
  - the published `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:261`);
  - the new `decodeIdx_eq_some_iff`;
  - a converse for `decodeFin`: `decodeFin ℓ w = some x → w = List.ofFn x`. It does not exist yet.
- **The `decodeFin` converse** can be proved without unfolding `decodeFin`, about 8 lines:
  - `length_eq_of_decodeFin_eq_some` (`Adversary.lean:89`) gives `w.length = ℓ`;
  - rewrite `w` as `List.ofFn` of its own entries;
  - `decodeFin_ofFn` then gives `some f = some x`.

  Its home is `Asymptotic/Adversary.lean` (pack 03a), which is outside S2b's change set and is imported almost everywhere. Recommended: a `private` copy in `BitCodec.lean`, plus a requested shared lemma `decodeFin_eq_some_iff` for the next ch. 2–4 window.
- **Optional, and useful to the fill and to prong reductions:** a canonical encoder `encodeBitMove : Move (bitSpec din dout) (Fin dα → Bool) → List Bool`, with `decodeBitMove_encodeBitMove` and `encodeBitMove_injective`. The fill's `B` can then output `encodeBitMove (decodeBitMove w)`, which is the canonicalization step.
- **Docstrings.** `BitCodec.lean:59` gains "every other word is `none`". `:20–23` and `:73–75` can stay as they are, because after the fix they are true.

**Size:** about 60–90 lines in `BitCodec.lean` (the fix, 1 proof re-done, 4–5 lemmas, the private helper), plus about 25 lines if `encodeBitMove` is added.

### Effect on proofs

- **S2b.** Only `decodeIdx_replicate` (`:64–68`) changes. Its `dif_pos` needs the second conjunct, which is `List.length_replicate` plus `rfl`. `decodeBitMove_query`/`_ret` (`:109`, `:114`) go through unchanged: `simp` uses `decodeIdx_replicate`.
- **`Efficiency.lean`.** It contains no proof about the decoder. `InteractiveHandler.call` (`:182`) uses `decodeBitMove` in a definition. Its meaning changes only on handler outputs with a non-unary index, which now take the default.
- **Efficiency fill (not issued).**
  - The round function adds an all-`true` check on the index. It is polynomial-time by the pairing calculus.
  - The proof gets easier: it uses the converse lemmas instead of unfolding.
  - The brief draft's T0 status line ("T0, done and compiling") needs a refresh.
- **Prongs.** I grepped `wt-prong-{a,b,c,d}`, and also `wt-prong-d2`, `wt-pb-yao` and `wt-pb-compose`. No proof unfolds or reasons about `decodeIdx`, `decodeBitMove` or `bitCodec`. The uses are definitions only:
  - prong A: `Authentication/Defs.lean:122,197` (the forger codecs);
  - prong C: `Composability/{Defs:172, PublicKey:382, NonMalleable:71, SimNonMalleable:180,239}`.

  Nothing to re-prove.

### Does any statement change meaning?

No statement text changes. Only the meaning per machine changes: a machine that emits a non-unary index now gets the default return where it used to get a query.

Every notion built on `bitCodec` quantifies over all `A : NUPPT` (prongs A and C: forgery, IND, NM and SIM-NM games; T1 and T2). The class of computations `{A.toComp(On) (bitCodec …) n q r}` is the same before and after:
- **From the old decoder to the new:** post-compose `A` with the polynomial-time canonicalizer "replace a length-`i` index word by `1^i`".
- **From the new decoder to the old:** post-compose with "replace a non-unary query word by `pairEncode [true] (List.ofFn (zeroBits dα))`".

`Complexity.exists_comp` (`Closure.lean:200`) gives `B.coins = A.coins` and `B.runAtL n y r = post (A.runAtL n y r)`, so the coin space is identical and every advantage is preserved. This argument is not in Lean, and nothing needs it to be.

### Ruling: yes, light (R-04-1, §6)

`Efficiency.lean:21` declares the T0 definitions "final", and the fill brief freezes them at issue. The brief is not yet issued, so the change is cheap now.

---

## 2. F02 (major): missing defining equations; consumers unfold other files' definitions

### Verdict: **true, and understated**. Severity: **major (agree)**.

**Rule.** `policy.md` §1 says, under "Definitions land with their lemmas": "Every new public `def` is published, in the same PR and beside the definition, with the lemmas that let a consumer read it without unfolding … Consumers never unfold another file's definition." `briefs/pass-shelat-ch5-8/WORKFLOW.md` (rule 10) adds:
- it "applies to the maintainer's own API proofs too";
- only core and Mathlib definitions "may reduce in `rfl`, `decide` or `show`";
- "an API that must look inside an author's definitions goes beside them, in their file".

The fill brief repeats rule 10 for T1/T2. So without these equations the fill must either break the rule or copy definitions privately.

**The auditor's sites, all confirmed:**
- `Bridges/Machines.lean:65`: `simp only [MachineCodec.encodeLog, …, encodeHist]`. Also `:63`, `| nil => rfl` through both bodies.
- `:79`, `:82`: `unfold buildComp buildTree`.
- `:108`: `simp only [NUPPT.toComp, NUPPT.toOracleAdversary]`.
- `Bridges/Strategies.lean:183`: `simp only [Protocol.outP, Protocol.outV, Protocol.transcriptWith]`.

**Sites the auditor missed (S2b proofs reading other files' TCSlib definitions):**

| Site | What it reads | Kind |
|---|---|---|
| `Bridges/Experiments.lean:119` (`acceptProb_eq`) | `Games.accept` (`Advantage.lean:63`) | `rw [… accept …]` |
| `Bridges/Experiments.lean:127` (`distAdv_eq`) | `Games.advantage` (`Advantage.lean:67`) | `rw [distAdv_def, advantage, …]` |
| `Bridges/QueryTree.lean:76–77` (`simulate_ofComp_pure`) | `Games.simulate`, `QueryImpl.ofComp` (`Simulate.lean:74,115`), `OracleComp.bind` | `rfl`; `exact ih _` by defeq |
| `Bridges/QueryTree.lean:86–87` (`eval_eq_evalFn`) | `QueryTree.eval` (published `eval_ret`/`eval_query` exist but are not used) | `rfl`; defeq |
| `Bridges/QueryTree.lean:103–108` (`simulate_eq`) | `QueryTree.simulate` (`OracleAdversary.lean:150`, no equations), `QueryImpl.ofComp`, `OracleComp.call` | `rfl`, `show`, `simp only [… QueryImpl.ofComp …]` (:106) |
| `Bridges/Strategies.lean:138,142–145` (`exec_turnParty`) | `Party.exec`, `step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–146`), `OracleComp.bind` | `rfl`, `show` |
| `Bridges/Strategies.lean:159` (`exec_eq_alt`) | D8 `exec` at 0 (published `exec_zero` exists) | `rfl` |
| `Bridges/Strategies.lean:163` (`exec_eq_alt`) | `moverIsV` (`Interaction.lean:205`; `moverIsV_true`/`_false` exist) | `simp [moverIsV, h]` |
| `Hopping.lean:85,88,168` | `OracleComp.AllOutputs`, moved by S2b to `OracleComp.lean:268` | term-mode defeq (`exact h a hc`, `hc j`, `exact hs`) |
| `Protocols.lean:238,262,263,268` | `AllOutputs` on `.pure` | `show`; anonymous constructors |
| `Machines.lean:112,116–117` (`buildComp_costBoundedBy`) | `CostBoundedBy` (`OracleComp.lean:203`; `costBoundedBy_pure`/`_query` exist) | `exact trivial`; anonymous constructor |

So 16 S2b proofs read another file's definitions, against the 4 proofs (5 sites) the auditor named. Two cases are new debt rather than missing equations:
- **The `AllOutputs` move.** Gate 02 closed `AllOutputs` as `Hopping.lean`'s own definition. Moving it made `Hopping` and `Protocols` cross-file consumers of a predicate that has no `_iff` lemmas. Check 8 does not flag it, because `allOutputs_true` matches the name.
- **The `Bridges/QueryTree` and `Bridges/Experiments` reads** target S2a definitions (`Simulate.lean`, `Advantage.lean`) that gate 02 closed without equations. Their first cross-file consumers are S2b's.

### Equation lemmas to add, per definition

All are `rfl`, `Iff.rfl`, or a two-line `unfold`/`rw` in the definition's own file. None gets `@[simp]`. Each docstring states its formula (policy §1).

**S2b's own definitions**

| Definition (file:line) | Lemmas |
|---|---|
| `MachineCodec.encodeLog` (`Machines.lean:89`) | `encodeLog_nil : codec.encodeLog [] = []`; `encodeLog_cons : codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)` |
| `buildComp` (`Machines.lean:97`) | four case lemmas covering every input: `buildComp_zero_of_ret (h : next hist = .ret a) : buildComp next t 0 hist = .pure a`; `buildComp_zero_of_query (h : next hist = .query i x) : … = .pure t`; `buildComp_succ_of_ret`; `buildComp_succ_of_query (h : next hist = .query i x) : buildComp next t (q+1) hist = .query i x fun y => buildComp next t q (hist ++ [⟨i, x, y⟩])` |
| `NUPPT.toComp` (`Machines.lean:122`) | `toComp_eq : D.toComp codec n q r = buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []` |
| `NUPPT.toCompOn` (`Machines.lean:135`) | `toCompOn_eq` (the same, with `pairEncode x (codec.encodeLog hist)`) |
| `bitSpec` (`BitCodec.lean:56`, abbrev) | `bitSpec_dom`, `bitSpec_rng` (a new public abbrev still lands with an `_eq` lemma, policy §1) |
| `decodeIdx`, `decodeBitMove` | the converses of §1 |
| `zeroBits` (`BitCodec.lean:71`) | `zeroBits_apply : zeroBits d j = false`; `ofFn_zeroBits : List.ofFn (zeroBits d) = List.replicate d false` |
| `bitCodec` (`BitCodec.lean:97`, structure-valued) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]`, which gives `bitCodec_decodeMove`, `bitCodec_encodeEntry` and `bitCodec_timeout`; plus `encodeLog_bitCodec`, saying the log encoding does not depend on `dα` (`InteractiveHandler.call` encodes logs with `dα = 0`, `Efficiency.lean:184`, while T2's `B` uses `dα.eval n`) |
| `bitSpecAt` (`Efficiency.lean:62`, abbrev) | `bitSpecAt_eq` |
| `PolyHandler.input` (`:86`) | `PolyHandler.input_eq` |
| `PolyHandler.answer` (`:93`) | `answer_of_pairDecode_eq_none`, `answer_of_pairDecode_eq_some` (together, every input), and the well-formed case `answer_of_run_eq (h : H.run (input …) = pairEncode (List.ofFn y) (List.ofFn s')) : H.answer … = (y, s')` |
| `PolyHandler.impl` (`:105`) | `PolyHandler.impl_apply : H.impl n z ω i x s = .pure (H.answer n z ω s i x)` |
| `InteractiveHandler.input` (`:171`) | `InteractiveHandler.input_eq` |
| `InteractiveHandler.call` (`:178`) | `call_eq` (`= buildComp (…) (zeroBits _) (H.perCall.eval n) []`) |
| `InteractiveHandler.impl` (`:190`) | `InteractiveHandler.impl_apply` |
| `singleCodec` (`Bridges/Machines.lean:45`) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]` |
| `toHist` (`Bridges/Machines.lean:54`) | `toHist_nil`, `toHist_cons` |
| `OracleComp.evalFn` (`Bridges/QueryTree.lean:64`) | `evalFn_pure`, `evalFn_query` |
| `treeImpl` (`Bridges/QueryTree.lean:91`) | `treeImpl_apply` |
| `acceptGame` (`Bridges/Experiments.lean:107`) | `acceptGame_eq` |
| `turnParty` (`Bridges/Strategies.lean:69`) | `turnParty_zero : turnParty next 0 M = .pure (next M)` (`turnParty_succ` exists) |
| `waitParty` (`:80`) | `waitParty_none`, `waitParty_some_zero`, `waitParty_some_succ : waitParty next (k+1) M (some y) = turnParty next k (M ++ [y])` |
| `alt` (`:95`) | `alt_zero`, `alt_succ : alt nF nG (k+1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap` (`alt_succ_last` is a derived law, not the defining equation) |
| `OracleComp.AllOutputs` (`OracleComp.lean:268`, moved) | `allOutputs_pure : (OracleComp.pure a).AllOutputs P ↔ P a`; `allOutputs_query : (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P` |
| `singleSpec` (`OracleComp.lean:155`, abbrev) | `singleSpec_dom`, `singleSpec_rng` (optional) |
| `QueryTree.induct` (`OracleAdversary.lean:97`, new; motive in `Sort`) | `induct_ret`, `induct_query` (its computation rules; needed only if data is defined with it) |

**Definitions in files S2b already changes, which S2b's proofs consume (predating the rule, "covered as consumers need them")**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `encodeHist` (`Asymptotic/PRF.lean:201`) | `encodeHist_nil`, `encodeHist_cons` | `Bridges/Machines.lean:63–67` |
| `buildTree` (`PRF.lean:208`) | the four case lemmas, as for `buildComp` | `Bridges/Machines.lean:79–84` |
| `NUPPT.toOracleAdversary` (`PRF.lean:235`) | `toOracleAdversary_eq` | `Bridges/Machines.lean:108` |
| `QueryTree.simulate` (`OracleAdversary.lean:150`) | `simulate_ret`, `simulate_query` | `Bridges/QueryTree.lean:103–108` |
| `oracleDist` (`OracleAdversary.lean:191`) | `oracleDist_apply` (optional now; the ch. 2–4 files unfold it widely, pack 03d) | — |
| `Party.step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–126`, S2a) | `step_pure`, `step_send` (`.query (.inl ()) m k`), `step_coin` (`.query (.inr j) x k`); `close_pure`, `close_send`, `close_coin`; `endWith_eq`; `swap_done`, `swap_outOfFuel`, `swap_sentAfterEnd` | `Bridges/Strategies.lean:138–145` |

**Definitions in files outside S2b's change set (R-04-2 decides whether they join it)**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `Games.accept`, `Games.advantage` (`Games/Advantage.lean:63,67`, S2a) | `accept_eq`, `advantage_eq` (and `guessGame_eq`, which check 8 also lists) | `Bridges/Experiments.lean:119,127` |
| `QueryImpl.ofComp` (`Games/Simulate.lean:115`, S2a) | `ofComp_apply : QueryImpl.ofComp f i x s = (f i x).bind fun y => .pure (y, s)`. Prong A will want `withLog_apply` for its MAC game, `Authentication/Defs.lean:130`. Check 8 also lists `passthrough`, `sum` and `QueryImpl.comp`. | `Bridges/QueryTree.lean:76,106` |
| `Protocol.transcriptWith`, `transcript`, `outV`, `outP`, `viewV`, `viewP`, `Strategy.out` (`ZeroKnowledge/Interaction.lean:326,331,340,344,349,354,267`, ch. 2–4, pack 03e) | `transcriptWith_eq` (`= exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`); `transcript_eq_transcriptWith` (the name `transcript_eq` is taken); `outV_eq` (for any `P'`; `outV_eq_out` covers only the honest `π.P`); `outP_eq`; `viewV_eq`, `viewP_eq`; `Strategy.out_eq` | `Bridges/Strategies.lean:183`; prong B (below) |

### Consumer proofs to re-point (S2b)

1. `Bridges/Machines.lean`:
   - `encodeLog_singleCodec` (`:62–67`): use `encodeLog_nil/cons`, `encodeHist_nil/cons`, `toHist_cons` and `singleCodec_encodeEntry`;
   - `buildComp_singleCodec` (`:78–90`): use the `buildComp`/`buildTree` case lemmas;
   - `toComp_singleCodec` (`:98–110`): use `toComp_eq`, `toOracleAdversary_eq` and `singleCodec_decodeMove`.
2. `Bridges/QueryTree.lean`:
   - `simulate_ofComp_pure` (`:76–77`): use `simulate_pure/query`, `ofComp_apply`, `pure_bind` and `evalFn_*`;
   - `eval_eq_evalFn` (`:86–87`): use `eval_ret/query` and `evalFn_*`;
   - `simulate_eq` (`:103–108`): use `QueryTree.simulate_ret/query`, `treeImpl_apply`, `ofComp_apply` and `call_bind`.
3. `Bridges/Experiments.lean`: `acceptProb_eq` (`:119`) and `distAdv_eq` (`:127`) use `accept_eq` and `advantage_eq`.
4. `Bridges/Strategies.lean`:
   - `exec_turnParty` (`:138–145`): use `Party.exec_zero/succ`, the `step/close/endWith/swap` lemmas, `turnParty_zero`, `waitParty_*` and `pure_bind`;
   - `exec_eq_alt` (`:159`, `:163`): use `exec_zero`, `alt_zero` and `moverIsV_true/false`;
   - `exec_strategies` (`:183`): use `outP_eq`, `outV_eq` and `transcriptWith_eq`.
5. `Machines.lean`: `buildComp_costBoundedBy` (`:112`, `:116–117`) uses `costBoundedBy_pure` and `(costBoundedBy_query …).2`.
6. `Hopping.lean`: `expect_mono_of_allOutputs` (`:85`, `:88`) and `simulate_allOutputs_bad` (`:168`) use `allOutputs_pure/query`.
7. `Protocols.lean`:
   - `endWithT_ne_outOfFuel` (`:238–239`): use `allOutputs_pure`, and `Option.elim_none`/`Option.elim_some` instead of `simp [Option.elim]` (N5);
   - `execT_trace` (`:262–268`): use `allOutputs_pure.2 ⟨…⟩`.

That is 16 proofs (3 + 3 + 2 + 3 + 1 + 2 + 2) and about 60–80 changed lines.

### Size

| Part | Lemmas | Lines (with docstrings) |
|---|---|---|
| `Machines`, `BitCodec` (with F01), `Efficiency` | about 30 | about 200–240 |
| `Bridges/*` | about 17 | about 80 |
| `OracleComp`, `Protocols`, `OracleAdversary`, `PRF` (in the change set) | about 25 | about 120 |
| `Advantage`, `Simulate`, `Interaction` (outside) | about 10–15 | about 50–70 |
| **Total** | **about 75–85** | **about 450–510**, plus about 70 lines re-pointed |

About one maintainer day.

**Evidence to redo:**
- the replay of `Games/*`;
- the downstream of `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` and `OracleComp.lean`, which is already S2b's set;
- under R-04-2 option 1, also the downstream of `Advantage.lean`, `Simulate.lean` and `Interaction.lean` (the ZK modules);
- the axiom prints;
- check 8 (§5, N2);
- a rule-10 seal over the 16 re-pointed proofs.

### Effect on the prongs

- **Statements:** none. All additions are lemmas.
- **Prong B proofs** that read ch. 2–4's D8 definitions, re-pointable once the `Interaction.lean` lemmas land (9 sites):
  - `ObliviousTransfer.lean:155,211`: `simp [Protocol.outV, Protocol.transcriptWith, otProtocol, exec, …]`;
  - `ComposePhases.lean:530,542`: `show` through `viewP`/`viewV`;
  - `ComposePhases.lean:558,577`: `show` through `outP`/`outV`/`transcriptWith`;
  - `Yao.lean:548,555`: `yaoMain_outV/outP … := rfl`;
  - `Yao.lean:795,798`: `show (yaoMain …).outV/outP …`.
- **Prong B's own requested lemmas.** The Yao worker reported these. They are `private … := rfl` copies of another file's definition in `Yao.lean`, so they are themselves definitional closures. They should become shared lemmas beside their definitions, and the copies should be deleted:
  - `keyAt` (`Garbling.lean:192`): `keyAt_of_lt` and `keyAt_of_not_lt`, replacing `keyAt_eq'` (`Yao.lean:310`);
  - `garbledValues` (`Garbling.lean:236`): `garbledValues_eq`, replacing `garbledValues_eq'` (`Yao.lean:610`). Its only lemma, `garbledValues_getD`, is a correctness claim, not an equation.
  - `inputKeys` (`Garbling.lean:231`): `inputKeys_eq`, replacing `inputKeys_eq'` (`Yao.lean:615`);
  - `tableAt` (`Garbling.lean:213`): `tableAt_of_not`, the off-gate case, replacing `tableAt_eq'` (`Yao.lean:620`). `tableAt_gate` already exists.
  - `HybridProtocol.answersB` (`Hybrid.lean:91`): `answersB_eq`, which removes the `show` at `Yao.lean:738–739`.

  This is prong B's work for gate 06, not S2b's. Check 8 on prong B also lists 40 more of its definitions, among them `Garbling.lean`'s `argKeys`, `evalGate`, `garbledRow` and `garbledTable`.
- **Prongs A, C, D:** no current proof reads an S2b definition; their reductions are still sketches. The future fills of Thms 135.4, 137.2, 144.1 (prong A) and 168.2, 170.4, 175.9 (prong C) will need:
  - `toComp_eq`/`toCompOn_eq`;
  - the `buildComp` cases;
  - `bitCodec_*`, `encodeLog_cons` and `zeroBits_apply`;
  - `ofComp_apply`/`withLog_apply`.

  Prong C already states lemmas whose right-hand sides are `.pure (zeroBits _, s)` (`Composability/Defs.lean:156,162`; `PublicKey.lean:371,377`; `NonMalleable.lean:115`; `SimNonMalleable.lean:173`).

### Ruling: scope only (R-04-2, §6)

The rule is binding, so there is no "whether". The ruling decides whether the S2a and ch. 2–4 lemmas join this PR.

---

## 3. Minors

### F03: `PolyHandler.answer` defaults componentwise

- **Verdict: true. Severity: minor (agree).**
- **Evidence:**
  - `Efficiency.lean:91–92`: "A malformed output gives the all-`false` answer and state".
  - `:97–100`: after `pairDecode` succeeds, the code is `((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`. So `pairEncode [true] []` (with both lengths 1) gives answer `true` and state all-`false`.
- **Missed by the auditor (N6).** T2's handler defaults **jointly**. `InteractiveHandler.call` decodes `y ‖ s'` with one `decodeFin (dout + stateLen)` through `decodeBitMove` (`:182`), so a wrong total length gives all-`false` for both. T1 and T2 thus disagree on malformed output, and neither docstring says so.
- **Fix (recommended, docstring-only).** Reword `:91–92` to: "if `run`'s output is not a pair, both are all-`false`; otherwise each component of the wrong length is replaced by all-`false` independently". Add the `answer_*` equations of §2. State the joint default in `InteractiveHandler`'s docstring (`:145–150`).
- **Alternative (not recommended now).** Reject the whole pair, aligning with T2. That changes a T0 definition and would need a ruling. No consumer cares: handlers are the reduction's own code and never emit malformed output.
- **Effect on prongs:** none (no prong defines a handler yet).
- **Ruling:** no.

### F04: "up to `perCall(n)` rounds of `run`"

- **Verdict: true. Severity: minor (agree).**
- **Evidence.** `Efficiency.lean:146–147` says "One inner query `x` to oracle `i` is answered in up to `perCall(n)` rounds of `run`". But `call` is `buildComp … (H.perCall.eval n) []` (`:182–185`), and `buildComp` inspects one more move at fuel 0 (`Machines.lean:99–101`). So `p` outer queries take up to `p + 1` activations, and `perCall = 0` still gives one activation. `call`'s docstring "up to `perCall(n)` rounds against the outer oracles" (`:175–176`) is ambiguous. The field docstring (`:157`, "bound on outer queries") and the module doc (`:37`, "up to `perCall(n)` times per inner query") are correct.
- **Fix (docstring-only).** `:146–147`: "answered with at most `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off with the default)". The same for `:175–176`. The fill brief's replay bound should count `q(n)·(perCall(n)+1)` handler activations, which the auditor's construction outline already does.
- **Effect:** none on statements. T2's budget `q(n)·perCall(n)` counts queries and is correct.
- **Ruling:** no.

### F05: attestation 3 miscounts the axiom log

- **Verdict: true. Severity: minor (agree).**
- **Evidence.**
  - `evidence/axioms.log` has 237 entries, including `uprob_update_absorb'` (`:226`). Two contain `sorryAx` (T1 `:154`, T2), so 235 are clean. The pack says 236 and 234.
  - A comment-stripped count of the 22 changed files gives 237 public and 14 private theorem declarations (251 in all), matching the auditor.
  - The private ones cannot be `#print`ed from outside their file. Their admission-freeness is attested instead by the replay's per-module `sorry=` counts (`replay.log:732`, `Games/Efficiency … sorry=2`, all other S2b modules `sorry=0`).
- **Fix.** Reword attestation 3: "237 public theorems printed; 235 standard-only; T1 and T2 `sorryAx`. The 14 private theorems are covered by the replay's admission counts." When the evidence is refreshed (§7), also carry the source/olean provenance the auditor asks for. The replay header names `827ad8e1`, while the axioms and lint name `afe5982f`.
- **Effect on prongs:** none.
- **Ruling:** no.

### F06: inherited descriptions overstate their statements

**Verdict: true, all five points checked. Severity: minor (agree).** None is an F-1 regression: F-1's diff to these files touches only universe binders.

| Point | Evidence | Fix (docstring-only) |
|---|---|---|
| `multiMsgAdv_boundedBy` | `MultiMessage.lean:147–148`: "makes exactly `q + 1` queries"; the statement is `BoundedBy (q + 1)` | "at most `q + 1`" |
| `decodeFin_runAt_prfDec_of_not_wf` | `:467–468`: "a ciphertext `w` that is not a pair of `n`-bit strings"; the premise is the projected lengths, and `w = []` at `n = 0` is not a pair but meets them | "whose two projections are not both `n` bits long" |
| `pairFstD_pairFstD_histBlock` | `MultiMessageLemmas.lean:299`: "the two components … the query and the answer"; the statement gives the query only | "the query component" (or add the answer projection) |
| `take_drop_ofFn_blocks` | `:377–379`: "(private copy …)" but public. It is also an unledgered duplicate (N4). | see N4 |
| `exists_queryChain_nuppt` | `:618–619`: "asks `ρ₀, …, ρ_{q(n)}`"; the statement gives evaluation equality only | "whose evaluation against any oracle `g` is …" |
| `SubHybrids.tableDist`, `GGM.ggmDist` | `SubHybrids.lean:103`, `GGM.lean:194`: "*Cost.* … at most `q` evaluations of `G`" holds only when `A.BoundedBy q` | add "for `A` bounded by `q`" |

- **Where to fix.** The files are in S2b's change set (F-1), but their packs are 03d (`MultiMessage`) and 03j (`MultiMessageLemmas`), both pending. Recommended: fix the docstrings in S2b and tell the 03d and 03j pack authors, so those auditors do not re-raise them.
- **Effect on prongs:** none.
- **Ruling:** no.

---

## 4. Severities at a glance

| # | Verdict | Auditor | Proposed | Fix kind | Ruling |
|---|---|---|---|---|---|
| F01 | true | major | major | definition change plus new lemmas | R-04-1 (light) |
| F02 | true, understated | major | major | new lemmas, 16 proofs re-pointed | R-04-2 (scope) |
| F03 | true | minor | minor | docstring plus equations | no |
| F04 | true | minor | minor | docstring | no |
| F05 | true | minor | minor | evidence wording | no |
| F06 | true | minor | minor | docstrings | no |
| N1 | missed | — | **major** | statement change before the fill (or wrappers) | R-04-3 |
| N2 | missed | — | minor | evidence (lint and seal) | no |
| N3 | missed | — | minor | docstring | no |
| N4 | missed | — | minor | ledger entry | no (ledger) |
| N5 | missed | — | minor | proof (folded into F02) | no |
| N6 | missed | — | minor | folded into F03 | no |
| N7 | missed | — | minor | evidence (folded into N2) | no |

---

## 5. What the auditor missed

### N1 (proposed major): T1/T2 do not cover the reductions they are cited for

The auditor's "Exact limitations" 1–4 (findings lines 179–186) are correct, but were not counted ("possible missing future prongs are not counted as additional present majors"). The brief's item 3 asks exactly this question ("T1 and T2 must be usable contracts … what a reduction needs"). The coverage is already claimed in two places:
- `Efficiency.lean:44–47`: T2 is what "the PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions" need;
- the pack: T2 is "needed by the reductions of Thms 135.4, 144.1, 168.2, 170.4".

The prongs' sketches build on that claim. Five gaps:

1. **No adversary input.** T1 and T2 simulate `A.toComp` (`Efficiency.lean:136`, `:224`). The signature and public-key games run `A.toCompOn … pk`:
   - prong A: `Authentication/Defs.lean:207`;
   - prong C: `Composability/PublicKey.lean:391`, `NonMalleable.lean:100`, `SimNonMalleable.lean:218,260`.

   In a reduction the input is computed from the reduction's input `z` and seed `ω`. Lamport builds `pk` from `y` and its coins; hash-and-sign's `B` and `C` build `⟨pk, i⟩`.
2. **No final state and no finalization.** T1 hides the state (`∃ s`) and T2 projects it away (`res.1`). Several reductions post-process `A`'s output with the state or seed, and sometimes with more oracle queries:
   - the PRF MAC's distinguisher queries at `A`'s message and checks freshness against the log;
   - Lamport outputs `σ'_i` or aborts;
   - hash-and-sign outputs `(m, m′)` or `(h_i(m′), σ′)`;
   - Thm 175.9 (⇒) asks ℓ more `Dec` queries and runs `D`;
   - `padded_cpa` flips or zeroes the guess.
3. **Normalized output only.** T1 gives `padFin dα (B.runAt …)` (`:138`). An inverter is read through `decodeFin` (`NUPPT.inverter`, `Adversary.lean`), so Lamport's `B` needs exact output.
4. **No bridge to the PRF assumption.** `PRF F` (via `OracleEnsemble.Indist`) quantifies over `D.toOracleAdversary`, which is `D.toComp (singleCodec ℓ₁ ℓ₂)` by `toComp_singleCodec`. T2's `B` is a `toCompOn (bitCodec …) z` machine. The two differ in:
   - the index type (`Unit` against `Fin 1`);
   - the query word (`⟨[false], x⟩` against `⟨[false], ⟨[], x⟩⟩`);
   - the verdict word (`[true, b]` against `⟨[true], [b]⟩`);
   - the log entry (`⟨x, y⟩` against `⟨[], ⟨x, y⟩⟩`);
   - the input (none against `⟨z, log⟩`).

   No lemma relates them. Every PRF-based reduction needs one: 135.4, 168.2 and 170.4.
5. **T1 is cited where only T2 can apply.** T1's handler targets `unifSpec` and answers with `.pure` (`:105–108`), so it cannot query any oracle. Yet "by T1" is cited for oracle-forwarding reductions:
   - `PRFMAC.lean:111` ("the handler forwarding queries");
   - `PRFScheme.lean:76` ("querying its own oracle … efficiency by T1");
   - `CCA2Scheme.lean:300` ("answers `Enc′` and `Dec′` with its oracle … by T1");
   - `NonMalleable.lean:125` ("asks CCA2's `Dec` … `D` is run by T1's handler").

**What each reduction needs:**

| Reduction (prong, file:line) | Cites | Input | Final/state | Exact output | Codec bridge | Oracle (T2) |
|---|---|---|---|---|---|---|
| Thm 135.4 PRF MAC (A, `PRFMAC.lean:111`) | T1 | — | yes (final query, log) | — | yes | yes |
| Thm 137.2 Lamport (A, `Lamport.lean:463–464`) | T1 | yes | yes (abort, `σ'_i`) | yes (inverter) | — | — |
| Thm 144.1, `B` (A, `HashAndSign.lean:266–267`) | T1 | yes | yes | — | — | — |
| Thm 144.1, `C` (A, `HashAndSign.lean:271–272`) | T2 | yes | yes (`h_i(m′)`) | — | — | yes |
| Thm 168.2 CPA/CCA1 (C, `PRFScheme.lean:76`) | T1 | — | — (`b` fixed in the handler) | — | yes | yes |
| Thm 170.4 (C, `CCA2Scheme.lean:300`) | T1 | — | — | — | yes | yes |
| Thm 175.9 (⇒) (C, `NonMalleable.lean:125`) | T1 | yes | yes (ℓ `Dec` queries, then `D`) | — | — | yes |
| `padded_cpa` (C, `PublicKey.lean:417`) | T1 | yes | yes (flip or zero) | — | — | — |

**Why major.** The coverage claim at `Efficiency.lean:44–47` is materially misleading. T0–T2 freeze at the fill's issue (fill brief, ground rule 1). A later change costs a re-freeze and a re-fill, or one machine construction per reduction (several hundred lines each, by the S2b-efficiency note's own count for ch. 2–4). No present statement is wrong (T1/T2 are true candidates), so it is not a blocker.

**Fix (recommended, R-04-3 option 1): extend before issue.** A sketch:

```lean
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  stateLen seedLen : PolyExpr
  init : ∀ n, Fin (stateLen.eval n) → Bool
  run : List Bool → List Bool
  poly : PolyTimeComputable run
  /-- The adversary's input, from `⟨1^n, ⟨z, ω⟩⟩`. -/
  advIn : List Bool → List Bool
  advIn_poly : PolyTimeComputable advIn
  /-- The reduction's output, from `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (final state, adversary's output). -/
  out : List Bool → List Bool
  out_poly : PolyTimeComputable out

-- T1': exact output, adversary with input
∃ B : NUPPT, ∀ n, ∃ φ, ∀ z ω r, ∃ a s,
  simulate (H.impl n z ω) (A.toCompOn codec n (q.eval n) (H.advIn (seedIn n z ω)) r) (H.init n)
    = .pure (a, s) ∧
  B.runAt n z (φ (ω, r)) = H.out (pairEncode (seedIn n z ω) (pairEncode (List.ofFn s) (List.ofFn a)))
```

- **T2'** uses the same fields, with an interactive finalization: one more `call`-like phase `H.finish n z ω s a` on the outer oracles, with budget `finCall` and a `dβ`-bit output. Its conclusion is `(simulate …).bind (fun res => H.finish n z ω res.2 res.1) = B.toCompOn (bitCodec din' dout' dβ) n (q·perCall + finCall) z (φ (ω, r))`.
- **Two companions:**
  - `exists_toCompOn_of_toComp`: an input-free adversary is an input-taking one that ignores its input. It follows from `exists_comp` with `pre = pairSndD`; the coins are unchanged.
  - **T4**, the codec bridge: `∀ B, ∃ B'` with `B'.coins = B.coins` such that `(B'.toOracleAdversary n ℓ₁ ℓ₂ q r).eval f` equals the evaluation of `B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1) n q [] r` against `fun _ => f`, read at bit 0. An eval-level equality suffices for `oracleDist`/`prfAdv` and avoids relabelling `Unit` against `Fin 1`.
- **Cost.** T0 gains 4 fields per handler structure and one definition. T1/T2 are restated (still `sorry`), and T4 and the companion are stated. The fill grows by an estimated 400–700 lines (input threading, finalization replay, T4's re-encoding of logs). The prong sketches above re-cite T1′/T2′/T4. No prong statement text changes.

**Effect on the prongs.** Docstring sketches only, at the eight sites listed. Their theorems are `sorry` under sketches.

### N2 (minor): the lint attestation omits check 8; no rule-10 seal evidence (with N7)

- **What the pack ran.** Attestation 4 (`evidence/lint.log`: "0 findings in 22 files") ran `scripts/style_lint.py`. That is main's per-file linter, with checks for docstrings, sketches, headers and size, but no check 8. `workflow.md` §6 names `scripts/campaign_style_lint.py` as the campaign lint, and says of check 8: "a landing adds no name to it".
- **What check 8 shows** (`--check8b`, `TCSlib/Cryptography`), at `a3c5fa8b` against `afe5982f`. S2b removes `invProb`, `predProb` and `uexp` (F-3, done) and **adds 16 names**:
  - `BitCodec`: `bitCodec`, `zeroBits`;
  - `Bridges/Experiments`: `acceptGame`;
  - `Bridges/Machines`: `singleCodec`, `toHist`;
  - `Bridges/QueryTree`: `OracleComp.evalFn`, `treeImpl`;
  - `Bridges/Strategies`: `waitParty`;
  - `Efficiency`: `answer`, `call`, `impl` ×2, `input` ×2;
  - `Machines`: `encodeLog`;
  - `OracleAdversary`: `induct`.
- **Name-only passes.** Check 8 accepts any lemma whose name starts with the definition's, so 8 more definitions pass on a name alone:
  - `buildComp` (`buildComp_costBoundedBy`);
  - `NUPPT.toComp` and `toCompOn` (`_costBoundedBy`);
  - `decodeIdx` (`decodeIdx_replicate`);
  - `decodeBitMove` (`_query`/`_ret`);
  - `turnParty` (`turnParty_succ`);
  - `alt` (`alt_succ_last`);
  - `AllOutputs` (`allOutputs_true`).

  This is F02's list in mechanical form.
- **Fix.** Re-run attestation 4 with `campaign_style_lint.py --check8b`. Its check-8 diff against the base should list no new name after F02. Add a rule-10 seal log (WORKFLOW rule 10: `attribute [local irreducible]` on every consumed definition, with controls) for the 16 re-pointed proofs.

### N3 (minor): `Bridges/Strategies.lean` promises results that are not there

- `:50–51` says: "The traced and probabilistic forms (views, and tapes sampled first) are stated in a later part of this file." The file ends at `exec_strategies` (`:173–189`).
- B4's design theorems 2–4 (traces, probabilities, fuel; `design/B4-strategy-embedding.md`) are not stated. The auditor noted that they are absent, but not that the docstring claims them.
- Fix: "are planned (B4 design note, theorems 2–4) and not yet stated". No prong uses B4 yet (grep for `turnParty`, `exec_strategies` and `Bridge.` in all prongs: none).

### N4 (minor, inherited): an unledgered duplicate

- `MultiMessageLemmas.lean:379`, `TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks`, has the same statement as `EnsemblesLemmas.lean:385`, `TCSlib.Cryptography.EnsembleLemmas.take_drop_ofFn_blocks`. Its docstring calls it a "private copy", but it is public.
- It is not in `duplication-ledger.md` (DL-1 to DL-8). It predates S2b.
- Policy §1, "Duplication": "every instance … must be human-approved".
- Fix: ledger entry DL-9 (keep the `EnsembleLemmas` copy and point `MultiMessageLemmas` at it), routed to pack 03j. Correct the docstring now (F06).

### N5 (minor): a core definition passed to `simp`

- `Protocols.lean:239`: `cases p.1 <;> simp [Option.elim]`. The 2026-10-23 rule allows core definitions only in `rfl`/`decide`/`show`.
- Fix: `Option.elim_none`/`Option.elim_some` (core lemmas). This is folded into F02's re-point 7.

### N6 (minor): T1's and T2's malformed-output defaults disagree

Folded into F03.

### Not findings (checked)

- **No new `@[simp]`.** The diff `a3c5fa8b..afe5982f` adds none.
- **The facades are complete.** `Games/Bridges.lean` imports all seven S2b modules, and `TCSlib.lean:60–61` imports `Games` and `Games.Bridges`. The facade's contents line for `Efficiency` names only T1; the auditor's editorial note stands, and the fix is to add T2.
- **The replay covers T2.** `replay.log:732` shows `Games/Efficiency … sorry=2`, recorded after the T2 commits, despite the `827ad8e1` header.

---

## 6. Rulings for the user (multiple choice; recommended option first)

**R-04-1 (F01): the unary index of the shared codec.**
1. **Strict unary decoding, with converse lemmas (recommended).** `decodeIdx` checks `iw = List.replicate iw.length true`. Add `decodeIdx_eq_some_iff`, `decodeIdx_eq_none_iff`, `decodeBitMove_eq_query_iff` and `decodeBitMove_of_not_canonical`, plus optionally `encodeBitMove`.
   - *Cost:* about 60–90 lines in `BitCodec.lean`, one lemma re-proved, and a T0 change before the fill is issued.
   - No prong edits; no change of meaning for any ∀-adversary notion.
   - The fill adds one all-`true` check.
2. **Keep length-only decoding, and document it.** The grammar becomes "any word of length `i < k` names oracle `i`", with converse `decodeIdx k iw = some i ↔ iw.length = i`.
   - *Cost:* docstrings at `BitCodec.lean:20–24,59,73–75` and `Efficiency.lean:149`.
   - The codec is no longer injective on accepted words.
   - It departs from D7's strict-format convention, under which ch. 2–4's `decodeOracleMove` is exact.

**R-04-2 (F02): the scope of the equation lemmas in this PR.**
1. **Everything S2b's proofs consume, in this PR (recommended).**
   - S2b's own definitions;
   - `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` (S2a definitions) and `OracleComp.lean`, already in the change set;
   - `Advantage.lean`, `Simulate.lean` (S2a) and `Interaction.lean` (ch. 2–4), which join it;
   - all 16 proofs re-pointed.

   *Cost:* about 75–85 lemmas, about 450–510 lines, about 70 lines re-pointed, and the replay extended to `Interaction.lean`'s downstream. Packs 03d and 03e get small additive deltas (`rfl` lemmas only). Prong B can then re-point its 9 D8 sites.
2. **S2b's own definitions and the files already in the change set now; `Advantage`, `Simulate` and `Interaction` in a follow-up PR before gate 06.**
   - *Cost:* `acceptProb_eq`, `distAdv_eq`, `simulate_ofComp_pure`, `simulate_eq` and `exec_strategies` keep reading those definitions until then. That is a recorded debt line the user acknowledges, and `Bridges/{Experiments, QueryTree, Strategies}` must be re-pointed twice.
3. **Acknowledge the whole debt and close.**
   - *Cost:* not recommended. The efficiency fill must then break rule 10 or carry private copies (each a disclosed duplicate), and every prong reduction repeats this.

**R-04-3 (N1): T1/T2 as contracts for the cited reductions.**
1. **Extend T0–T2 before the fill brief is issued (recommended).**
   - adversary input from a polynomial-time function of `⟨1^n, z, ω⟩` (`A.toCompOn`);
   - a polynomial-time finalization on (final state, output), interactive in T2 with its own budget;
   - exact output in T1;
   - companions `exists_toCompOn_of_toComp` and T4 (the codec bridge to `toOracleAdversary`).

   *Cost:* T0 gains 4 fields per handler and one definition; T1/T2 are restated (still `sorry`); 2 statements are added; the fill grows by about 400–700 lines; a delta re-audit of `Efficiency.lean`. The eight prong sketches are re-cited.
2. **Keep T1/T2 and add wrapper targets T4 (codec bridge), T5 (adversary input) and T6 (finalization and exact output).**
   - *Cost:* three more machine-level statements, each with its own functional equation by induction on the budget, plus composition of machines. More total work than option 1, and every reduction composes three or four results.
3. **Accept as a scope limitation.** Correct `Efficiency.lean:44–47` and the eight sketches to say what T1/T2 do not cover.
   - *Cost:* prongs A and C build their own machines for Thms 135.4, 137.2, 144.1 (×2), 175.9 and `padded_cpa`, and a PRF codec bridge for 135.4, 168.2 and 170.4. That is several hundred lines each: the per-reduction cost the efficiency route was meant to remove.

---

## 7. Proposed closing condition for gate 04

1. **F01** applied per R-04-1: the converse lemmas, and `decodeBitMove_of_not_canonical` proved.
2. **F02** applied per R-04-2: the lemmas of §2, and the 16 proofs re-pointed.
3. **R-04-3** ruled. Under option 1, T0–T2 restated and T4 stated before the fill brief is issued.
4. **F03, F04, F06, N3** docstrings fixed. N4 recorded in the ledger as DL-9 (pack 03j).
5. **Evidence refreshed at the new head:**
   - the replay, with source and olean provenance;
   - axiom prints with corrected counts (F05);
   - `campaign_style_lint.py --check8b` with no new check-8 name against the base (N2);
   - a rule-10 seal log for the re-pointed proofs (N2, N7).
6. **A delta re-audit** of `BitCodec.lean`, `Efficiency.lean` and the new equation lemmas. The equation lemmas are `rfl`, so a statement-only check suffices.
