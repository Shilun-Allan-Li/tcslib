# Gate 02 (S2a), round 2: review of the auditor's findings

**What was checked.**
- **The code.** The worktree `.../scratchpad/wt-s2a` is at `586510c1416afa21881b9a42b5a8d0578c9bd749` (`git rev-parse HEAD`), and it is clean. I read all seven files in full. Line numbers below are per file. Files without a directory are under `TCSlib/Cryptography/Games/`.
- **The D8 model.** `ZeroKnowledge/Interaction.lean` in the main checkout: `exec` :218, `Strategy.out` :267, `Protocol` :284, `outP` :344, `outV_eq_getLast_of_moverIsV` :386.
- **The source.** The [PS10] PDF has SHA-256 `76245560…bda8`, the same as the auditor's. Text was extracted for book pp. 69–73, 114–116, 155 and 168–169, and the whole book was searched for guessing formulations.
- **The model.** An exact-rational Python transcription of `step`/`close`/`endWith`/`exec` and `stepT`/`closeT`/`endWithT`/`execT` is in `.../gate02r2-review/scripts/model.py`. It checked:
  - finding 1's counterexample;
  - finding 3's branch;
  - Q2 example 8, the coin order;
  - the three trace invariants of note 5, on 13,336 outcomes of 4,000 random party pairs with fuel 0–5. There were no violations, and both alternation cases and all three outcome kinds occurred.
- **Axioms.** I recounted the theorems against `evidence-r2/axioms.log`.
- **No Lean was run.**

**Bottom line.**
- The auditor's 15 verdicts and 6 findings are substantially right, and I found **no blocker or major**. The gate can close on the auditor's terms.
- **M2 is right for the wrong reason.** [PS10] does state the guessing/distinguishing relation, in §3.1.1, book p. 73, Lemma 73.8. So the code's "without stating it" is false. The auditor's fix would leave the theorem without its correct tag.
- **Missed minor.** The auditor also missed an off-by-one in the prose of `exists_advantage_hybrid_gap`.

## Table

| Item | Verdict | My severity | Justification |
|---|---|---|---|
| T1 #1 (fixed) | true | note (closed; was blocker) | `close` (`Protocols.lean:110–113`) returns `none` at the first exchange query and never runs its continuation. `endWith` (:117–119) maps `none` to `sentAfterEnd`. At fuel 0, `exec` (:132–133) maps a send to `outOfFuel`. So no drain can turn an attempted send into `done`, which closes the round 1 defect. The extra activation is declared at :125–129. The caveat is right: the code is broader than "D8 with early returns" (finding 1). |
| T1 #2 (fixed) | true | note (closed; was major) | `execT` (:206–211) conses `mk.1` onto the second mover's received list and concatenates `p.2 ++ r.2.2.coins` for the first mover. `endWithT` (:191–193) records closing draws. The model gives Bob `received = [m]` when he returns at once (`exec 1`, send-then-return). `execT_outcome` (:252) is equality of `ProbComp` trees after projection. The full-tape caveat is finding 2. |
| T1 #3 (fixed) | true | note (closed; was major) | `hagree` (`Hopping.lean:222–224`) is equality of `E[1_good · g]` for every `g`, that is, of the unnormalized good-successor laws of (reply, state). The crossing-call example satisfies it: both handlers put mass ½ on (false,false). The gap is ½, which equals the bad probability. A discarded `sampleFin 0` leaves every expectation unchanged. Both stickiness premises are kept (:225–226). `hagree_of_eq` (:326) and `identical_until_bad_init` (:338) state what their docstrings say. |
| T1 #4 (recorded) | true | note (recorded debt) | Two records carry the restriction: `design/S2-game-framework.md:53–54` and `inventory-ch5-8.md:130` (strict PPT or `PerfectZKAbort`). Nothing in S2a claims expected-time coverage. The auditor's point about a uniform per-session abort bound for `Q·2^-k` is correct union-bound bookkeeping, and it belongs in the ch. 7 statement. |
| T1 #5 (fixed) | true | note (closed; was minor) | The `rfl` examples at :154–163 and the recurrence (:132–136) agree with the model. A return costs no fuel, and each delivered message costs one. One send followed by two returns needs fuel 1, and a further reply at fuel 1 gives `outOfFuel`. The residue is finding 3. |
| T1 #6 (fixed) | true | note (closed; was minor) | `OracleComp.lean:17–19`: "well-founded tree (every run makes finitely many queries) … With finite answer types … the tree is finite". This is accurate, and the `ProbComp` claim (`Probability.lean:24`) is correct. |
| T1 #7 (fixed) | true for the code; headers not re-verified | note (closed; was minor) | Tags are at `Probability.lean:72` and `:79` (`uniformFin`) and at `Simulate.lean:139` (`QueryImpl.compose`) and `:147` (`simulateQ_compose`). The reference blocks list `ProbComp/Basic.lean` and `QueryImpl/Compose.lean`. `CITATION-VCVio.md`'s author list agrees with the round 1 review's verified reading. I could not re-read the VCVio headers: the session's GitHub access excludes that repository. |
| T1 #8 (not resolved) | partly true | minor | **True:**<br>- `Hopping.lean:46–48` says outright that no section or lemma number is cited, and `:127` and `:288` cite bare `[Sho04]`. This falls short of `policy.md` §2 ("precise location").<br>- `[BR06]` (:44–45, :288) also lost its location and is equally unpinned. The auditor's Table 1 does not count it.<br><br>**Not verified:** the auditor's replacement (18 Jan 2006 revision, §1.1, Lemma 1, p. 3). `www.shoup.net` does not resolve from this session, and ePrint returned 403.<br><br>**Also:** the `[Sho04]` entry in `Advantage.lean:47–48` is now cited by no declaration in that file. The repair removed `[Sho04, §3]` from `advantage_hybrid`. |
| T1 #9 (fixed) | true | note (closed; was minor) | `Advantage.lean:70` says "nonnegative", matching `0 ≤ accept G`. `Hopping.lean:100–101` states the support-restricted inequality that the theorem proves. |
| T1 #10 (fixed) | true | note (closed; was minor) | `Advantage.lean:6` imports `Foundations.Probability`, which has only Mathlib imports (checked). `:102–104` and `:109–111` are one-line instances of `abs_sub_le_sum_hybrids` and `exists_hybrid_gap` (`Foundations/Probability.lean:211,223`). The constant is finding 4. |
| T1 #11 (recorded) | true | note | `resolutions-r1.md:39` records it. No S2a declaration claims a bounded fair-bit implementation of `sampleFin 2`. |
| T1 #12 (recorded) | true | note | The facade (`Games.lean:27–29`) defers the bridges. `S2-game-framework.md:219–222` reports B1/B2/B3 work in `Games/Bridges/…` and `Games/Machines.lean`, neither of which exists at this head (checked: the worktree has only the six modules). |
| T1 M1 (fixed) | true | note (closed; was minor) | `Hopping.lean:21–24` and `:150–153` scope the bound to one fresh draw after a list. The statement's program shape (`c.bind fun L => (sample T).bind …`, :160) forces the list to come first. |
| T1 M2 (not resolved) | partly true | minor | **True:**<br>- Def 168.1 (book p. 168) defines `IND_b` for fixed `b ∈ {0,1}` and asks for `{IND_0} ≈ {IND_1}`, which is a distinguishing definition. So `Advantage.lean:151` ("uses both (§3.1 and Def 168.1)"), `:116` ("The challenge bit … of [PS10, Def 168.1]") and the reference line `:45–46` misattribute the guessing form.<br><br>**False:** the auditor's claim that §3.1 offers only "informal guessing motivation":<br>- §3.1.1, "Distinguishing versus Predicting" (book p. 73), states that a predictor with success `½ + 1/poly` "would be a valid distinguisher (show this!)".<br>- Lemma 73.8 (the Prediction Lemma) formally uses `Pr[b ← {0,1}; t ← X^b_n : A(t) = b] ≥ ½ + µ(n)/2`.<br>- So the code's "without stating it" is itself false. The correct tag for `accept_guessGame` and `guessAdv_eq_half_advantage` is [PS10, Lemma 73.8] / p. 73.<br><br>**Also missed:** the concrete layer already has the exact identity `predict_eq`, tagged so (`Asymptotic/Ensembles.lean:565–580`). The auditor's fix would leave the theorem untagged. |
| T1 M4 (recorded) | true | note | `S2-game-framework.md:46–52` names the current declarations and states that the code and that paragraph take precedence over the pre-gate sketches below (`Option (α × β)` and log-based views at :175–179, `IsQueryBound` at :130). The paragraph itself repeats "Executions follow D8's reading" and "Views are recorded by the executor" (:49–50), so it inherits findings 1–2. |
| T2 #1 | true | minor | **The counterexample is exact.** In the model, `exec 1 (send false (λ_. return true)) (λ_. return false)` gives `done true false` with probability 1, `M_A = []` and `M_B = [false]`. In D8, a party's output is `next` on its complete history (`Interaction.lean:267,344–345`). The last sender's history does not change after its last send (`exec`, :218–224). So its output is its last message: here `outP = P.next … [] =` the one message. No one-message D8 protocol gives Alice output ≠ message. `outV_eq_getLast_of_moverIsV` (:386) is the verifier instance of this.<br><br>**The code says otherwise.** `Protocols.lean:22–23` ("As in … D8, the waiting party is activated once more") and `:128–129` ("Unlike D8 … a party may return early") present early returns as the only difference, and so does `Games.lean:42–43`. D8 never re-activates the last sender on new input.<br><br>**Why minor.** It is an overclaim in documentation, not a bug. The maintainer's later ruling (main `7bd1a019`, plan decision log 2026-11-05) defines protocols by D8 strategies and uses `Party` only as a proof calculus via B4, so no definition is built on arbitrary `Party`s. |
| T2 #2 | true | minor | `stepT`/`closeT` (:180–181, :187–188) record `⟨j, y⟩` only when a draw is executed. A party that never draws has `coins = []`, whatever its source tape. [PS10] §4.4 (book p. 115) puts the whole tape `r` in the view, and "Random executions" (p. 116) samples every bit of it. D8's `View.r` is `List.ofFn` of the full `Coins` (`Interaction.lean:350,355`). So `Obs` with fixed inputs cannot recover unused tape bits, and draws from `Fin (m+1)` with `m+1 ≠ 2^k` are not bit strings. The module claim (:28–33) and the `[PS10, §4.4] (views)` tag on `execT` (:198) overstate this. Minor, because sampling the full tape first fixes it, as the auditor's Q6 says and the later ruling adopts. |
| T2 #3 | true | minor | The prose of `exec_zero` (:138) mentions only the send. The statement (:140) also has the `inl a ↦ endWith a B` branch. In the model, `exec 0 (return a) (λ_. return b)` gives `done a b`, and a waiting party that draws a bit and sends on one value gives `done`/`sentAfterEnd` with ½ each. Under `policy.md` §2 ("Statement prose … trusted surface"), the omission is a defect, though a small one. |
| T2 #4 | true, and it understates the issue | minor | **The constant.** Lemma 71.6 (book pp. 71–72) has `m` distributions `X¹…Xᵐ`, a threshold with `|g₁ − g_m| > ε`, and the conclusion `|gᵢ − gᵢ₊₁| > ε/m`. The Lean statement (`Advantage.lean:109–110`) has `n` hops and the bound `adv(G 0, G n)/n`. It is sharper (`m = n + 1`) and non-strict, so the source's form follows from it. The docstring discloses none of this. `policy.md` §2 *Deviations* requires the disclosure, and the concrete `hybrid_lemma` (`Asymptotic/Ensembles.lean:410–414`) already gives it.<br><br>**Missed by the auditor.** The docstring says "along a chain of `n > 0` games", but `G 0, …, G n` has `n + 1` games and `n` hops, so the prose miscounts. The auditor's comparison said "The prose matches". |
| T2 #5 (note) | true | note | Erasure alone does not certify the observations' contents, and the three invariants are true for the code as written (proof sketch below). The model found no violation in 13,336 outcomes. The bound in (i) is attained by `done` and `sentAfterEnd` as well, so its converse is false, consistent with "a successful run need not use all available fuel". |
| T2 #6 (note) | true | note | The six files have 76 `theorem`s: 75 public, plus `private expect_ite_one_split` (`Hopping.lean:194`). The log has exactly 75 entries, each name matching a public theorem, all with axioms among `propext`/`Classical.choice`/`Quot.sound`. Three entries are wrapped over lines. |

### Note 5: the three invariants

Write `r = (o, obsA, obsB)` for an output of `execT fuel A B`, where `obsA = r.2.1 : Obs M₂` belongs to this call's first mover, `M_A = obsA.received` and `M_B = obsB.received`. The proof is by induction on `fuel`, generalizing `M₁ M₂ α β A B` as in `execT_outcome`.
- **Return branch (any fuel).** `M_A = M_B = []`, and `o` is `done` or `sentAfterEnd`. All three invariants hold.
- **Blocked send (fuel 0).** `o = outOfFuel` and `M_A = M_B = []`, so the sum is 0, which equals the fuel.
- **Send at fuel+1.** The IH is about `r' = execT fuel (B (some m)) k`, whose first mover is the original B. Write `M₁' = r'.2.1.received` (B's) and `M₂' = r'.2.2.received` (A's). The output has `M_A = M₂'` and `M_B = m :: M₁'`. So:
  - `|M_A| + |M_B| = |M₁'| + |M₂'| + 1 ≤ fuel + 1`;
  - from `|M₂'| ∈ {|M₁'|, |M₁'|+1}`, `|M_B| = |M₁'| + 1 ∈ {|M_A| + 1, |M_A|}`;
  - `o = r'.1.swap`, and `swap` fixes `outOfFuel`, so `outOfFuel` gives a sum of `fuel + 1`.

**Off-by-one check.**
- The alternation stays oriented to the call's first mover, because the IH is applied with the roles swapped and the `::` lands on the third component.
- An inductive invariant that pinned "A" to the second component, or omitted the `mk.1 ::`, would fail.
- The auditor's glossary ("original first and second movers") matches the code.
- Equivalently, `|M_B| − |M_A| = (|M_A| + |M_B|) mod 2`.

**Practical point.** `OracleComp.AllOutputs` lives in `Hopping.lean:69`, and `Protocols.lean` imports only `Probability` (:5). Stating these invariants in `Protocols.lean` needs `AllOutputs` moved down to `OracleComp.lean` (it is generic in `spec`) or a new import.

## Missed by the auditor

None of these is a blocker or a major.
1. **M2's correct source (minor; part of M2).** Covered in the table: [PS10, p. 73, Lemma 73.8] states the relation that `guessAdv_eq_half_advantage` proves exactly. The code says [PS10] does not state it.
   - The same exact identity already exists as `predict_eq` (`Asymptotic/Ensembles.lean:580`, on `uprob` over seed spaces). This parallel is undisclosed (note), and it falls under B2 in the way `prob_mono`/`uprob_mono` did in round 1.
2. **The game count of `exists_advantage_hybrid_gap` (minor; fold into finding 4).** The docstring says "`n > 0` games"; there are `n + 1` games and `n` hops.
3. **[BR06] location (minor; fold into #8).** `Hopping.lean:44–45` and `:288` have no lemma number, the same `policy.md` §2 gap as [Sho04].
4. **The design note repeats findings 1–2 (note).** `S2-game-framework.md:49–50` says "follow D8's reading" and "Views are recorded by the executor". Fix it together with the code.
5. **Small regressions and leftovers (notes).**
   - `exec_zero` lost `@[simp]`: it was `@[simp] theorem exec_zero` at `597eef43`. No downstream user exists in the main checkout.
   - `[Sho04]` remains in `Advantage.lean`'s references with no citing declaration.

## Proposed fixes (true or partly true items)

- **Finding 1**
  - **`Protocols.lean:125–129`**, replace the last sentence with: "**Relation to D8.** This executor is broader than D8 in two respects: a party may return early (D8 fixes the number of messages), and a party's output is a separate return value, computed after its last activation and possibly after fresh coins on closure. In D8 a party's output is its next-message function on its complete history, so the last sender's output equals its last message (`Protocol.outV_eq_getLast_of_moverIsV`). D8 executions are the executions of embedded strategies (each samples its whole tape first, sends `next` on its scheduled turns, and returns `next` on its complete history); agreement with D8 is claimed only for that class (bridge B4)."
  - **`:22–23`**: "Following D8, both parties have outputs: the waiting party is activated once more …". Drop "As in".
  - **Facade `Games.lean:42–43`**: "executions in a coroutine model that contains D8's (bridge B4), and traced executions recording received messages and coin draws."
  - **B4.** State it for embedded strategies only.
- **Finding 2**
  - **`Protocols.lean:28–33`**: "**Traces.** `Party.execT` returns, beside the outcome, each party's received messages (the second mover's first message first) and the coin draws it executed (`Party.Obs`). A [PS10, §4.4] view `(x, z, r, M)` contains the whole random tape `r`, including bits never read. It is recovered from the trace only for parties that sample their whole tape first, as the embedding of a D8 strategy does (B4). Inputs and auxiliary inputs are Lean parameters of the party."
  - **`:198`**: change the tag to "[PS10, §4.4] (the received messages of a view; its random tape for parties that sample it first)".
- **Finding 3** (`:138`): "With no fuel, the first mover runs until it returns or tries to send. If it returns, the waiting party is closed (`endWith`): activated with `none`, it may draw coins, and the outcome is `done` if it returns and `sentAfterEnd` if it sends. If the first mover tries to send, the outcome is `outOfFuel` and the waiting party never runs." Optionally restore `@[simp]`.
- **Finding 4 and the missed count** (`Advantage.lean:106–108`): "**The hybrid lemma:** along a chain `G 0, …, G n` of `n > 0` hops (`n + 1` games), some neighbouring pair has advantage at least `advantage (G 0) (G n) / n`. [PS10, Lemma 71.6] **Deviation:** sharper than the source, which takes `m` distributions (`m − 1` hops), a threshold `ε < |g₁ − g_m|`, and concludes `> ε/m`. Here the divisor is the number of hops and the bound is the exact endpoint advantage. The source's form follows with `m = n + 1`. It is the concrete layer's `exists_hybrid_gap` for the acceptance probabilities." Make the same change in the module text at `:38` ("a `1/n` share, for `n` hops").
- **M2**
  - **`Advantage.lean:149–151`**: "**Guessing versus distinguishing:** `|Pr[win] − ½| = |Pr[G 1 = 1] − Pr[G 0 = 1]| / 2`. This is the identity behind [PS10, §3.1.1, p. 73, and Lemma 73.8]: a predictor with success `½ + δ` is a distinguisher with advantage `2δ`, and conversely. **Deviation:** stated exactly, at one parameter, for whole games; the absolute value replaces the source's 'without loss of generality' complement of the distinguisher. [PS10, Def 168.1] is stated in the distinguishing form only, with its experiments `IND_0`, `IND_1` as the games `G false`, `G true`. The concrete layer's counterpart is `predict_eq`."
  - **`:116`**: "… win if its output is `b`: the prediction experiment `b ← {0,1}; t ← X^b : A(t) = b` of [PS10, Lemma 73.8], with `G b` the whole game for challenge bit `b`."
  - **`accept_guessGame` (`:123`)**: tag it "[PS10, proof of Lemma 73.8]".
  - **Reference line `:44–46`**: "§3.1 (Def 69.4), Lemma 71.6 (the hybrid lemma), Lemma 73.8 (the prediction lemma) and Definition 168.1 (the experiments `IND_b` for a fixed challenge bit)."
- **#8**
  - **[Sho04].** Once someone with access confirms it, pin the revision in `Hopping.lean:46–48`: "IACR ePrint 2004/332, revision of 18 January 2006 (https://www.shoup.net/papers/games.pdf)". Cite "[Sho04, §1.1, Lemma 1]" at `:127`, and give `:288` its own location or drop it.
  - **[BR06].** Do the same for its fundamental lemma; the auditor names Lemma 2 of ePrint 2004/331, which is unverified.
  - **`Advantage.lean:47–48`.** Remove `[Sho04]`, or cite it from a declaration.
- **M4**: in `S2-game-framework.md:49–50`, apply the finding 1 and 2 wording ("a coroutine model containing D8's"; "traces of received messages and executed draws; full views for parties that sample their tape first").
- **Note 5 (optional)**: move `OracleComp.AllOutputs` to `OracleComp.lean`, then prove, for all `fuel A B`, that `(execT fuel A B).AllOutputs` holds of the three relations above. Generalize over the types, as `execT_outcome` does.
- **Note 6**: in the pack, say "all 75 public theorems; the private helper `expect_ite_one_split` is covered transitively", or print it separately.

## Not verified

- **Shoup's location and date** (18 January 2006, §1.1, Lemma 1, p. 3). WebFetch of `https://www.shoup.net/papers/games.pdf` failed: `www.shoup.net` does not resolve, because it is outside the session's allowed network domains. `https://eprint.iacr.org/2004/332.pdf` returned HTTP 403. To check it, `www.shoup.net` has to be allowed in the session's network settings.
- **The [BR06] lemma number** (ePrint 2004/331, Lemma 2). Not attempted, since the same network limits apply.
- **The VCVio headers and counterpart names at commit `90549893`.** GitHub access in this session is limited to `shilun-allan-li/tcslib`. I relied on the round 1 review's verified reading, which `CITATION-VCVio.md` matches.
- **Lean.** No Lean was run, including the elaboration, axiom and lint attestations. The Python model corroborates; it does not certify.
- **The design note at the audited state.** I read it at the main checkout's current head (`7bd1a019`), not as frozen in the round 2 bundle.
