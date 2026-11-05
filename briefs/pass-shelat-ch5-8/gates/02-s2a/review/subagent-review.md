# Gate 02 / S2a: review of the external auditor's findings

**Summary.** Of the 12 findings, 11 are **true** and 1 is **partly true** (#1: the defect is real, but the "source-faithful" fix the auditor proposes does not exist). None is false. **No severity changes.** #1 stays a blocker, but for a different reason: its fix changes the public type of `exec`, not because it is unfaithful to the source as literally written. **Human decisions are needed on #1** (adopting D8's reading of the idle party's output; F-2 with Frederick), **#4** (extending D8's strict/truncated simulators to Thm 175.1, or adding expected time), and **#10** (reuse by import, or ledger entry DL-2). Before the gate closes, #1, #2 and #3 need code or docstring changes, and #4 needs a recorded ruling.

**How this was checked.** Every Lean reference was read at head `597eef43` in the worktree. PS10 text was extracted from PDF pp. 82–84, 126–128, 133–136, 166–169, 180–182 and 186–189 (SHA-256 matches the auditor's). The auditor's examples A4, A5, A7 and A8, and the replacement hypothesis proposed under #3, were checked by an exact-rational transcription of the definitions (`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/gate02-review/scripts/model.py`). All numbers match. VCVio headers and counterparts were read at the pinned commit `90549893` (fetched read-only from `Verified-zkEVM/VCVio`). **Not verified:** Shoup's section numbers (shoup.net and ePrint were unreachable from this session). No Lean was run. The "Lean checks" list at the end says what to run.

The S2b branch was also checked. Its `Bridges/` and `Machines.lean` do not use `Party`, `exec`, `finish`, `prob_eq_until_bad`, `identical_until_bad` or `advantage_hybrid`. So none of the API changes below breaks existing code.

---

## #1 (blocker): `Party.finish` and `Party.exec` versus PS10 §4.4

**Claim.** `exec` does not implement §4.4. After the active party returns, it drains the waiting party. That party can draw fresh coins and make any number of sends, all silently answered `none` and discarded, and the run is still reported as a success.

**Check: partly true.**
- *The defect is true.*
  - In `Protocols.lean:75–78`, `finish` answers every exchange with `none` and discards the outgoing message.
  - In `Protocols.lean:88`, `exec` reports `some (a, b)` whatever `finish` did.
  - A5 reproduces: `exec 1 (pure a) (fun _ => K 100)` gives `some (a, 100)` after 100 discarded sends.
  - The docstrings of `exchangeSpec`, `Party` and `exec` cite `[PS10, §4.4]` without a deviation note, which breaks the deviation rule in `policy.md` §2.
- *The auditor's remedy rests on a false premise.* §4.4 (book p. 115) says "A round ends with the active machine either halting —in which case the protocol ends— or by it entering a special idle state". A machine's output is defined only "upon halting" (p. 114). So under the literal rule, the idle party never gets an output. Yet the source uses both outputs: Def 155.1 (book p. 156) needs `out_B(e)` jointly with `view_A(e)` and `out_A(e)` jointly with `view_B(e)`, and Def 116.1 needs `out_V` even when the prover moves last.
- A "source-faithful stopping semantics" that never activates the waiting party therefore cannot define Def 155.1. The ch. 2–4 layer already settled this in its D8 deviation (`ZeroKnowledge/Interaction.lean:27–33`, `outV`/`outP` at :340–345): the idle party's output is its next-message function applied to its complete history, which is one more activation after the last message.
- So some post-end activation is necessary. The defect is that this activation is **unbounded and silent**: sends after the end are hidden from every observer of the output.

**Severity.** Keep **blocker**, on API grounds. The fix changes `finish` and the result type of `exec`. B4 (the bridge to his `Protocol.exec`) and Def 155.1 (prong B) are to be stated against that type, and the design note's §8 says B4 is waiting for this gate.

**Disposition: fix (changes the public API).** The minimal sound design aligns with D8 and makes violations observable:

```lean
/-- The outcome of an execution: both outputs, the message budget ran out, or a party sent a
message after its counterpart had returned. -/
inductive ExecOutcome (α β : Type) : Type where
  | done (a : α) (b : β)
  | outOfFuel
  | sentAfterEnd

/-- Exchange the roles in an outcome. -/
def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
  | .done a b => .done b a
  | .outOfFuel => .outOfFuel
  | .sentAfterEnd => .sentAfterEnd

/-- Close a party whose counterpart has returned: its pending send is answered `none`; it may
still draw coins, and must then return without sending (`none` if it sends). -/
def close : Party Out In α → ProbComp (Option α)          -- replaces `finish`
  | .pure a => .pure (some a)
  | .query (.inl ()) _ _ => .pure none
  | .query (.inr j) x k => .query j x (fun y => close (k y))

def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β) :=
  (close (B none)).bind fun ob => .pure (match ob with
    | some b => .done a b
    | none => .sentAfterEnd)

/-- At most `fuel` messages are delivered. -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
  | 0, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B)
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))
```

The design in more detail:
- **Fuel.** A return is no longer charged against `fuel`, so `fuel` is exactly the message budget. This also fixes #5. For example, `exec 1 (send m (fun _ => pure a)) (fun _ => pure b) = pure (.done a b)`, and `exec 0 (pure a) B` succeeds.
- **Docstring deviation note for `exec`.** "The text ends the protocol when the active machine halts and defines outputs only on halting, so the idle party has none, while Defs 116.1 and 155.1 use both outputs. As in D8 (`Interaction.lean`), the idle party is activated once more, with `none`: it may draw coins, but a send is reported as `sentAfterEnd`. Early returns are allowed, whereas D8 fixes the number of messages."
- **Laws to add now:**
  - the A4 and A5 instances as `example`s;
  - monotonicity in fuel: for every `o ≠ .outOfFuel`, `prob (exec n A B) (· = o) ≤ prob (exec (n+1) A B) (· = o)`.
- **B4's correspondence theorem** (S2b): a `Strategy` induces a party that draws its whole tape up front (`2^k` outcomes, so the sampling is dyadic, see #11) and makes its scheduled moves. For such parties, `exec rounds` is `.done (outP, outV)` with exactly the law of his `Protocol.exec`.
- **A smaller variant** keeps `Option (α × β)` and sends both failure modes to `none`. It is acceptable, but a timeout can then no longer be told apart from a violation. That distinction is needed for "the honest execution completes with probability 1" lemmas.

**Human decision.**
1. Adopt D8's reading (one final activation, no sends) as the Games execution semantics.
2. Allow early returns at all.

Both should be agreed with Frederick under F-2, since B4 must match his `Protocol.exec`.

---

## #2 (major): views read from a party's own oracle log

**Claim.** The module docstring's recipe, "a party's view … is the log of its own oracle answers", loses the second mover's first message. That message is the argument of `B (some m)`, not an oracle answer.

**Check: true.**
- `Protocols.lean:21–22` states the recipe.
- `exec`, at `Protocols.lean:84` and :89, delivers A's first message by applying `B` to it. No exchange query of B is answered with it.
- This is not only the case where B returns at once (A6). For every second mover, the first message is missing from its own log.
- Two further gaps:
  - `exec` is not built from `simulate`, so `withLog` cannot be applied to it. The only route under the current API is to wrap each party separately, as `simulate passthrough.withLog`, and that route still misses the first message.
  - The docstring's view omits the party's input and auxiliary input, which §4.4's views `(x, z, r, M)` include (book p. 115). Design §6 does include the input.
- A6's privacy counterexample is valid.

**Severity.** **Major** is right. It is a wrong claim in the trusted surface, no `View` exists yet, and S2b would follow the recipe.

**Disposition: fix.**
1. **Docstring, now (no API change).** Replace `Protocols.lean:21–22` with: "a party's view (its input, auxiliary input, coins and the messages delivered to it, starting with the second mover's first message) is recorded by the executor (`execT`). It is not the log of the party's own oracle answers, which misses the second mover's first message." Correct design §6 the same way, including its line 164, "the transcript comes from logging handlers".
2. **Design: a traced execution that records deliveries at the executor** (new API, best landed together with #1):
   - **Observations.** `structure Obs (In : Type) where received : List In; coins : List (Σ m : ℕ, Fin (m + 1))`.
   - **Traced steps.** `stepT` and `closeT` work like `step` and `close`, and also return the coins drawn along the way.
   - **Traced execution.** `execT n A B : ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)`. When the active party sends `m`, the executor appends `m` to the receiver's `received` before resuming it, so the second mover's first message comes first. Each segment's coins are appended to the active party's `coins`, including coins drawn in `closeT`.
   - **Laws:**
     - projection: `(execT n A B).map Prod.fst = exec n A B`;
     - the second mover's `received` starts with A's first message;
     - `received.length` of the two parties adds up to the number of messages delivered.
   - **Views.** Parties take inputs as Lean parameters (`A : X → Z → Party …`). A view is `(x, z, o.coins, o.received)`.
   - **Def 155.1's joint law** is a single map over a single `execT`: `(execT n (A x) (B y)).map fun (o, oA, _) => (viewA x oA, o.outB?)`. This keeps the view and the other party's output jointly distributed, which is what the auditor asked for.
   - **Coins.** Lazily drawn coins differ from §4.4's fixed tape only by unused, independent bits. B4's induced parties draw the tape up front, so their `coins` *is* the tape.

---

## #3 (major): identical until bad requires equal computations, including on the call that sets `bad`

**Claim.** `hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s` requires the two handlers to be equal as computations on every call that starts in a good state, including the branch on which that call raises the flag. Standard hops diverge on exactly that branch.

**Check: true.**
- See `Hopping.lean:194` and :242.
- A7 reproduces:
  - Pr₀[answer] = 0 and Pr₁[answer] = 1/2;
  - Pr[bad] = 1/2 in both games;
  - yet the two handler computations differ at the good state.
- The case the pack's Q5 names fails in the same way. In the repeated-nonce hop of Thm 168.2 (book p. 169: "the encryption oracle happens to have sampled the same r₀ or r₁ in some previous query"), the random-function game reuses the stored pad on a collision, while the one-time-pad game draws a fresh one. The two differ only on the branch that sets `bad`, which `hagree` forbids.
- BR06's notion ("code differs only in statements that follow the setting of bad") allows exactly this divergence. So the lemma is narrower than the `[BR06, Lemma 2]` it cites, and it carries no deviation note.
- The second restriction is also true: an equal-law handler with an extra unused draw is a different tree.
- A8 confirms that stickiness must stay: the gap is 1 while the final bad probability is 0.

**Severity.** **Major** is right. The statement is not wrong, but it is unusable for the hops the design (§5.3) and probe P-S2-3 rely on. The fix adds to the API; it does not withdraw anything.

**Disposition: fix (generalize the hypothesis; the conclusions are unchanged).** Replace `hagree` in both `prob_eq_until_bad` and `identical_until_bad` with equality of the **off-bad laws** of the successor:

```lean
-- old
(hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s)
-- new  (add `[DecidablePred bad]`, or state the indicator classically)
(hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
    ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
      ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
```

What the new hypothesis gains:
- It accepts A7: both off-bad laws are {(false, false) ↦ 1/2}, checked in `model.py`.
- It accepts the Thm 168.2 hop, and handlers that are equal in law.
- It is implied by the old hypothesis. Keep the old statements as corollaries, `prob_eq_until_bad_of_eq` and `identical_until_bad_of_eq`.

**Proof sketch** (a small change to the existing proof). Induct on `c`, generalizing `s`, with both conjuncts.
- At a query from a good `s`, write `F_b(ys)` for the continuation's probability of "Q and good at the end".
- On a bad successor, `F_b(ys)` is 0 by stickiness (`simulate_allOutputs_bad`). So `E₀[F₀] = E₀[1_{¬bad} F₀]`.
- This equals `E₀[1_{¬bad} F₁]` by the induction hypothesis on good successors.
- It equals `E₁[1_{¬bad} F₁]` by the new hypothesis with `g := F₁`.
- That is `E₁[F₁]` by stickiness again.
- For the bad conjunct: `E_b[1_bad] = 1 − E_b[1_{¬bad}·1]`, which is equal for `b = 0, 1` by the hypothesis with `g := 1`. Add the off-bad part as above.

**Docstring deviation note.** "BR06 assumes syntactic identity up to `bad ← true`. Here the hypothesis is semantic: from a good state, the two handlers give the same law to good successors and may differ arbitrarily on bad ones, including in the call that raises the flag. Stickiness is required (without it the bound fails)."

**API.** No downstream consumer exists, so the general form can take the existing names. If the names are kept for the narrow form instead, the generalization is purely additive.

---

## #4 (major): expected-polynomial-time simulators

**Claim.** No `ProbComp` can express the retry loops of the source's expected-p.p.t. simulators. So the framework, with its planned strict-machine bridge, does not cover Thm 175.1 in the source's generality.

**Check: true.**
- `unifSpec` has finite branching (`Fin (m+1)`). A well-founded tree with finite branching is finite, so every `ProbComp` has finite support and a bounded number of draws. A10 is correct.
- Def 121.2 (book pp. 121–122) "only require[s] it to be an expected p.p.t".
- Algorithm 123.4, step 4, says "restart the emulation of V* and repeat".
- The proof of Thm 175.1 (book p. 176) argues "by linearity of expectations, the expected running-time of SQ is polynomial".
- Design §6 (B4) says Thm 175.1 "is stated in the framework with a proved equivalence to his ZK" and is silent on expected time.
- **However, the debt is already recorded.** The campaign inventory, `inventory-ch5-8.md:130`, says: "source assumes **expected** poly-time simulators. His are strict PPT (his D8) or truncated with abort (`PerfectZKAbort`), so the composition must carry the truncation error". The pack did not include the inventory, so the auditor reasonably rated the debt as unacknowledged.
- The ZK layer that B4 targets is itself strict: see `ZeroKnowledge/Defs.lean:32–35` ("strict PPT simulators … the rewinding simulators … are truncated and the theorems become statistical").

**Severity.** **Major** is right, as debt that needs explicit human acknowledgment. The inventory is a planning draft, not a ruling, and the S2 design note does not carry the deviation.

**Disposition: record, plus a human ruling. No change to S2a code.** The options:

**(a) Strict and truncated simulators, with an explicit error term, as a declared deviation (D8 carried into ch. 7).** Thm 175.1 is stated against his definitions:
- `ZK ⇒ ZK`, with strict simulators. The standard hybrid proof works and takes Q·poly time.
- `StatZK δ ⇒ StatZK (Q·δ)`.
- `PerfectZK ⇒ PerfectZK`.
- `PerfectZKAbort ⇒ StatZK (Q(n)·2^{-k(n)})`. This works through the k-fold truncated retry of the abort simulator, which is `2^{-k}`-close per session; with `k = |x|` the error is negligible.

Abort simulators do not compose directly, because the abort probability compounds. The "perfect" half of Thm 175.1 therefore becomes statistical for protocols such as GI, matching what D8 did for Thm 122.3. Expressivity: a strict simulator is a finite `ProbComp`, or a strict NUPPT via B3. Cost: low.

**(b) Unbounded iteration in the framework** (`repeatUntil` or a coinductive/partial `ProbComp`):
- The semantics must become a limit, a sub-probability over `ℝ≥0∞` or a measure. That reverses ruling R-1 ("finite sum … no PMF, no ℝ≥0∞").
- "Expected p.p.t." also needs an expected-time machine class, which Frederick's `NUPPT` layer does not have, and his ZK definitions would have to change (F-2).
- Cost: high, and it crosses ownership.

**(c) An extensional middle ground.** An expected-time simulator is represented by its truncations, `S : ℕ → ProbComp (Option V)`, with:
- agreement where `S k` already succeeds;
- `Pr[S k = none] → 0`;
- a bounded expected-cost series.

"Perfect" becomes a limit equality. This keeps the finite core and represents Algorithm 123.4's *law* faithfully, but it still needs an expected-time machine notion for the "p.p.t." part. Cost: medium. It is a possible later addition.

**Recommendation: (a).** Add the deviation paragraph to design §6 (B4), to the facade's docstring, and later to Thm 175.1's docstring. Cite `inventory-ch5-8.md:130` and D8.

**Human decision.** Accept D8's strict/truncated simulators for ch. 7, including the statistical weakening of the perfect case, or commission (b) or (c).

---

## #5 (minor): fuel is not the message count

**Claim.** "With at most `fuel` messages" is off by one: a one-message protocol needs fuel 2, two immediate returns need fuel 1, and `finish` is not charged.

**Check: true.**
- The claim appears at `Protocols.lean:34–35` and :80, and in design §6 ("the protocol's message count").
- Reproduced: `exec 1 A B = none` and `exec 2 A B = some (a, b)` for A4's one-message protocol; `exec 0 (pure a) B = none` and `exec 1 (pure a) B = some (a, b)`.
- Each level consumes fuel whether the active party sends or returns, so a run with `r` messages needs `r + 1`.

**Severity.** Minor.

**Disposition: fix.**
- **Preferred.** The #1 redefinition makes `fuel` exactly the message budget, because a return is not charged. That is a behavioral change inside an API that #1 changes anyway.
- **If #1's redefinition is not adopted** (docstring only, no API change): "at most `fuel` activations: at most `fuel − 1` messages, then a return; the post-return drain is not charged".

Either way, add the fuel-monotonicity lemma from #1.

---

## #6 (minor): "a finite tree"

**Claim.** `OracleComp.lean:17–18` calls every oracle computation a finite tree. With `rng i = ℕ` it can have infinitely many branches of unbounded depth.

**Check: true.** A11 is a legal term: the `OracleSpec` fields `dom` and `rng` are unrestricted (`OracleComp.lean:66–70`). `Probability.lean:24` ("finite tree with finite branching") is correct for `ProbComp`.

**Severity.** Minor.

**Disposition: fix (docstring only, no API change).**
- Old: "a finite tree whose inner nodes are queries, with one subtree per possible answer."
- New: "a well-founded tree (every run makes finitely many queries) whose inner nodes are queries, with one subtree per possible answer; with finite answer types, as for `ProbComp`, the tree is finite."

---

## #7 (minor): VCVio declaration tags and the header sentence

**Claim.** `ProbComp`, `sampleFin`, `QueryImpl.comp` and `simulate_comp` follow identifiable VCVio constructions but carry no tags. `CITATION-VCVio.md` says the headers read "VCVio Contributors", which is false.

**Check: true, verified at the pinned commit.**
- **The constructions match.**
  - `ProbComp/Basic.lean:31` has `abbrev ProbComp : Type → Type := OracleComp unifSpec`; locally this is `Probability.lean:71`.
  - :45 has `def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) := unifSpec.query n`; locally `sampleFin`, `Probability.lean:78`.
  - `SimSemantics/QueryImpl/Compose.lean:35` has `QueryImpl.compose` and :48 has `simulateQ_compose`; locally `Simulate.lean:137` and :148.
  - None of the four local declarations has a tag. `CITATION-VCVio.md` §"Declaration level" requires one.
- **The headers name people.**
  - `OracleComp.lean`, `ProbComp/Basic.lean` and `QueryImpl/Compose.lean`: "Copyright (c) 2024 Devon Tuma … Authors: Devon Tuma, Quang Dao".
  - `OracleSpec.lean` and `OracleQuery.lean`: "Authors: Devon Tuma".
  - `LoggingOracle/Core.lean`: "Authors: Devon Tuma, Quang Dao, Alexander Hicks".
- **Licence and commit are as cited.** The licence is Apache 2.0, and the commit is dated 2026-11-04.

**Severity.** Minor.

**Disposition: fix (docstrings and design documents only, no API change).**
- **Tags to add:**
  - `ProbComp`: `[VCVio, OracleComp/ProbComp/Basic]`;
  - `sampleFin`: `[VCVio, OracleComp/ProbComp/Basic (uniformFin)]`;
  - `QueryImpl.comp`: `[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)]`;
  - `simulate_comp`: `[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]`.
- **Reference block.** Add `OracleComp/ProbComp/Basic.lean` to its module list. The existing `unifSpec` tag already cites `OracleComp/ProbComp`, which the block does not list. The block appears in 7 Lean files and 2 design documents.
- **`CITATION-VCVio.md:41`.** Replace "The file headers say 'VCVio Contributors'" with the actual names, per module, as above.
- **Optional.** Update the URL to `https://github.com/Verified-zkEVM/VCVio`; the old one redirects.

---

## #8 (minor): source locations

**Claim.** PS10's hybrid lemma is Lemma 71.6, not "Lemma 70.2". Shoup's difference lemma is Lemma 1 in §1.1, not §4.

**Check: true for PS10, verified. Shoup not verified here.**
- PDF p. 83 (book p. 71) reads ".Lemma 71.6 (Hybrid Lemma)", and its proof continues on p. 72.
- Book p. 70 holds "Figure 70.2: A game parameterized by n".
- `advantage_hybrid` is the telescoping inequality displayed in the proof. The lemma itself is the existential `∃ i, D distinguishes Xⁱ, Xⁱ⁺¹ with ε/m`.
- The concrete layer already cites PS10 correctly: `Asymptotic/Ensembles.lean:410` has `hybrid_lemma` "[PS10, Lemma 71.6]".
- Separately, `Hopping.lean:45` assigns "§4" to the difference lemma while :227 cites "[Sho04, §4]" for the fundamental lemma. Both cannot be right.
- Shoup's section numbers could not be checked: shoup.net was not reachable and ePrint was behind a challenge.

**Severity.** Minor.

**Disposition: fix (docstrings only).**
- `Advantage.lean:43` and :94: "Lemma 70.2" → "Lemma 71.6", with this note at :94: "the telescoping inequality in the proof of [PS10, Lemma 71.6]". See also #10, which adds the existential form.
- Shoup: pin the revision (for example, "revised 18 January 2006"), then re-check §1.1 / Lemma 1 and the §3/§4 references in `Advantage.lean:45`, `Hopping.lean:45` and :227 against that revision.

---

## #9 (minor): two docstrings that do not state their theorems

**Claim.** `accept_nonneg` says "between zero and one" but proves only `0 ≤`. The docstring of `expect_mono_of_allOutputs` states no inequality.

**Check: true.** `Advantage.lean:65–66` proves `0 ≤ accept G`. `Hopping.lean:95–97` says "only depends on the function's values at the possible outputs", but the theorem is `c.AllOutputs P → (∀ a, P a → f a ≤ g a) → expect c f ≤ expect c g`.

**Severity.** Minor.

**Disposition: fix (docstrings only).**
- `accept_nonneg`: "An acceptance probability is nonnegative."
- `expect_mono_of_allOutputs`: "If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`, then the expectation of `f` over `c` is at most that of `g`."

---

## #10 (minor): `advantage_hybrid` duplicates `abs_sub_le_sum_hybrids`

**Claim.** `advantage_hybrid` is the existing `abs_sub_le_sum_hybrids` with `P i = accept (G i)`, and this duplication is not disclosed.

**Check: true. It is a duplicate statement, not a copied proof.**
- `Foundations/Probability.lean:211` has `abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) : |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)|`.
- `advantage G₀ G₁ := |accept G₀ - accept G₁|` (`Advantage.lean:63`). So `advantage_hybrid G n` (:97) is, after unfolding `advantage`, exactly `abs_sub_le_sum_hybrids (fun i => accept (G i)) n`.
- The proofs differ textually: `(advantage_triangle _ (G n) _).trans (by linarith)` versus `(abs_sub_le _ _ _).trans (add_le_add_right ih _)`. They are the same induction.
- It is not among B1–B2 or the advertised `advantage`/`distAdv` correspondence, and `duplication-ledger.md` has only DL-1.
- The concrete layer already reuses this lemma for PS10's form: `Asymptotic/Ensembles.lean:415` has `hybrid_lemma := exists_hybrid_gap (fun i => acceptProb (X i) D) hm`.

**Severity.** Minor.

**Disposition (recommended): reuse via import. No public API change; one theorem added.**
- `Foundations/Probability.lean` imports only Mathlib (BigOperators, Fintype.Prod, Real.Basic, Cardinal.Finite, Linarith). S2b's `Bridges/Experiments.lean` already depends on the concrete layer.
- In `Games/Advantage.lean`:

```lean
import TCSlib.Cryptography.Foundations.Probability
...
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
  abs_sub_le_sum_hybrids (fun i => accept (G i)) n

/-- [PS10, Lemma 71.6] -/
theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
  exists_hybrid_gap (fun i => accept (G i)) hn
```

- This invalidates attestation 4 of the pack ("No ch. 2–4 module is imported"). Re-run the name screen.
- **Alternative**, if the maintainer wants `Games` free of concrete-layer imports: add **DL-2** to `duplication-ledger.md`. New: `Games.advantage_hybrid`; existing: `TCSlib.Cryptography.abs_sub_le_sum_hybrids`. Status: a duplicate statement (an instance), with an independent proof. Resolution: a one-line corollary at integration. The ledger requires the user's acknowledgment, so this is a **human decision**.
- Other parallel lemmas are on different objects and are covered by the B2 bridge, so they are not ledger duplicates: `prob_mono`/`uprob_mono`, `prob_or_le`/`uprob_or_le`, `prob_not`/`uprob_not`.

---

## #11 (note): exact non-dyadic sampling is not fair-bit-efficient

**Check: true.** `sampleFin 2` has probability 1/3. A machine using at most `k` fair bits has probabilities `a/2^k`, and `3a = 2^k` has no solution. This is relevant to B3, and to source items that sample from non-dyadic sets such as `S_n` in Algorithm 123.4 (π ← Sₙ) and `Z_p`.

**Disposition: record. No S2a change.** S2b's machine bridge should do one of two things:
- restrict machine-induced games to dyadic sampling (bit strings); or
- reuse the concrete layer's truncated rejection sampler (`Asymptotic/Sampling.lean:607`, `rejectionSample`, and `statClose_rejectionSample`) with its explicit statistical term. This is the same pattern as #4(a).

---

## #12 (note): bridges and efficiency are deferred

**Check: true.** `simulate_comp` and `simulate_costBoundedBy` are semantic and query-count statements. Polynomial-time closure, oracle substitution, and protocol/ZK equivalence remain open obligations (design §§5.4, 7, 8). `uprob` on an empty type is `0`, so B2 needs `Nonempty`, as the auditor says.

**Disposition: record**, as already scheduled. No new obligation.

---

## Missed by the auditor

1. **The collision bound is oversold (minor).** `Hopping.lean:21–23` presents `prob_mem_le` as "the bad event of … a repeated nonce in [PS10, Thm 168.2]". The theorem covers one fresh draw against a list fixed beforehand. Thm 168.2's event (book p. 169) also covers later oracle nonces hitting the challenge nonce, which needs a union bound across adaptive steps. The auditor raised this in Q6 but did not number it.
   - Fix: reword the docstring ("one fresh draw against an earlier list; the adaptive repeated-nonce bound is a union of such steps").
   - Schedule the adaptive lemma, the auditor's sanity item 6.
2. **Results without source tags (minor; `policy.md` §2 says "anything a reader would recognize as 'a result' may not [omit the tag]").** These declarations have none:
   - `prob_mem_le`;
   - `guessGame`, `guessAdv`, `accept_guessGame`, `guessAdv_eq_half_advantage`;
   - `identical_until_bad` cites BR06, but the restriction needs the #3 deviation note.
3. **No averaging over the initial state (sanity lemma).** `identical_until_bad` starts from a fixed good state, but every game first samples its key or initial state. Missing corollary: if `init.AllOutputs (¬ bad ·)`, then `|Pr[init >>= sim₀ c ∈ p] − Pr[init >>= sim₁ c ∈ p]| ≤ Pr[init >>= sim₀ c ∈ bad]`. It follows from `prob_bind`, `expect_mono_of_allOutputs` and linearity.
4. **The S2 design note is out of sync with the code (note).**
   - §9 gives the namespace as `TCSlib.Cryptography`; the code uses `TCSlib.Cryptography.Games`.
   - §3 calls the query bound `IsQueryBound c qb`; the code has `CostBoundedBy cost c q`.
   - §9 lists `OracleSpec.lean` as a separate file; it lives inside `OracleComp.lean`.
   - §6 says "fuel is the protocol's message count" (#5) and that "the transcript comes from logging handlers" (#2).
   - Update the note when #1–#5 land.
5. **Context the auditor lacked.** `inventory-ch5-8.md:130` already records #4's debt. The disposition of #4 should cite it, and future packs should include the inventory rows for any source item they ask about.

## Lean checks for the maintainer (one process at a time)

- **#1.** Elaborate `ExecOutcome`, `close`, `endWith` and `exec` as above, then check these `example`s by `rfl`, with concrete types such as `Unit`/`Bool`:
  - `exec 1 (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) = .pure (.done a b)`;
  - `exec 0 (.pure a) (fun _ => .pure b) = .pure (.done a b)`;
  - `exec 1 (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) = .pure .sentAfterEnd`.
- **#3.** Prove the generalized `prob_eq_until_bad` and `identical_until_bad` from the sketch, and derive the `_of_eq` corollaries by rewriting.
  - Optionally add A7 as an `example` that satisfies the new hypothesis. `hagree` should reduce to a two-term sum (`expect_query`, `Fin.sum_univ_two`). This is untested.
- **#10.** Check that `advantage_hybrid := abs_sub_le_sum_hybrids (fun i => accept (G i)) n` elaborates; it is a definitional unfolding of `advantage`. Then re-run `name-screen` with the new import, under `open TCSlib.Cryptography TCSlib.Cryptography.Games`.
- **#2.** When `execT` exists, prove the projection law `(execT n A B).map Prod.fst = exec n A B` by induction on `n`.
