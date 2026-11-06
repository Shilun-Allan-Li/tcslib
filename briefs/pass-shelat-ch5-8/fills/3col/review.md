# Review of the 3-colouring fill brief (`fills/3col/brief.md`, units col-a, col-b)

**Verdict: issue after edits.** col-a can be issued once the edits below are in. col-b has one
blocker (B1): `distAdv`'s published equation (P7) is still missing at #210's head, and steps 6
and 7 (and therefore `col_zk`) cannot be done without it.

Checked against PR #210's head `fff0430c7c9db136e60ed14b069e972c2ea56fc8` (worktree `$SP/wt-e1`,
`git rev-parse HEAD`), olean tree `$SP/e1-oleans`, one Lean process at a time, no build. Logs are
under `$SP/review/3col/`, where `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.
The probe files `Probe/ReviewColA.lean` and `Probe/ReviewColB.lean` were removed after the runs.
Their sources are kept in the logs.

## Findings

### B1 (blocker, col-b): P7 is still missing; the published lemma is `distAdv_def` in #195

**What the route needs from P7.** The brief uses `distAdv`'s body in four places. Probes at #210's
head, sealed (`ReviewColB-route.log`):

| Use | Brief | Without P7? | Probe |
|---|---|---|---|
| `0 ≤ ε_B n` | step 7, "Sign" | **Yes.** Replace `ε_B` by `fun n => \|ε_B n\|`: `Negligible.mono` with `abs_abs`, then `le_abs_self` and `abs_nonneg`. | S3 passes sealed |
| `Δ ≤ 1` at `n = 0` | error accounting | **Yes.** `StatClose X Y 1` from `statClose_iff` (#210), `uprob_nonneg` and `uprob_le_one`, then `distAdv_le_of_statClose`. | S6 passes sealed |
| Coin transport used inside `distAdv` (`B.distinguisherL n` against `D` at `n²`) | step 5, step 7 | **Yes,** if it is stated at the `distAdv` level. Use `NUPPT.distinguisherL_eq`, `NUPPT.runAt_eq` and `hrun` pointwise, then a `change` to `Fin (B.coinLen n) → Bool` and `rw` with the length equation (`NUPPT.coinLen_eq`, `PolyExpr.eval_subst`). The brief's `acceptProb` form (R5 shape, S2) also passes, but turning it into a `distAdv` bound needs P7. | S8, S2 pass sealed |
| Triangle inequality | step 6 (`(1/4)^N + distAdv …`), step 7 | **No.** No published lemma at #210 gives `distAdv X Z D ≤ distAdv X Y D + distAdv Y Z D` for samplers on different seed types. The near misses: `hybrid_lemma` (`Asymptotic/Ensembles.lean`) needs one common seed type and loses a factor `m`; `Ensemble.Indist.trans` works on ensembles; `LevinTransfer.distAdv_eq_of_unifProj` is an equality, and `UnifProj` has no public constructor for an equivalence. | C2 fails sealed, passes unsealed; S4 passes sealed with a `distAdv_def`-shaped hypothesis |

(The π-average of step 6 can probably go through `distAdv_sunglassRed`, `exists_fixCoins` and
`distAdv_comp` without P7. Not probed. Step 6 still needs the triangle inequality for its
`(1/4)^N` term.)

**The name.** The worker report E1a ("Not done", `gates/07-eqlemmas/worker-reports/E1a-REPORT.md:71`)
left `distAdv_eq` out because `Foundations/Experiments.lean` is a #195 file. #195 (open, head
`40553944`) adds a block "Defining equations" to that file, after `distAdv`: `invProb_def`,
`predProb_def`, `acceptProb_def` and `distAdv_def`, where
`distAdv_def (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D = |acceptProb X D - acceptProb Y D| := rfl`.
So P7 is `distAdv_def`, not `distAdv_eq`. Nothing at #210 provides it (`#check @distAdv_eq` and
`#check @distAdv_def` are both unknown identifiers: `ReviewColB-names.log`).

**What to do before issuing col-b (one of):**
- **(A, recommended)** Land #195's Experiments.lean block verbatim on the campaign branch before
  `@ANCESTOR@`, or merge #195 first. #195's version of the file is #210's plus exactly this
  block, so a verbatim copy merges with #195 without conflict. The DL brief also lists this lemma
  (E1a report, the same line).
- **(B)** Issue col-b with steps 6 and 7 expected to be blocked (E-API). `col_zk` is col-b's only
  target, so the fill would deliver only steps 1–5. Not recommended.

**Suggested replacements (assuming A):**
- Table row P7: `| P7 | distAdv (Foundations/Experiments.lean) | distAdv_def (from #195's "Defining equations" block, landed before @ANCESTOR@) | col-b (steps 6, 7: the triangle inequality) | review C2/S4 |`
- Step 7, replace the bullet "**Sign and triangle inequality.** …" by:
  > - **Sign.** Use `fun n => |ε_B n|` for `ε_B`: it is negligible by `hε.mono ⟨0, fun n _ => (abs_abs _).le⟩`,
  >   it is nonnegative, and it still bounds every gap (`le_abs_self`). No equation of `distAdv` is needed.
  > - **Triangle inequality.** `rw [distAdv_def]` on the three advantages, then `abs_sub_le`.
  > - **`n = 0`.** `Δ ≤ 1` by `distAdv_le_of_statClose` with `StatClose X Y 1`, which follows from
  >   `statClose_iff`, `uprob_nonneg` and `uprob_le_one`.
- Step 5, the coin-transport sentence. Replace "It is `EnsembleLemmas.acceptProb_coins_equiv` along
  `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)`, and it needs P8 and P9." by:
  > State it at the `distAdv` level: `distAdv X Y (B.distinguisherL n) = distAdv X Y fun y c => D.distinguisherL (n * n) (F y) c`
  > from `B.coins = D.coins.subst (.mul .var .var)` and `∀ y r, B.runAtL n y r = D.runAtL (n * n) (F y) r`.
  > Proof: `NUPPT.distinguisherL_eq`, `NUPPT.runAt_eq` and the run equation pointwise; `change` the
  > coin type to `Fin (B.coinLen n) → Bool`; `rw` with `B.coinLen n = D.coinLen (n * n)`
  > (`NUPPT.coinLen_eq`, `PolyExpr.eval_subst`, `eval_mul`, `eval_var`). An `acceptProb` form
  > (`EnsembleLemmas.acceptProb_coins_equiv` along `Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)`)
  > may be added beside it.

### M1 (major): the "Before issue" conditions and the prerequisite table are out of date

#210 adds every prerequisite except P7. All names below are at #210's head with the meaning the
brief gives them (`ReviewColA.log`, `ReviewColB-names.log`).

**Replace the Status block's "Before issue" list (lines 7–10) by:**
> - **Before issue** (each item lands on the campaign branch, so that `@ANCESTOR@` contains it):
>   - PR #210 (the rule-10 equation lemmas P1–P6, P8–P12, table below);
>   - P7, `distAdv_def`: #195's `Foundations/Experiments.lean` block "Defining equations"
>     (col-b only; see the table);
>   - the edits from this brief's review (`review.md`);
>   - the issue commit.

**Replace the section "Rule-10 prerequisites (before issue)", from its first paragraph through
the line "P10 changes col-a's file, …", by:**
> ## Rule-10 prerequisites (published equations)
>
> The routes read these definitions only through the equations below. All except P7 come from
> PR #210. None is `@[simp]`.
>
> | # | Definition (file) | Published lemma(s) | Unit(s) |
> |---|---|---|---|
> | P1 | `R3COL` (`ThreeColoring/Language.lean`) | `R3COL_iff` | col-a, col-b |
> | P2 | `ProperColoring` (`Language.lean`) | `ProperColoring_iff` | col-a |
> | P3 | `encColoring` (`ZeroKnowledge/Encoding.lean`) | `encColoring_eq` (`List.ofFn` form), `getD_encColoring`, `getD_encColoring_two_mul`, `getD_encColoring_two_mul_add_one` | col-a |
> | P4 | `Strategy.coinLen` (`ZeroKnowledge/Interaction.lean`) | `Strategy.coinLen_eq` | col-a, col-b |
> | P5 | `ZK` (`ZeroKnowledge/Defs.lean`) | `ZK_iff` | col-b |
> | P6 | `Protocol.viewV`, `View.encode` (`Interaction.lean`) | `Protocol.viewV_withV`, `View.encode_mk` | col-b |
> | P7 | `distAdv` (`Foundations/Experiments.lean`) | `distAdv_def` (#195's block; see the Status) | col-b (the triangle inequality in steps 6–7) |
> | P8 | `NUPPT.distinguisherL` (`Asymptotic/Adversary.lean`) | `NUPPT.distinguisherL_eq` | col-b |
> | P9 | `NUPPT.coinLen` (`Complexity/Randomized/PPT.lean`) | `NUPPT.coinLen_eq` | col-b |
> | P10 | `colCommit`, `colOpen`, `colCoinSlice`, `colIterations`, `colProver`, `colProtocol` (`ThreeColoring/Protocol.lean`) | `colCommit_eq`, `colOpen_eq`, `colCoinSlice_eq`, `colIterations_eq`; `colProver_coins`; `colProver_next_nil`, `colProver_next_cons`, `colProver_next_cons_of_edgeCount_eq_zero`; `colProtocol_P`, `colProtocol_V`, `colProtocol_rounds`, `colProtocol_verifierFirst` | col-b |
> | P11 | `sampleIdx` (`Language.lean`) | `sampleIdx_eq_rejectionSample`, `sampleIdx_ofFn_eq_rejectionSample` (the tape lemma) | col-b |
> | P12 | `Strategy.Efficient` (`Interaction.lean`) | `Strategy.efficient_iff` | col-b (generic verifier-call lemma) |
>
> - **If one of these is missing at `@ANCESTOR@`,** report the steps that need it as blocked
>   (escalation E-API, defined under Ground rules) and go on with the others. Do not read the body.

Keep the bullet "Published equations that already exist and suffice". All of its names exist;
`NUPPT.simulate_eq` is in `ZeroKnowledge/Defs.lean`. Also add `PolyExpr.eval_mono` (see m2).

**Elsewhere:**
- Line 8: replace "the rule-10 prerequisites P1–P11 below (published equations missing at the
  pre-ship commit)" as above.
- col-a route, line 113: replace "It needs the bitwise equation of `encColoring` (P3)." by "Read
  `encColoring` through `encColoring_eq` / `getD_encColoring` (P3)."
- REPORT checklist, last item: replace "Prerequisites P1–P12 found missing at `@ANCESTOR@`, if any,
  and the steps they blocked." by "Any prerequisite of the table found missing at `@ANCESTOR@`
  (expected: none), and the steps it blocked."

### M2 (major, col-a): `Protocol.lean` already has 999 lines, so col-a will pass 1000

At #210's head `Protocol.lean` has **999** lines; the brief says 926. E1a wrote its additions
compactly to stay under (E1a report: "`Protocol.lean` ends at 999"). `colRep_efficientProverProof`
names `colProtocolRep`, so its proof must stay in `Protocol.lean`. Any proof there takes the file
past 1000. The user's 2026-11-06 size exceptions cover only `Candidates/RSA.lean`,
`Candidates/Rabin.lean` and `Asymptotic/Collections.lean` (plan, decision log).
- **Before issue:** record a size exception for `ThreeColoring/Protocol.lean` (user ruling, as for
  RSA, Rabin and Collections), or tell col-a explicitly that crossing 1000 is expected and is
  reported, not avoided.
- **Replacement for the bullet "Why." (lines 63–64):**
  > - **Why.** At `@ANCESTOR@`, `Protocol.lean` has 999 lines and `Simulator.lean` has 804.
  >   `colRep_efficientProverProof` names `colProtocolRep`, so its proof stays in `Protocol.lean`,
  >   and col-a's fill takes that file past 1000 lines. [Size exception for `Protocol.lean`:
  >   <ruling, date>.] Keep the file's growth small: put everything that does not name the
  >   definitions below in helpers.
- **Replacement for the sentence "Aim to keep each owned file at or under 1000 lines. …":**
  > `Simulator.lean` should stay at or under 1000 lines. `Protocol.lean` will pass 1000; record
  > its final line count and the reason in `REPORT.md` (the frozen definitions and statements
  > cannot move).

### M3 (major): the lint sweep and its "decisions" are done; the brief still assigns them

#210 fixed all 20 pre-existing `style_lint.py` findings, including col-a's. `colProtocol_sound`
(now at `Protocol.lean:796`) already has a **Proof sketch.** (diff at `Protocol.lean:789–795`).
At #210's head (`lint-head.log`, `c8b-head.log`, `c8b-zk-head.log`):
- `style_lint.py`: **0 findings** in the 9 `ThreeColoring/` files and the facade;
- `campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge/ThreeColoring`: **0 FAIL**,
  8 WARN (check 8: `Protocol.lean` 3, `Simulator.lean` 17);
- the 6 facade FAILs on `ThreeColoring.lean` appear only when the parent directory is linted
  (`… --check8b TCSlib/Cryptography/ZeroKnowledge`).

The brief still tells col-a to add that sketch, and Ground rule 1 still authorizes it. A worker
would make a redundant docstring edit, which is a statement-freeze deviation for no reason.

**Replace the section "Lint sweep (decision 2026-11-05)" by:**
> ## Lint
>
> - **Run, before and after:** `python3 -I scripts/style_lint.py <owned files and your helpers>`,
>   and `python3 -I scripts/campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge`.
>   The script takes a **directory**; given a file it prints "no .lean files". Read the
>   `ThreeColoring` lines; the parent directory is needed for the facade check.
> - **At `@ANCESTOR@`** (the 2026-11-05 sweep was done by PR #210):
>   - `style_lint.py`: 0 findings in the 3-colouring files;
>   - `campaign_style_lint.py`: no FAIL in `ThreeColoring/`; 6 pre-existing facade FAILs on
>     `ThreeColoring.lean` (owned by neither unit); check-8 WARNs `Protocol.lean` 3,
>     `Simulator.lean` 17.
> - **Your delivery** adds no finding, no FAIL and no new check-8 name in your files, apart from the
>   facade line of each new helper module (above). Edit no file outside your unit.

**Elsewhere:**
- Ground rule 1, second bullet: replace "the docstring edits authorized above (`col_zk`'s sketch;
  `colProtocol_sound`'s sketch);" by "the docstring edits authorized above (`col_zk`'s sketch,
  col-b);".
- Pre-ship record, row "Lint at the base": keep it, and add a row (m7).

### M4 (major, col-b): the rule-11 wording now also catches public lemmas

Ground rule 3 says: "For col-b this includes `Protocol.lean`'s private `colProver_next_*` and
`Language.lean`'s private `tapeEquiv` and `sampleIdx_ofFn`." At #210's head, `colProver_next_*`
also matches the **public** P10 lemmas `colProver_next_nil`, `colProver_next_cons` and
`colProver_next_cons_of_edgeCount_eq_zero`. The private ones are now `colProver_next_nil_of` and
`colProver_next_cons_of` (`Protocol.lean:682, 693`). `sampleIdx_ofFn` is also a prefix of the
public `sampleIdx_ofFn_eq_rejectionSample`. A careful worker could refuse the very lemmas that
steps 2, 3 and 6 need.

**Replace by:**
> For col-b this includes `Protocol.lean`'s private `colProver_next_nil_of`,
> `colProver_next_cons_of`, `colProtocol_outV`, `colProtocol_outV_honest`, `uprob_check_uniform_le`
> and `colProtocol_sound`, and `Language.lean`'s private `tapeEquiv` and `sampleIdx_ofFn`. Use
> their public forms: `colProver_next_nil`, `colProver_next_cons`,
> `colProver_next_cons_of_edgeCount_eq_zero` and `sampleIdx_ofFn_eq_rejectionSample`.

### m1 (minor): line numbers

At #210's head (`Simulator.lean` is unchanged by #210):
- the unit table: `R3COL_witnessRelation`'s `decidable` clause is at `:919` (`· sorry`; brief
  `:846`); `colRep_efficientProverProof` is at `:990` with its `sorry` at `:992` (brief `:919`);
  `col_zk` is at `:780` (unchanged);
- line 56: replace "Line numbers are at the pre-ship commit `5f2771631fe853dae9c2aa44791ae5b0e09c95eb`."
  by "Line numbers are at PR #210's head `fff0430c7c9db136e60ed14b069e972c2ea56fc8`; check them
  at `@ANCESTOR@`.";
- line 122: "Follow its docstring sketch (`Protocol.lean:893–916`)" becomes `Protocol.lean:966–989`;
- P10's "(today private, `:644–667`)" goes (M1's table replaces it);
- `Simulator.lean:769–771` and `:744–745`, for the docstring edits, are still right.

### m2 (minor): route hints worth adding (all checked or present at #210's head)

- **col-b, step 2.** The commitment randomness `r_i j = r.getD (3|x| + i ℓ(n) + j)`
  (`colProver_next_nil`) lies inside the prover's tape of `3|x| + |x| ℓ(|x|)` bits
  (`Strategy.coinLen_eq`, `colProver_coins`) because `n ≤ n² = |x|` and `PolyExpr.eval_mono`. The
  rest of the unfolding is `Protocol.viewV_withV`, `View.encode_mk` (probe S5 rewrites the left
  side sealed), `colProtocol_P`, `colProtocol_rounds` with `PolyExpr.eval_const`,
  `colProtocol_verifierFirst` and `exec_succ`.
- **col-b, step 7: the simulator's seed.** `S.Coins |x|` against the ladder's
  `Fin ((colSimCoins ℓ V').eval |x|) → Bool`: `funext` of `exists_colSimulator`'s equation, then a
  `change` to `Fin (S.coinLen |x|) → Bool`, then `rw` with `NUPPT.coinLen_eq` and `S.coins = colSimCoins ℓ V'`
  (probe S7, sealed). The same move works for `D`'s coins: `change` first, as the brief's
  "Lengths" bullet requires; a direct `rw` fails with a motive error.
- **col-a, the decider.** The colour values go through `ColMachines.decColoring_val`. Its right
  side `ColMachines.colorVal` has `ColMachines.colorVal_poly` (`Machines.lean:865`); cite that too.

### m3 (minor): the "Mathlib first" paragraph points to a section with no 3-colouring entry

`mathlib-overlap-nt.md`, "Advice for the fill briefs", has entries for rsa, rabin, fac and dl
only. **Replace** "The names to cite for this fill are in … (all reachable from the owned files'
current imports)." by:
> That file has no 3-colouring entry: these fills prove no number-theory facts. The arithmetic
> they need is already in TCSlib or Mathlib (`Nat.sqrt_eq`, `one_sub_inv_pow_mul_le_exp`,
> `negligible_exp_neg_sqrt_div`).

### m4 (minor): leftover attachment wording

Line 469: "Use the environment addendum attached at dispatch (v1)." The exchange protocol has no
attachments (EXCHANGE.md: the addendum is in `outbox/fills/<fill>/`). **Replace** by "Use the
environment addendum v1 (`fill-environment-addendum.md`, next to this brief in `outbox/fills/3col/`
on the exchange branch)." No other zip or attachment language remains.

### m5 (minor): checkpoints and E-API are not defined

- After "Push at each checkpoint" (line 32), **add**:
  > Checkpoints: col-a after the decider and after `colRep_efficientProverProof`; col-b after each
  > ladder step. Also push at least every two hours of work.
- Ground rule 5: **add**:
  > **E-API:** a published equation that a step needs is missing. Report it in `REPORT.md` with the
  > definition and the lemma you would need, mark the step blocked, and go on with the steps that
  > do not need it.

### m6 (minor): the pre-ship record should say what changed at #210

**Add a row** to the pre-ship table:
> | Review at #210's head `fff0430c` | All cited names present with the cited meaning, except P7 (`distAdv_def`, #195). Build inputs regenerated: unchanged (order 142, roots 66, 21 sorried declarations in 10 modules; owned files `Protocol.lean` 2, `Simulator.lean` 1). Ladder statements 1–4, `colSimRed_fixed_eq` and 6 elaborate. Sealed: `ZK_iff` intro, the coin transport (`acceptProb` and `distAdv` forms), `\|ε_B\|`, `Δ ≤ 1`, the simulator-seed transport and the step-2 unfolding pass; the triangle inequality fails without P7. Lint: 0 `style_lint` findings, 0 FAIL in `ThreeColoring/` | `review.md` and `$SP/review/3col/` |

In the build-inputs paragraph (lines 472–479), replace "identical for both units at the pre-ship
commit" by "identical for both units at the pre-ship commit and at #210's head". Note for the
maintainer: if #195 merges before `@ANCESTOR@` (option A of B1), regenerate the inputs at
`@ANCESTOR@`. #195 touches upstream files, so the counts may change.

### m7 (minor): the facade FAIL is invisible with the brief's lint command

The brief says a new helper "adds a facade FAIL in `campaign_style_lint.py`". With the command the
brief prescribes (`--check8b …/ThreeColoring`), the facade check of `ThreeColoring.lean` does not
run: it shows only for the parent directory (`c8b-zk-head.log`). M3's replacement fixes the
command.

### Checked, no finding

- **Targets.** `base-sorries.txt` at #210's head lists `Protocol.lean`: `R3COL_witnessRelation`,
  `colRep_efficientProverProof` (2) and `Simulator.lean`: `col_zk` (1). These are exactly the
  brief's targets. The quoted statements match the source: `WitnessRelation L3COL R3COL`;
  `EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL`; `ZK (colProtocol Com ℓ) R3COL`. The
  consumers (`colRep_interactiveProof`, `col_hvzk`, `col_zeroKnowledgeProof`) exist.
- **Routes (rule 10).** Every route names published lemmas. The only foreign body still read is
  `distAdv`'s (B1). The gate 03g route is the brief's: the §2.3 sketch, the erratum and R2-1's
  `ε_B(n) ≤ N² ε_B(n)` for `m = 0`, `n ≥ 1`. R2-2's advice bound is quoted correctly. The
  docstring replacement text for R2-1 matches the erratum.
- **Self-containment and protocol.** The repository, branch, `@ANCESTOR@` placeholder, local
  `fill/<unit>` branch, `inbox/fills/<unit>/` layout, pull-rebase rule, no force-push and no PRs
  all agree with the exchange branch's `README.md` (head `0543e73e`) and `EXCHANGE.md`.
- **Parallel safety.** The units own disjoint files. col-b needs only statements of `Protocol.lean`,
  and the P10 lemmas are in #210, so col-b no longer waits on col-a. The authorized imports are
  cycle-free: GI `SoundnessRepGI`, `Efficiency` and `NPLemmas` import nothing from `ThreeColoring`.
  The helper namespaces `ColRep` and `ColZK` are distinct.

## Probe results (at `fff0430c`)

| Probe | Result | Log |
|---|---|---|
| `Probe/ReviewColA` (imports `ThreeColoring.Protocol`, GI `SoundnessRepGI`, GI `Efficiency`): every col-a name, P1–P4, P10, the GI templates | 71 of 72 names resolve. The exception, `colProtocol_sound`, is private, as the brief says | `$SP/review/3col/ReviewColA.log` |
| `Probe/ReviewColB`, names (imports `ThreeColoring.Simulator`, `NPLemmas`, `GraphIsomorphismZK.Closeness`): every col-b name, P1, P4–P12, templates | 123 of 125 checks resolve. The exceptions are `distAdv_eq` and `distAdv_def` (P7) | `$SP/review/3col/ReviewColB-names.log` |
| `Probe/ReviewColB`, route (sealed: `multiCom`, `distAdv`, `acceptProb`, `NUPPT.distinguisherL`, `NUPPT.coinLen`, `NUPPT.runAt`, `PolyExpr.eval`, `ZK`, `Protocol.viewV`, `transcriptWith`, `View.encode`, `Strategy.Efficient`, `Strategy.coinLen`, `Negligible`, `StatClose`, `uprob`; `-simp` `eval_var`, `eval_mul`) | Controls: C1 (`0 ≤ distAdv` by body) and C2 (triangle) **fail sealed** and **pass unsealed**. Pass sealed: S1 (`rw [ZK_iff]; intro`), S2 (`acceptProb` coin transport, P8/P9), S3 (`\|ε_B\|`), S4 (triangle from a `distAdv_def` hypothesis), S5 (`viewV_withV`, `View.encode_mk`), S6 (`Δ ≤ 1`), S7 (simulator seed), S8 (`distAdv` coin transport). Ladder statements l1–l4, `colSimRed_fixed_eq`, l6 elaborate (`sorry` warnings only) | `$SP/review/3col/ReviewColB-route.log` |
| `fillinputs.py … fff0430c …` for both units | Unchanged from the brief's `inputs/` (`cmp`): 142 / 66 / 21 in 10 modules | `$SP/review/3col/inputs/` |
| `style_lint.py` and `campaign_style_lint.py --check8b` at the head | See M3 | `$SP/review/3col/lint-head.log`, `c8b-head.log`, `c8b-zk-head.log` |
