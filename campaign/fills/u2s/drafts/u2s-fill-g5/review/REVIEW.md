# Review of `u2s-fill-g5.DRAFT.md` (G5, `two_work_tapes_run`)

Reviewer: read-only review agent, 2026-11-06. Sources read at the overlay
`/home/user/tcslib-scratch/wt-hk` (`7f05ef30`, #202's head plus the `Build.ZoneStep` import).
Line numbers `Lnnn` are the draft's. The known placeholders (`@TBD@`, `@ANCESTOR@`) are not
reported.

Two scratch elaborations were used (the allowed maximum), against `oleans-lsi2`:
- `wt-hk/rvprobe/g5review/G5RvSigma.lean` gives `agents/g5review/G5RvSigma.out`, exit 1;
- `wt-hk/rvprobe/g5review/G5RvSigma2.lean` gives `agents/g5review/G5RvSigma2.out`, exit 1.
  This one is the decisive run. In the file, `U*` are unsealed controls and `S*` run under the
  seal.

## Summary

| # | Rank | Where | Problem |
|---|---|---|---|
| B1 | **blocker** | L242–243, L300–303, L419–433, L539–546 | Under the seal, no proof can reach the data maps' per-track contents (`zoneRebalanceData_snd`, `zoneExtendData_snd` are dependent and pointwise). The invariant, fullness and the count cannot be proved |
| M1 | major | L536–537 vs L304–307, L540–548 | The brief permits unfolding `MultiTapeTM.step`/`Action.apply` for the leaf. The required seal makes both irreducible |
| M2 | major | L405–408, L435–439, L443–448 | The iteration's starts are described circularly, and the recommended invariant is false at round 0 |
| m1 | minor | L452–459, L415–416, L519–521 | The count and level bounds need an orbit invariant that is not stated. Checkpoint 6 depends on part of checkpoint 4 |
| m2 | minor | L395–397 | `Contract.*_positive` give `Contract.Positive`, a definition with no equation, so they are unusable under the seal. The same holds for `Segment`'s projections |
| m3 | minor | L443–445 vs L470–472 | The iteration is stated only up to `t₀`, but the converse needs it without a halting time |
| m4 | minor | L210–214, L371–373 | The machine of a stay phase is unspecified, and the brief's "no further leaf" rule makes it look like an escalation |
| m5 | minor | L51, L230, L283–284 | The import probe does not check four cited names. Two names the copied probe uses are not listed |
| m6 | minor | L460–463 | `Nat.pow_log_le_self` needs `t₀ ≠ 0`, and the brief does not say where that comes from |
| n1–n4 | note | various | Line shift after region (a); `Simulation` not in the screen population; plan §8 not among the design records; binding versus recommended for segments |

The arithmetic of the final bound (task item 4) checks out (see the section below). The other
cited lemmas (task item 2) match their statements at the overlay (see the section after it).

---

## B1 (blocker): the per-track contents of the data maps cannot be reached under the seal

**What the brief asks.**
- L242–243 cite `zoneRebalanceData_fst`, `_snd`, `zoneExtendData_fst` and `_snd` as the way to
  read the data maps.
- L300–303 allow the maps to be read "only through their equations".
- L419–433 build the invariant's preservation on them: "`zoneRebalanceData_snd` changes track
  `t` only", the represented tape through `zoneTrackTape_rebalance_right`/`_left`, and the
  extension through `zoneTrackTape_extend` and `extend_words_*`.
- L539–546 require a seal with `zoneRebalanceData`, `zoneExtendData`, `zoneTrackStepData`,
  `zoneTrackTape` and the rest irreducible.

**What is wrong.** `ZoneData k := Σ ℓ, Fin k → ZoneContents ℓ`. The `simps` fields are
*pointwise* and dependent:
- `(zoneRebalanceData dir t D).snd a = Function.update D.snd t (zoneRebalance dir (D.snd t)) a`;
- `(zoneExtendData D).snd t = (D.snd t).extend`.

The left side lives at level `(zoneRebalanceData dir t D).fst`. The right side lives at `D.fst`,
or `D.fst + 1` for the extension. The two levels are equal only by unfolding the map. Under the
seal, rewriting with `_snd` leaves goals whose two sides differ only in the hidden implicit `ℓ`.
Rule 10 forbids closing them by `rfl` on another file's definition, and the seal rejects it. The
Sigma-level equation cannot be rebuilt from the fields either.

**Evidence** (`G5RvSigma2.out`; `G5RvSigma.out` agrees):
- **Unsealed controls pass.** `U1` and `U2` state the Sigma equations
  `zoneRebalanceData dir t D = ⟨D.1, Function.update D.2 t (zoneRebalance dir (D.2 t))⟩` and
  `zoneExtendData D = ⟨D.1 + 1, fun t => (D.2 t).extend⟩`; both hold `:= rfl`. `U3` closes by
  `rw [zoneRebalanceData_snd, Function.update_self]`. No errors on these lines.
- **S1** (sealed, the rebalanced track): the `rw` leaves the goal
  `zoneTrackTape (zoneRebalance dir (D.snd t)) p = zoneTrackTape (zoneRebalance dir (D.snd t)) p`,
  with both sides printed identically. `exact rfl` then fails: "Type mismatch … rfl has type
  ?m = ?m". An agent will see a goal that looks trivial and cannot be closed.
- **S4** (sealed, another track, `rw [zoneRebalanceData_snd, Function.update_of_ne h]`): the
  same leftover, `zoneTrackTape (D.snd t') p = zoneTrackTape (D.snd t') p`, unsolved.
- **S5** (sealed, the extension): after `rw [zoneExtendData_snd]`, the lemma
  `zoneTrackTape_extend` fails with "did not find an occurrence of the pattern", because of the
  `ℓ` mismatch.
- **S2 and S3** (sealed): the Sigma equation from `Sigma.ext`, `zoneRebalanceData_fst` and
  `heq_of_eq (funext (zoneRebalanceData_snd …))` fails with an application type mismatch.
  `simp only [Sigma.ext_iff, …]` does not get it either.
- **S6 and S7** (sealed, given the Sigma-level equations as hypotheses): the rebalanced track's
  represented tape (through `zoneTrackTape_rebalance_right`) and the extension's (through
  `zoneTrackTape_extend`) both elaborate with no error. So the equations below are sufficient.

**Cost.** Every step that reads a track's contents after a track step is blocked, under the
seal: invariant item 2 (the represented tapes), item 5 (fullness), the count and level bounds,
and so checkpoints 4–8. The agent's only legal move is to escalate (ground rule 4), after
discovering the trap. The pre-ship missed it because the import probe does not `#check` these
four names (m5).

**Fix** (before issue, as #202 was handled). Publish two Sigma-level equations in
`Build/ZoneRebalance`, each proved `rfl` (U1 and U2 confirm they hold):
- `zoneRebalanceData_eq`: `zoneRebalanceData dir t D = ⟨D.1, Function.update D.2 t (zoneRebalance dir (D.2 t))⟩`;
- `zoneExtendData_eq`: `zoneExtendData D = ⟨D.1 + 1, fun t => (D.2 t).extend⟩`.

Then cite them in place of the `_snd` fields at L242–243 and L433, add them to the import probe,
and add to the pitfalls: "rewrite whole `ZoneData` values, never `.snd` alone; a printed goal
`f x = f x` that `rfl` cannot close is a hidden-level mismatch."

The fallback is a narrowly scoped rule-10 exemption for these two maps. It is weaker, since it
punches a hole in the seal and in "never restate one as a private".

---

## M1 (major): rule 10 permits unfolding `step`/`Action.apply`, but the seal forbids it

**What the brief says.**
- L536–537: "unfold `MultiTapeTM.step` and `Action.apply` only for your own leaf".
- L304–307: `MultiTapeTM.step` only "through `step_of_some`/`step_of_halt`, `Action.apply`
  through its fields".
- L540–548: the seal "start[s] from the route probe's seal, 15 definitions". That list includes
  `step` and `Action.apply` (`route/README.md` L23), with `[-simp]` on `Action.apply`.

**What is wrong.** If the agent takes up the permission, its seal test fails. The test is a
"checklist failure" (L557). The permission is also unnecessary:
- `step_of_some` gives `tm.step cfg = (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg`
  (`Deterministic.lean` L200);
- `Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` and `Action.apply_workTapes`
  (`Simulation.lean` L89) give every field;
- only the leaf's own `tr` needs unfolding.

**Fix.** Replace L537's clause with: "for your leaf, read `MultiTapeTM.step` through
`step_of_some` and `Action.apply` through `Action.apply_*` and `Action.apply_workTapes`; unfold
only your own transition function."

---

## M2 (major): the iteration's starts and round 0

**What the brief says.**
- L443–448: the rounds' starts are "the run's configurations at the round boundaries".
- L405–408: the recommended invariant "at the start of round `s`" includes `zoneRowPre D d`.
- L435–439: the first round starts from a tape `0` that is blank, "not a zoned tape".

**What is wrong.**
- `Segment.iterate_seq (cs) (τ) (h0) (n) (h : ∀ r < n, Segment M F P (cs r) (cs (r+1)) (τ r))`
  (`Contract/Basic.lean`) needs each `cs r` given in advance. If `cs r` is defined as `HS`'s run
  at the summed boundary times, then knowing its shape is exactly the induction over rounds that
  the brief forbids ("never write the induction yourself", L447–448).
- The usable reading is an **explicit encoding** `cs r := enc(c_r, D_r)`: state the leaf at
  `c_r`'s state, tape `0` `= zonedTape D_r.2`, head `0` at `0`, tape `1` blank, head `1` at `0`,
  `c_r`'s input position, and `c_r.output.map Sum.inl`. Every field is fixed by the invariant.
  The brief does not say this.
- At `r = 0`, `cs 0` must be `HS`'s initial configuration. Its cell `0` is blank, whereas
  `zonedTape_zero` puts `some (.inr fun t => some none)` there. So the recommended invariant is
  false at round 0, and the uniform per-round hypothesis of `iterate_seq` breaks at `r = 0`.

**Fix.** Say it explicitly:
- `cs 0 :=` the initial configuration, and `cs (r+1) := enc(c_{r+1}, D_{r+1})`;
- the round lemma takes any start whose tape `0` agrees with `zonedTape D.2` off cell `0`, and
  whose cell `0` is either blank (with every home blank) or `zonedTape D.2 0`. The leaf's decoded
  read `(zoneCellOfCell (w 0) t).join` is the same on both (`zoneCellOfCell_none`/`_inr`);
- the lemma ends exactly at `enc(step c, D')`.

This makes the first round an instance rather than a special case, and makes invariant item 1
"off cell 0".

---

## m1 (minor): the count and level bounds need an unstated orbit invariant

**The level bound** (L456–459).
- "The level after `s` steps is at most `Nat.log 2 s + 1`" holds at round boundaries.
- Within round `s`, an earlier track's extension can raise `D.1` before track `t` scans.
  Example: at `s = 1`, a track displaced by `1` extends at level `1`, so `D.1 = 2 > Nat.log 2 1 + 1`.
- So `idx t s` must be bounded by the level after `s + 1` rounds, `≤ Nat.log 2 (s+1) + 1`. This
  is still `≤ L := Nat.log 2 t₀ + 1` because `s + 1 ≤ t₀`, so the brief's `L` is right.
- Say this, or the agent will try to prove a false intermediate claim.

**The quantity both arguments use.**
- The count argument (L452–455) and the level argument both rest on one quantity: per track, the
  number of stored cells on one side over levels `≤ i`. Under fullness it changes by exactly
  `±1` per move whose index is `≤ i`, is `2^{i+1} − 1` after an index `> i`, and is unchanged
  by extensions, which add only higher levels.
- This follows from `zoneCascadeRight_lengths`/`zoneCascadeLeft_lengths` (levels `< j` and level
  `j`), `zoneRebalance_frame` (levels above), and `extend_words_*`.
- It is not among step 4's invariants. The level bound also needs its global form: the side
  total minus `2^{D.1} − 1` equals the track's net displacement.

**Checkpoint dependency.** Ground rule 4 (L519–521) says checkpoint 6 is "pure arithmetic over
the data orbit" and independent of the controller. But fullness preservation, which checkpoint 6
needs, is placed in checkpoint 4 together with the controller round.

**Fix.**
- Add the side-total invariant to step 4.
- Move fullness preservation (a pure data-orbit fact) into checkpoint 6.
- Add the `s + 1` remark to L458.

---

## m2 (minor): positivity lemmas and segment projections under the seal

- L395–397 recommend `Contract.inPhase_positive`, `seq_positive` and `branch_positive`. They
  return `C.Positive`, a `def` (`Contract/Basic.lean`: `Positive C := ∀ i d, …`) with no
  equation. Applying it unfolds the def, so the seal ("every other-file TCSlib definition your
  proofs mention") rejects it. Positivity is free anyway: `inPhase_time … = C.time … + 1`, and
  the leaf's step takes one time unit.
- Likewise `Turing.Segment` and `HeadBox` are defs. Anonymous projections `h.1`/`h.2.1` on a
  sealed `Segment` fail. Use `segment_iff`, which is listed.

**Fix.** Recommend positivity from `inPhase_time` (or the leaf step). Add `Segment`, `HeadBox` and
`Contract.Positive` to the seal's "at least" list with a "read through `segment_iff`" note.

---

## m3 (minor): the iteration is bounded by `t₀`, but the converse has no `t₀`

L443–445 state the iteration "for every `s ≤ t₀` (`t₀` the source's first halting time)". Step 6
(L470–472) needs `HS` live through `s` rounds for **every** `s` when `M` never halts, where there
is no `t₀`.

**Fix.** State the iteration lemma for every `s` such that `M`'s run is live at all times
`< s`. One lemma then serves both directions; otherwise checkpoint 8 redoes checkpoint 5.

---

## m4 (minor): which machine runs a stay phase?

**What is wrong.**
- L371–373 recommend stays as zero-time phases (`Contract.zero M e …` needs some machine `M`
  and entry `e`, with exits `{some e}`).
- L210–214 make "any further leaf … an escalation". An agent may write a trivial `Unit` machine,
  or may stall on whether that is allowed.

**Fix.** Name the choice. For example: the stay phase's machine is the track machine of either
direction at its `entry`, with `X = {some entry}` and `red p s := if s = entry then … else none`.
Or explicitly allow a trivial `Unit` machine and say that it is not a leaf.

---

## m5 (minor): the import probe and the API list

- L51 and L230 say the probe checks "every name this brief cites". It does not `#check`
  `zoneRebalanceData_fst`, `zoneRebalanceData_snd`, `zoneExtendData_fst` or `zoneExtendData_snd`.
  A script compared the draft's backticked names with the probe's 213 `#check`s; only these
  four, the WS-1 names and the probe-only names are absent.
- `tt_zero_tapes`, which L141 says to copy "as they are", uses `embedEmitCfg_state` and
  `embedEmitCfg_output` (`route/G5Route.lean.txt` L85–92). L283–284's R1 list omits them.

**Fix.** Add these names to the list and the probe; re-run.

## m6 (minor): `t₀ ≠ 0`

L462: `Nat.pow_log_le_self 2 (hx : t₀ ≠ 0)` needs `t₀ ≥ 1`. That comes from the initial state
being live (`initCfg_eq`, `Cfg.init_state`, `runFrom_zero`), or from `not_computesInTime_zero`
at `t₀`. L479 states it only for `t`. Add one clause.

## Notes

- **n1.** "Lines in this brief are your base's" (L91), but region (a) is the first edit. After it,
  regions (b)–(d) are at 50, 71 and 64, not 49, 70 and 63 (the pre-ship's `OwnedFile.out` already
  reports the `sorry` at 71). Say "+1 after region (a)".
- **n2.** The screen population (L592–595) omits `Simulation.lean`, home of the cited
  `Action.apply_workTapes`.
- **n3.** L59 lists plan §1–§3 and §6–§7. The last section (L735) rules from plan §8, which
  should be listed too.
- **n4.** Step 3 calls the round-as-segment form "Recommended" (L383). The hazards (L641–642,
  "compose your round as segments instead") and Q4 (L745–746) make it effectively binding.
  Mark it binding, or say that an exit-set restatement is a duplication finding.

## Task item 4: the arithmetic of the final bound (checks out)

`sum_cost_le_of_count k T L A B idx cost` (`ZoneStep.lean` L298) concludes
`Σ_{s<T} cost s ≤ B·T + k·(A·((L+2)·T + 2^L) + T)`. Its `hstep` shape matches the round:
- `B = 2` (the leaf and its dispatch);
- `A·(2^{idx}+1)` per track (`exists_zoneTrackStepTM`); a stay costs `0 ≤ A·2`;
- `+k` for the tracks' dispatches (`inPhase_time = C.time + 1`);
- the halting round costs `1 ≤ B`, with `idx := 0`.

With `T = t₀ ≥ 1` and `L = Nat.log 2 t₀ + 1`:
1. `2^L = 2·2^{log t₀} ≤ 2t₀`.
2. So the sum is at most `B·T + k·(A·(log T + 5)·T + T)`.
3. That is at most `(B + k(5A+1))·T·(log T + 1)`.
4. That is at most `c₁·(T+1)(Nat.log 2 (T+1) + 1)`, by `Nat.log_mono_right`.
5. Then `ComputesInTime.mono` takes it to `t`, and `tt_frame` multiplies by `c₂`.

`t = 0` is vacuous (`not_computesInTime_zero`). The brief's `L` is the right target, with m1's
remark about the round-`s` index.

The count form is satisfiable. After a scan beyond level `i`, the side total over levels `≤ i` is
`2^{i+1} − 1`; the next such scan needs it at `0` or at `2^{i+2} − 2`, so such scans are at least
`2^{i+1}` rounds apart, which gives `≤ T/2^i + 1`.

## Task item 2: citations that check out

These were spot-checked against the overlay; each matches the brief's description and argument
shape:
- `exists_zoneTrackStepTM` (five clauses, per-`x` contract, `none ∉ X`);
- `sum_cost_le_of_count` / `sum_two_pow_le_of_count`;
- `zoneRowPre_congr` (function equality of `workTapes`, head `0`) and `zoneRowPre_mapState_iff`;
- `Contract.inPhase` (`hnone`, `hred`, `hsome` with `q.1 ≠ p`; `pre`/`time`/`post` as the brief
  says);
- `phaseHostTM_run_le` (the guard on states before `T`; works for the halting leaf step);
- `Segment.iterate_seq` (arbitrary starts; `P` at `cs 0`);
- `alphabet_reduction_run` (`∃ c M'`, image converse);
- `Cfg.bindState_*` (pointwise, as pitfall 1 says);
- the Zone lemmas' hypotheses (`zoneTrackTape_rebalance_right`: lower opposite zones full, room
  `2^(idx−1)`; `zoneCascadeRight_lengths`), which fullness supplies;
- the direction convention: `SignType` `1` is `+1` head position, which is `zoneRebalance true`,
  with the represented tape read at `p + 1`.

The route probe's `tt_frame` hypotheses equal step 0's forward and converse properties word for
word. `tt_zero_tapes` matches step 1, including the `with q₀` restart.
