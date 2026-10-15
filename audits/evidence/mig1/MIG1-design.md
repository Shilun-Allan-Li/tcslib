# MIG-1 design: named witnesses, the `f2_` deletion, the R3 canonical retirement

> **Maintainer note (2026-10-13).** A maintainer sub-agent wrote this file against the read-only
> checkout `wt-mig1` of campaign commit `6aa9f67bc0b3181672d50eacb9d172e468070df3`. In the
> repository, `MIG1Draft.lean` is `audits/evidence/mig1/MIG1Draft.lean.txt`, `elaboration.log` is
> `audits/logs/mig1-draft-elaboration.log`, and the measurement scripts `work/*.py` are
> `audits/evidence/mig1/scripts/`; their data files are not kept. MIG-0a has since landed
> (PR #83) with the imports cited here, and MIG-0b's gate is issued (`audits/mig0b-pack.md`).

Statement-phase design for backlog row MIG-1 (`machine-library-design.md` §16, order of work
step 2), drafted 2026-10-13 against the campaign tip in `wt-mig1`. Measurements are in
`MIG1-inventory.md` (cited as *Inv.* §n); the representative statement draft is
`MIG1Draft.lean`, which elaborates with 0 errors and 26 `sorry` warnings (`elaboration.log`).
Figures marked ESTIMATE are estimates; all others are measured.

## 0. Summary

* **What MIG-1 does.** Every existential machine row of the eight named files (53 rows, plus
  `Complexity.timeConstructible_id`, whose definition hides the same existential; *Inv.* §1)
  gets a named public witness with spec theorems, and becomes a one-line corollary with its
  statement unchanged. The 304 `f2_` copies, the 45 `a2_` and the 7 `catalog_redirect*`
  declarations leave `Build/Catalog.lean`: the copies are deleted, and the new space proofs among
  them move next to their witnesses. The 20 Catalog space rows become short corollaries in place.
  The six R3 canonical `_run` rows retire, with their five consumer citations edited.
* **Witnesses:** 26 new public definitions (24 machines and the call's two anchor states), plus
  spec theorems for 2 existing public machines (`bufferedCompTM`, `redirectTM`): 28 in all
  (§3). 51 spec theorems and 4 supporting lemmas (ESTIMATE until stage S fixes the list; §3).
* **Style decision:** spec theorems in the library's existing style, not as MIG-0a `Contract`
  instances (§2).
* **Size:** net about −7.4k lines (ESTIMATE, range −6.9k to −7.8k; §12), against the backlog's
  −7.6k to −8.3k plus 0.4k: about 2.4k of the region's lines are new proofs that move rather than
  go. Catalog shrinks from 12,752 to about 3.3k lines (ESTIMATE).
* **Measured figures** against the backlog: 304 copies and 22 region publics reproduce; 66 rows,
  6,255 verbatim lines and "0 external consumers" of the R3 rows do not (*Inv.* §0).

## 1. Scope and invariants

**Rule.** Design §2: constructive layers export named machines with spec theorems; existential
packaging appears only at the consumer layer. §16 decision 1 lifts §8's byte-identity and
decision 12.2's byte-identical `Primitives`; decision 2 (scenario B) retires the R3 canonical
`_run` rows with their consumers edited.

**Invariants.**
1. Every one of the 53 rows and `timeConstructible_id` keeps its statement byte for byte, its
   name and its home module. Their 221 external citations in 35 files (*Inv.* §1) are untouched.
2. Witness bodies are moved or renamed, never changed (code identity modulo the rename map).
3. No row is ever proved through a `sorry`: a row's proof is swapped onto its witness only once
   the witness's spec theorems are proved (§8).
4. The only retired public statements are the six R3 canonical `_run` rows.
5. Two public head lemmas, `rewind_scan_heads` and `rewind_heads`, move from Catalog to
   `TuringMachine/Simulation.lean` (next to `timed_rewind`, which they refine) with their full
   names unchanged, so their three consumers (*Inv.* §2.2) are untouched.

**Out of scope.** The framed R3 rows and `_spaceUsedByTape` rows (MIG-11 makes them Contract
instances); the other Build files' existential rows (CfgRecord 3, RecordTable 6, OracleSim 4,
InputCall 2, Zone 2, CertShell 1, EmitIterBody 1, InputLength 1, and in the core CodeSimulator 2,
MathlibBridge 2, Universal 4; *Inv.* §0 note a); MIG-9's
counter unification; TMSAT's private polynomial machine (*Inv.* §4).

## 2. Contract instances or the existing style: existing style

**Decision.** The spec theorems are stated in the existing style: `ComputesInTime` /
`ComputesFunInTime` with explicit constants, `spaceUsed` bounds from `initCfg`, and, for the
loop and the call, the existing `Cfg.ofWords` seam statements with their witnesses named. The
draft carries no copy of the MIG-0a contract file.

**Reasons.**
1. **Layering forbids it.** The MIG-0a file imports `Build/Catalog` and `Build/Seam`
   (`audits/evidence/mig0/Contract-proposed-r2.lean.txt`, lines 6–8). Catalog itself and five
   home files (Composition, Simulation, Wrappers, Encoding, Loop) are in Catalog's import
   closure, so they cannot import it. Primitives and TimeConstructible could today, but not once
   MIG-1's corollaries make Catalog import Primitives, and through it TimeConstructible
   (*Inv.* §4). The core contract module that `Loop` could import is MIG-0b item 4, still being
   drafted. Contract-shaped specs would make MIG-1 wait on MIG-0b and its gate, against §16's
   order of work (MIG-1 is step 2, "no new infrastructure"; Contract instances are step 3).
2. **The shapes do not fit.** 28 of the 34 home rows are whole-machine function computations
   from `initCfg` to a halt, judged by the output (*Inv.* §1). A `Contract` is a first-exit
   contract with a full endpoint configuration, an exact time and per-tape intervals through the
   endpoint. Today's proofs determine neither the endpoint's work tapes nor an exact halting time
   for most witnesses; a Contract instance would have to take `post := M.runFrom d time` and
   `time := Nat.find …`, which adds no content. The space rows bound `spaceUsed` at every time
   from `initCfg`, not inside an interval envelope.
3. **Named witnesses come first anyway.** A `Contract M …` needs a named `M`; an existential row
   cannot be one. MIG-1 is therefore a prerequisite of MIG-11 and MIG-17, not a competitor.
4. **The Contract-shaped rows are kept ready.** Only the call rows (seam to seam, first positive
   exit) and the loop's configuration family (a round structure, MIG-0b's round layer) have
   contract shape. `callTM_install` and `callTM_emit` keep today's positive-only cut; since the
   landed `callEntry` and `callExit` are distinct (different summands of the state type), the
   full cut follows, which is exactly MIG-0a's entry/exit case split (design §16a, round-1
   minor 5). MIG-17 then packages them without restating.

## 3. The named witnesses

Names are public, in `Turing.FinTM` unless stated; "today" is the private name the body comes
from (*Inv.* §1). Constants are today's, made explicit. `k` lemmas (`W.k = n`, `rfl`) accompany
every witness whose space corollary needs its tape count.

| # | Witness (home) | Signature | Today | Spec theorems (shape) | Rows served |
|---|---|---|---|---|---|
| 1 | `idTM` (Composition) | `FinTM Bool` | `idTM` | `idTM_computes x : ComputesInTime x x (|x| + 1)`; `idTM_k : k = 0` | id; id space |
| 2 | `constTM` (Composition) | `List Bool → FinTM Bool` | `constTM` | `constTM_computes w x : ComputesInTime x w (|w| + 1)`; `constTM_k` | const; const space; inside 13, 14, 16 |
| 3 | `ifEqTM` (Composition) | `List Bool → List Bool → List Bool → FinTM Bool` | `ifEqTM` | `ifEqTM_computes : ComputesFunInTime (fun w => if w = w₀ then u else v) (fun n => (|w₀| + max |u| |v| + 3)·(n + 1))` | ifEq |
| 4 | `condTM` (Composition) | `FinTM Bool → FinTM Bool → FinTM Bool → FinTM Bool` | `condTM` | `condTM_computes_iff (hD) : ∀ x w, (∃ t, ComputesInTime x w t) ↔ ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t` | `exists_cond` |
| — | `bufferedCompTM` (existing, Simulation) | | public | `bufferedCompTM_computesInTime` (exists, public); new: `_computesFunInTime` (comp's body, constant 2), `_computesFunInTime_on_image`, `_computes_iff` (comp_partial's body) | comp, comp_on_image, comp_partial |
| 5 | `timedCondTM` (Wrappers) | `FinTM Bool → FinTM Bool → FinTM Bool → FinTM Bool` | `timedCondTM` | `timedCondTM_computes : ComputesFunInTime (if p x …) (fun n => 5·(T₀ n + max (T₁ n) (T₂ n) + 1))`; `timedCondTM_spaceUsed (hD : D.ComputesInTime x [b] T) : space ≤ D-space at T + branch space + 2`; `timedCondTM_k`; plus `branchTM_spaceUsed` (Simulation) | cond; cond space; inside 16 |
| — | `redirectTM` (existing, Wrappers) | | public | `redirectTM_runFrom` (today's private `redirect_run`, the configuration correspondence) | `redirectTM_spaceUsedByTape` |
| 6 | `Turing.pairDiagTM` (Encoding) | `FinTM Bool` | `pairDiagTM` | `pairDiagTM_computes x : ComputesInTime x (pairEncode x x) (4|x| + 5)`; `pairDiagTM_k` | pairEncode_diag; **pairDup** (replaces `pairDupTM`); pairDup space |
| 7 | `toCodeTM` (Encoding) | `(M : FinTM Bool) → M.k = 1 → CodeTM` (noncomputable) | anonymous `⟨card Q − 1, tm.relabelState e⟩` | `toCodeTM_computesInTime_iff : (M.toCodeTM hk).toFinTM.ComputesInTime x o t ↔ M.ComputesInTime x o t` | `exists_codeTM` |
| 8 | `lengthBitsTM` (TimeConstructible) | `FinTM Bool` | `Complexity.counterTM` | `lengthBitsTM_computes : ComputesFunInTime (Nat.bits |x|) (5·(n + 1))`; `lengthBitsTM_spaceUsed : space ≤ 5·(Nat.size |x| + 1)` | `timeConstructible_id`; lengthBits; lengthBits space; inside 14, 18, 19 |
| 9 | `prependTM` (Primitives) | `List Bool → FinTM Bool` | `catalogPrefixTM` | `prependTM_computes w : ComputesFunInTime (w ++ ·) (|w| + n + 1)`; `prependTM_k` | prepend, pairEncodeFixed; both space rows |
| 10 | `incFixedTM` (Primitives) | `FinTM Bool` | `incFixedTM` | `incFixedTM_computes x : ComputesInTime x ((incFixed x).getD []) (3(|x| + 1))`; `_k` | incFixed; space |
| 11 | `pairValidTM` (Primitives) | `FinTM Bool` | `pairValidTM` | `pairValidTM_computes x : ComputesInTime x [(pairDecode x).isSome] (|x| + 1)`; `_k` | pairValid; space |
| 12 | `pairExtractTM` (Primitives) | `Bool → Bool → FinTM Bool` | `pairExtractTM` | `pairExtractTM_computes` (general, 5(|x| + 1)); `_fst`, `_snd`, `_concat` (ComputesFunInTime forms); `_k : k = 1` | pairFst, pairSnd, pairConcat; their 3 space rows; inside 15, 16 |
| 13 | `polyUnaryTM` (Primitives) | `ℕ → ℕ → FinTM Bool` (`0 ↦ constTM`, `d+1 ↦` engine) | case split inside proofs; engine `catalogPolyUnaryTM` stays private | `polyUnaryTM_computes : ComputesFunInTime (replicate (C(|x|+1)^e) true) ((C + 5e + 4)((n+1)^e + n + 1))`; `polyUnaryTM_spaceUsed : space ≤ 5e(|x| + 1)` | polyUnary; space; inside 14, 15 |
| 14 | `polyBitsTM` (Primitives) | `ℕ → ℕ → FinTM Bool` | existential composite | `polyBitsTM_computes : ComputesFunInTime (Nat.bits (C(|x|+1)^e)) ((7C + 5e + 11)(n+1)^(e+1))` (ESTIMATE of the constant; fixed at stage S); definition: `if C = 0 then constTM [] else` `constTM (Nat.bits C)` at `e = 0`, `bufferedCompTM (polyUnaryTM C e) lengthBitsTM` otherwise, the case split of today's space proof (its round-1 finding 5) | polyBits; space |
| 15 | `pairLenCheckTM` (Primitives) | `ℕ → ℕ → FinTM Bool` | `pairCountTM G`, `G` existential | `pairLenCheckTM_computes : ComputesFunInTime (…) ((C + 5e + 17)((n+1)^e + n + 1))`; definition `pairCountTM (bufferedCompTM (pairExtractTM true false) (polyUnaryTM C e))` | pairLenCheck; space |
| 16 | `stripLastTM` (Primitives) | `FinTM Bool` | existential | `stripLastTM_computes : ComputesFunInTime (…) (K·(n + 1))`, linear (today's `f2_strip_linear`; `K` fixed at stage S); definition `timedCondTM (bufferedCompTM (pairExtractTM false true) anyTrueTM) rawStripTM (constTM [])` | stripLast (quadratic row, from the linear spec); space |
| 17 | `pairMapSndTM` (Primitives) | `FinTM Bool → FinTM Bool` | Catalog's `a2_mapTM Mg true` | `pairMapSndTM_computes (hg) (hTg) : … (22(n + 1 + Tg n))`; `pairMapSndTM_spaceUsed (Sg hgs hSg) : space ≤ Sg |x| + 22(|x| + 1)` | **pairMapSnd** (replaces `pairMapTM`); space |
| 18 | `splitSolveTM` (Primitives) | `ℕ → ℕ → FinTM Bool` | `splitSolve_closed`'s existential | `splitSolveTM_computes : … (K(n+1)^(e+2))`; `splitSolveTM_spaceUsed : space ≤ K(|x|+1)^(e+1)`; definition `loopHostTM (splitBodyTM source start) lengthBitsTM .anchor true` with today's per-`e` source | splitSolve; space |
| 19 | `splitSolveWithTM` (Primitives) | `(ℕ → ℕ) → FinTM Bool → FinTM Bool` | `emitterP2_closed`'s existential | `splitSolveWithTM_computes (hTE) (hE) : … (K_E(n+1)(TE(n+1) + n + 2))`; definition over `callTM E false`, `callTM lengthBitsTM false` and `loopHostTM` | splitSolveWith |
| 20 | `unaryTokenTM` (Primitives) | `FinTM Bool` | `emitterTokenTM` | `unaryTokenTM_computes : ComputesFunInTime (…) (3(n + 1))` | unaryToken |
| 21 | `appendBitTM` (Primitives) | `Bool → FinTM Bool` | `emitterAppendTM` | `appendBitTM_computes b x : ComputesInTime x (x ++ [b]) (|x| + 1)` | appendBit |
| 22 | `loopHostTM` (Loop) | `(body F : FinTM Bool) → body.State → Bool → FinTM Bool` | `loopHostM body F anchor false findMode` (`loopHost`) | `loopHostTM_contracts` (today's `loopHost_contracts`, constant 10); `loopHostTM_decides`, `loopHostTM_finds` (constant 10); `loopHostTM_spaceUsed` (decision mode, `19·k·(S + T + 1)`); `loopHostTM_spaceUsed_le_budget` (find mode, `c·(T + 1)`, today's `f2_exists_loopFind_space`, for 18) | loopCfg, loop, loopFind; loop space; inside 18, 19 |
| 23 | `emitLoopTM` (Loop) | `(body F : FinTM Bool) → body.State → FinTM Bool` | `emLoopHost body F anchor true` | `emitLoopTM_computes : ComputesFunInTime (flatMap emitF …) (10(T n + 1)(R n + 2))` | emitLoop |
| 24 | `callTM` (Loop) | `FinTM Bool → Bool → FinTM Bool` | `emCallTM` | `callTM_k_pos`; `callTM_install`, `callTM_emit` (today's `emCall_first`, coefficient `24 + 13·k_M`) | installCall, emitCall; inside 19 |
| 25–26 | `callEntry`, `callExit` (Loop) | `(M : FinTM Bool) → (emit : Bool) → (callTM M emit).State` | `q₀`, `.inr (.inr 5)` | (used by 24's specs) | installCall, emitCall |

Two more public lemmas: `Turing.FinTM.ComputesInTime.spaceUsed_le` (Catalog, today's private
`f2_space_of_time`; proved in the draft) and a run form of `workTapePos_step_le`
(`MultiTapeTM.workTapePos_runFrom_le`, Simulation; today's private `f2_head_steps`, which
backlog F6-1(g) retires with MIG-1, and the form `h1Run_headBound` of F7-1(a)).

**Naming decisions.** Private names are kept where they read well and renamed where they carry
an origin tag: `catalogPrefixTM → prependTM`, `emitterTokenTM → unaryTokenTM`,
`emitterAppendTM → appendBitTM`, `emCallTM → callTM`, `loopHostM → loopHostTM` (the `forward`
flag stays inside: `emitLoopTM` is the forwarding instance), `Complexity.counterTM →
Turing.FinTM.lengthBitsTM`. The last is declared in `ClassP/TimeConstructible.lean` under its
`Turing.FinTM` name, outside the file's `Complexity` namespace, so that MIG-9 can move it into
`Build/` without renaming; it stays in TimeConstructible now because `timeConstructible_id` needs
it and Primitives imports TimeConstructible.

**Two consolidations** (statement-preserving, open question 2): `computesFunInTime_pairDup`
moves onto Encoding's `pairDiagTM`, which computes the same function with no work tapes, and
`pairDupTM` with its four private lemmas retires (138 lines); `computesFunInTime_pairMapSnd`
moves onto the forwarding controller that its own space row already uses, and the
captured-payload `pairMapTM` with its 15 private lemmas retires (447 lines; *Inv.* §4). The
second also removes a witness that the F2 gate showed cannot carry the space claim.

## 4. Each row as a corollary

Five patterns, all exercised in `MIG1Draft.lean`, whose `row_*` theorems prove `type_of% @row`
(the landed row's own type) from the specs:

* **A, one line:** `⟨W, c, W_computes⟩` (with `.mono` when the spec is stated per input).
* **B, space with no work tapes:** A plus `spaceUsed_zero_tapes_eq_zero _ _ W_k`.
* **C, space from time:** A plus `ComputesInTime.spaceUsed_le` and the tape count (pairFst,
  pairSnd, pairConcat, polyBits, pairLenCheck, stripLast: today's proofs already argue this way).
* **D, space from the witness's own spec:** `⟨W, c, W_computes, W_spaceUsed⟩`, with one
  constant for both clauses (lengthBits, polyUnary, pairMapSnd, cond, loop, splitSolve).
* **E, configuration level:** the loop and call rows instantiate `loopHostTM_contracts`,
  `callTM_install`, `callTM_emit`.

| Row | Pattern | In the draft |
|---|---|---|
| `computesFunInTime_id`, `_const`, `_ifEq`, `_prepend`, `_pairEncodeFixed`, `_pairValid`, `_incFixed`, `_pairDup`, `_unaryToken`, `_appendBit`, `Turing.computesFunInTime_pairEncode_diag` | A | id, const, pairDup, pairEncode_diag |
| `computesFunInTime_lengthBits`, `Complexity.timeConstructible_id` | A | both |
| `computesFunInTime_pairFst`, `_pairSnd`, `_pairConcat` | A over `_fst`/`_snd`/`_concat` | fst, snd |
| `computesFunInTime_polyUnary`, `_polyBits`, `_pairLenCheck`, `_stripLast`, `_splitSolve`, `_splitSolveWith`, `_pairMapSnd`, `_cond` | A, with an arithmetic `mono` where the row's bound is coarser | polyUnary, pairMapSnd, cond |
| `computesFunInTime_comp`, `exists_comp_on_image`, `exists_comp_partial`, `exists_cond`, `Turing.exists_codeTM` | A over the iff or composition spec | — |
| `exists_loopCfgTM`, `exists_loopTM`, `exists_loopFindTM`, `exists_emitLoopTM` | E / A | all but emitLoop |
| `exists_installCallTM`, `exists_emitCallTM` | E | both |
| Catalog: `_id_`, `_const_`, `_prepend_`, `_pairEncodeFixed_`, `_pairValid_`, `_pairDup_`, `_incFixed_spaceUsed` | B | id, const, pairDup |
| Catalog: `_pairFst_`, `_pairSnd_`, `_pairConcat_`, `_polyBits_`, `_pairLenCheck_`, `_stripLast_spaceUsed` | C | fst, snd |
| Catalog: `_lengthBits_`, `_polyUnary_`, `_pairMapSnd_`, `_splitSolve_`, `_cond_spaceUsed`, `exists_loopTM_spaceUsed` | D | lengthBits, polyUnary, pairMapSnd, cond, loop |
| Catalog: `redirectTM_spaceUsedByTape` | 6 lines over `redirectTM_runFrom` | — |

## 5. The deletion plan for the region

The region (Catalog 1779–11361, 9,583 lines; *Inv.* §2.1) is replaced by about 340 lines
(ESTIMATE): the 19 existential space rows and `redirectTM_spaceUsedByTape` as corollaries (their
statements and first docstring paragraphs kept, the witness-specific sketches dropped), and
`ComputesInTime.spaceUsed_le`. Catalog gains
`import TCSlib.Complexity.TuringMachine.Build.Primitives` (acyclic; *Inv.* §4). Each region
declaration goes one of five ways:

| Fate | Declarations | Lines (with docstrings) |
|---|---|---|
| **Deleted, the original is used:** 253 of the 257 `f2_` copies with a same-named source (232 identical, 21 modified loop-host copies; the moved proofs are re-targeted at the originals) and the 7 `catalog_redirect*` copies | 260 | 5,425 |
| **Deleted, dead:** 11 new `f2_` declarations reached from no public row, and `a2_heads_halted` | 12 | 213 |
| **Absorbed** into spec theorems whose proofs are today's home-row bodies: `f2_counter_computes`, `f2_strip_linear`, `f2_cond_time`, `f2_unary_sharp`; replaced by public lemmas: `f2_space_of_time`, `f2_head_steps` | 6 | 182 |
| **Moved** to the witness's home, renamed and re-targeted (table below): 30 new `f2_`, 4 modified split copies, 44 `a2_` | 78 | 2,382 |
| Public rows, rewritten in place as corollaries; `rewind_*` moved to Simulation | 22 | 992 → about 340 |

| Moved family | Destination | Declarations | Lines today |
|---|---|---|---|
| counter space (`f2_counter_count_space`, `_heads`, `_space`) | TimeConstructible, `lengthBitsTM_spaceUsed` | 3 | 113 |
| branch space (`f2_finSumEquiv`, `f2_sum_add`, `f2_branch_space`) | Simulation, `branchTM_spaceUsed` | 3 | 70 |
| conditional ledger (`f2_condHeads`, `_control_heads`, `_branch_heads`, `_read_heads`, `f2_cond_ledger`, `f2_cond_space`) | Wrappers, `timedCondTM_spaceUsed` | 6 | 157 |
| polynomial space (`f2_polyHeads`, `_bounds`, `f2_poly_step`, `f2_poly_space`) | Primitives, `polyUnaryTM_spaceUsed` | 4 | 196 |
| forwarding map (30 `a2_map*` declarations) | Primitives, `pairMapSndTM` and its specs | 30 | 751 |
| pair and split helpers (`f2_catalogPair_inverse`, `f2_first_length`, `f2_splitEmbed_run`, and the space-threaded `f2_splitBody_round`, `f2_splitSolve_of_body`, `_source`, `_closed`, which replace their time-only originals in Primitives) | Primitives, `splitSolveTM_spaceUsed`, `pairLenCheckTM`, `stripLastTM` | 7 | 306 |
| loop space (`f2_loop_live_prefix`, `_input_move_le`, `_input_run_le`, `f2_loopHost_body_capture`, `_fuel_rewind`, `_payload_rewind`, `f2_loopCall_heads`, `f2_segment_heads`, `f2_space_radius`, `f2_seamed_space`, `f2_exists_loopFind_space`) and 14 `a2_` loop ledger lemmas | Loop, `loopHostTM_spaceUsed` and `_le_budget` | 25 | 789 |

The moved code is a disclosed move, not a copy: the fill batches that receive it take it from
the base Catalog, and the Catalog batch deletes it (§9). The combined head must contain each
moved declaration once (the full gate's duplication screen).

## 6. The space rows as corollaries

Of the region's 22 public declarations (*Inv.* §2.2), 20 are space rows and stay in Catalog,
each a corollary by pattern B, C or D (or the redirect form); their statements and names are
unchanged, and the four with external consumers (id, prepend, lengthBits, polyUnary: 5
citations in `Inclusions` and `Constructible`) are untouched. The two head lemmas move to
Simulation (§1, invariant 5). Seven witnesses carry their own space theorem, because their
space argument depends on their run structure: `lengthBitsTM`, `polyUnaryTM`, `pairMapSndTM`,
`timedCondTM` (with `branchTM_spaceUsed`), `splitSolveTM`, `loopHostTM` (two), and
`redirectTM` (through `redirectTM_runFrom`). The other 13 space rows need only time specs, the
tape count and `ComputesInTime.spaceUsed_le`. The scope note of `exists_loopTM_spaceUsed`
(round-1 note R10: no space clause for the configuration and find forms) is unchanged; the
find-mode budget theorem is public now because `splitSolveTM_spaceUsed` needs it, and is the
space clause R10 said would be commissioned by a consumer.

## 7. Retiring the R3 canonical `_run` rows

The six rows (237 lines) specialize the framed `_run_ofCfg` rows to `Cfg.ofWords` starts by a
`Cfg.ext` computation of about 20 lines each (*Inv.* §3). The backlog's "0 external consumers"
does not hold: `copyTM_run` is cited at `CertShell:571` and `CodeSimulator:1291`, and
`transferTM_run` at `CertShell:585, 589, 602`. Plan:
1. Add two canonical-word lemmas to Catalog's Part 1, stated once instead of per routine: the
   framed endpoint "destination interval holds `w`" from a `Cfg.ofWords` start with a blank
   destination is `Cfg.ofWords q' (Function.update w dst u)`, and its transfer variant (source
   also cleared). New public statements, so in the statement gate.
2. Each consumer site calls `copyTM_run_ofCfg`/`transferTM_run_ofCfg` and rewrites with the
   lemma: about 3 more lines per site (ESTIMATE).
3. Delete the six rows and their two docstring mentions in CertShell.

`CertShell` is closed (wave-1 gate); `CodeSimulator` belongs to the B5a continuations in flight,
so the site at `:1291` is edited only after B5a's continuation integrates (open question 1).

## 8. Order of work

1. **Stage S, statements (maintainer, one PR, statement gate).** The 26 definitions are made
   public under their final names by an asserted scripted rename in each home file (bodies
   unchanged); the spec theorems and the supporting lemmas are added; the two head lemmas move to
   Simulation. A spec whose proof is a citation of an existing private lemma is proved at once
   (for example `pairExtractTM_computes`, `pairValidTM_computes`, `incFixedTM_computes`,
   `prependTM_computes`); every other spec lands `sorry`. **No row's proof changes in stage S**,
   so no proved row comes to depend on a `sorry`. Gate evidence: the extension of
   `MIG1Draft.lean` to all 54 rows (every row a `type_of%` corollary of the gated specs), the code
   identity of each renamed body, the name screen re-run on the final list, and the acyclicity
   of the new import.
2. **Stage F, fills (four parallel batches, §9).** Each batch proves the sorried specs of its
   files, by moving a row's body into its spec (28 of the 34 home rows: all of Composition,
   Wrappers, Encoding and Loop, and 12 of Primitives, with `timeConstructible_id`) or by moving
   Catalog's proofs (the seven space specs, `branchTM_spaceUsed`, the six composite rows), then
   swaps each row onto its witness. The Catalog batch deletes the region and retires the R3 rows.
3. **Stage G, full gate.** Retired statements (the six R3 rows) and consumer edits; freeze,
   replay, axioms, duplication.

**Which witnesses first.** First the 16 whose specs are today's in-file proofs (witnesses 1–4,
6, 7, 9–12, 20, 21, 23–26), `bufferedCompTM`'s specs, and the time specs of 5, 8, 13 and 22:
relocations inside one file, which give named witnesses to 28 home rows and
`timeConstructible_id`. Next the lower-layer space specs
(`lengthBitsTM`, `timedCondTM`, `branchTM`, `redirectTM`), then `loopHostTM`'s space specs (the
risk concentration, §11 item 1), then the six composites (14–19), whose definitions use
witnesses 2, 5, 8, 9, 12, 13, 22 and 24 and whose split-search space needs the loop's budget
theorem. Catalog comes last, because every corollary there cites a home spec.

## 9. Batching for fill agents (disjoint file ownership)

| Batch | Owns | Work | Depends on (stage S statements) |
|---|---|---|---|
| F-A | `Composition`, `Simulation`, `Wrappers`, `Encoding`, `TimeConstructible` | the in-file specs of witnesses 1–8 and of `bufferedCompTM`; move and prove `lengthBitsTM_spaceUsed`, `timedCondTM_spaceUsed`, `branchTM_spaceUsed`, `redirectTM_runFrom`, the run-form head lemma; swap the 10 rows of these files and `timeConstructible_id` | — |
| F-B | `Primitives` | the in-file specs of witnesses 9–13, 20, 21; move and prove `polyUnaryTM_spaceUsed`, the composites 14–19, `pairMapSndTM` (the 30 `a2_map*`), `splitSolveTM_spaceUsed` (modulo F-C's budget theorem); swap the 18 rows; retire `pairMapTM` and `pairDupTM` | F-A's and F-C's specs |
| F-C | `Loop` | the in-file specs of witnesses 22–26 (today's `loopHost_contracts` with its constant made explicit, the summations, `emCall_first`); move and prove `loopHostTM_spaceUsed`, `_le_budget` (the loop family, re-targeted at `loopHostM`); swap the 6 rows | F-A's specs |
| F-D | `Catalog`, `CertShell` (and `CodeSimulator:1291`, after B5a) | delete the region; write the 20 corollaries and `ComputesInTime.spaceUsed_le`; add the Primitives import; retire the R3 rows and edit their consumers | all specs |

F-B and F-C read the base Catalog for the code they move; F-D deletes it. Integration order:
F-A, F-C, F-B, F-D (or one integration of all four), so that every merged head has every row
proved. Sizes (ESTIMATE): F-A about 0.5k lines moved or written; F-B about 1.3k moved, 0.85k
retired (the two consolidations and the split originals); F-C about 0.8k moved and re-targeted;
F-D about 9.5k deleted, 0.4k written. Screen populations: each batch's own files plus the base
Catalog (the move source), per the standing lesson that populations cover cited files.

## 10. Gates and replay closure

* **Statement gate** (stage S). Population: the 26 definitions, 51 spec theorems
  (ESTIMATE), `ComputesInTime.spaceUsed_le`, the run-form head lemma, the two canonical-word
  lemmas, and the two moved head lemmas (statements unchanged). Checks: names and homes; each
  spec's fidelity to today's private proof; the `type_of%` corollary file over all 54 rows;
  witness code identity modulo the rename map; the name screen; the acyclic new import.
* **Full gate** (stage G). Freeze: every public statement of the ten edited files unchanged
  except the six retired rows and the gated additions. **Replay closure: the ten edited files
  and everything importing them, 205 of the 623 modules** (*Inv.* §4), including 61
  colleague-owned `CircuitComplexity` modules and `TimeHierarchy/Separation`, replayed but not
  edited. Axiom probe: the 54 rows, the 20 Catalog space rows and every new spec, the standard
  three only, no `sorryAx`. Duplication screen over the combined head: no moved declaration twice,
  no `f2_`/`a2_` name left.

## 11. Risks

1. **The loop family's re-targeting (highest).** The 21 modified loop copies come from an older
   `Loop` (before `loopHostM … forward findMode`); the moved space proofs (about 800 lines) cite
   them. Measured: after removing the prefix, the old and the current host definitions differ only
   in the signature (the `forward` flag) and the body-dispatch line, which today goes through
   `loopBodyDispatch` (Loop:552–563), a `bif forward then … else captureAction …` whose `false`
   branch is the old line. So `loopHostM body F anchor false findMode` is very likely
   definitionally the old host; at F-C's start a `rfl` bridge should be tried, keeping most moved
   proofs as they are. Otherwise the phase lemmas are re-targeted one by one.
2. **Axiom regression.** Swapping a row onto a sorried spec would put `sorryAx` under 216
   external citations. Avoided by invariant 3 and the stage order.
3. **Universes, `Type*` versus `Type`.** Every witness is a `FinTM Bool` (`FinTM : Type → Type 1`,
   states in `Type`); MIG-1 introduces no universe parameter and does not engage MIG-0a's `Type`
   decision or UNIV-1. The R3 framed rows are stated for `{Symbol : Type*}`; consumers moving from
   the `Bool` canonical rows instantiate `Symbol := Bool`.
4. **Name clashes.** Screened (*Inv.* §4): no proposed full name exists except as the witness
   being renamed in its own home; `Complexity.polyUnaryTM` (TMSAT, private) resolves first in its
   namespace. The screen is re-run at stage S on the gated names.
5. **The colleague files with `open Turing`.** `TimeHierarchy/Separation.lean` opens
   `Turing.FinTM`, so every new `Turing.FinTM` name becomes visible there unqualified;
   `CircuitComplexity/Advice.lean` has a `Turing.FinTM` section. None of them mentions any
   proposed short name, bare or `FinTM.`-qualified (*Inv.* §4); they are replayed, never edited.
   A name added at the gate must pass the same screen.
6. **The new import edge.** Eight Catalog importers newly see Primitives and TimeConstructible
   (20 public names); screened clean.
7. **Public definitions over private helpers.** `polyUnaryTM`, `polyBitsTM`, `pairLenCheckTM`,
   `stripLastTM`, `splitSolveTM`, `splitSolveWithTM` unfold to private machines
   (`catalogPolyUnaryTM`, `pairCountTM`, `rawStripTM`, `anyTrueTM`, `splitBodyTM`,
   `emitterP2BodyTM`). Lean accepts this outside the module system; consumers use the specs.
   Revisit if the `module` system is adopted.
8. **Explicit constants of the composites** (14–19) are computed at stage S from today's proofs;
   a wrong constant blocks a fill. Pre-ship check: elaborate each composite time spec's proof
   sketch, or prove it at stage S where it is glue over proved specs.
9. **`toCodeTM`'s tape-count argument.** Today's proof eliminates `hk : M.k = 1` by destructuring
   `M`; the definition must match `⟨_, Q, hQ, dQ, tm⟩, rfl`, and is noncomputable
   (`Fintype.equivFinOfCardEq`). Benefit: RD-3's open space clause of the coding step becomes a
   lemma about `toCodeTM`.
10. **In-flight work.** Only §7 touches an in-flight file (`CodeSimulator`); `RecordTable` and the
    B5a files are replayed, not edited.
11. **Policy.** The 26 new public definitions need docstrings opening with statement prose (most
    private witnesses already have one); the moved proofs carry their sketches.

## 12. Size estimate (ESTIMATE)

| Item | Lines |
|---|---|
| Region deleted (9,583) less its replacement (about 340) | −9,240 |
| R3 canonical rows (237) less two canonical-word lemmas (about 40) | −200 |
| Moved proofs (2,382 lines today), after re-targeting | +2,380 |
| Time-only split originals in Primitives, replaced by the moved space-threaded versions | −260 |
| Spec statements and docstrings added in the home files (51 specs; about 30 are private lemmas made public) | +480 |
| Consolidations: `pairMapTM` family, `pairDupTM` family | −585 |
| Consumer edits (5 sites) | +15 |
| **Net** | **about −7.4k (range −6.9k to −7.8k)** |

Catalog goes from 12,752 lines to about 3.3k; Primitives grows by about 0.7k, Loop by about 0.9k.
The backlog's "−7.6k to −8.3k, +0.4k" assumed less code to move: about 2.4k of the region's lines
are new proofs (space arguments, the forwarding controller, the loop ledger) that must survive.

## 13. Relation to other rows

* **MIG-9** (one bit-length counter) builds on `lengthBitsTM`, named here in `Turing.FinTM`.
* **MIG-11 / MIG-17** state Contract instances over the named witnesses (§2, reason 4). MIG-17's
  "named loop hosts" is done by MIG-1 (open question 4).
* **MIG-20** needs the Catalog → Primitives import, which MIG-1 adds.
* **F6-1(g)** (`f2_head_steps`) and **F6-1(j)** (`f2_incFixed_cases`) are discharged.
* **F7-1(a)**'s `h1Run_headBound` can cite the run-form head lemma.
* **RD-3**: `exists_codeTM`'s space clause becomes a lemma about `toCodeTM`.

## 14. Open questions for the user

1. **When to retire `copyTM_run`, whose consumer `CodeSimulator:1291` is in flight (B5a).**
   *Recommendation:* sequence MIG-1's last PR after the B5a continuation integrates and retire all
   six rows there; if B5a is still out when the fills are done, retire five and leave `copyTM_run`
   to the B5a integration.
2. **The two consolidations** (`pairDup` onto `pairDiagTM`; `pairMapSnd` onto the forwarding
   controller, retiring `pairMapTM`). Both keep every statement and remove 585 lines.
   *Recommendation:* both.
3. **Where the 20 space rows live.** *Recommendation:* in Catalog, as corollaries (home and
   consumers unchanged), with only the witness-intrinsic proofs moved; a per-theme layout (12.2c
   option (c)) can move them later.
4. **MIG-17's "named loop hosts".** *Recommendation:* mark it done by MIG-1; MIG-17 keeps the
   Contract rebase of the loop hosts and of `splitSafe`/`SafeRun`, after MIG-0b.
