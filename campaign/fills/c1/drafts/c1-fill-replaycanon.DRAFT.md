# Ch3–4 fill campaign — C1, wave 2: the replay canonizer (`Turing.exists_replayCanonizer`, `NDCodeSimulator.lean`)

<!-- DRAFT (drafting agent), 2026-10-24, for megafill C. Drafting base: the campaign tip
`77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (TCSlib as after #155, #154 and the earlier batch;
#156 open). Pre-ship measured there, against a fresh bootstrap of the order list:
`campaign/fills/c1/drafts/c1-fill-replaycanon/preship-77f1eb4f/`. Issue-time items: @ANCESTOR@,
⟨BASE⟩, ⟨IN-FLIGHT⟩, the megafill banner, and re-running the pre-ship at the issue commit. -->

> **⟨Megafill C, item N⟩** (cover brief ⟨…⟩; addendum v2.5, Part 3). The preflight, the
> toolchain, the clone and the cache are done once for the whole queue. For this item: create its
> branch from the shared base (below), **re-bootstrap your order list**, then follow this brief.
> **Budget:** ⟨…⟩ from your branch's creation. Deliver a checkpoint zip after each checkpoint: the
> session may end at any time.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement**: `Turing.exists_replayCanonizer`, C1's host-contracts
    gate (`campaign/gates/12-c1-hosts-statements/`, PASS 0/0/11) and C1's design
    (`campaign/items/c1/C1-design.md`, the replay route of the user's decision 3);
  - **its consumer, landed:** the interpreter core `Turing.exists_ndInterpreterCore` (PR #151,
    gate 66) and the universal NDTM `Turing.exists_timed_universal_NDTM` (PR #154, gate 68), both
    proved modulo exactly your target. Your file has no other admission;
  - **the scheme and the compiler:** `Turing.EffectiveNDMachineCode` (`NDCodes`), the
    Mathlib bridge `Turing.codePrim_machine` and its `Primrec` building blocks
    (`MathlibBridge`), and the composition `Turing.FinTM.computesFunInTime_comp`
    (`Composition`);
  - **the layouts, with their published equations** (the ND inventory API, PR #118's family):
    `serializeK_eq`, `tableBitsK_eq`, `workReadsK_zero`/`_succ`, `actionBitsK_eq`,
    `NDTM.replayTM_q₀`/`_tr`, `NDTM.fixChoice_q₀`/`_tr`, the field encoders' case lemmas, and your
    file's proved bridge `CodeNDTM.serialize_eq_tableBitsK`;
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2.5**: Part 1, the resources and the cache for the Mathlib roots only, with the cache
    store logged first; **Part 3, the megafill**, under which this session runs), and the
    copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/c1/inputs/c1-fill-replaycanon/`): the import probe
    `C1RCImportProbe.lean.txt`, the route probe `C1RCRouteProbe.lean.txt` with its seal controls
    `C1RCSealControl.lean.txt`, the definitions probe `C1RCDefsProbe.lean.txt`, and the screen
    population; the order list
    `campaign/fills/c1/orders/c1-fill-replaycanon.txt`, the base sorry set, the screen base and
    the pre-ship log (`campaign/fills/c1/logs/c1-fill-replaycanon-*`).
- **The environment was set up once, at the session's start** (the cover brief; Part 1 of
  `campaign/standards/fill-environment-addendum.md` and its Part 3): the preflight, the
  toolchain, the clone and the cache for the whole queue's Mathlib roots. If Lean cannot start,
  Part 2 applies. **If Lean never runs, do not draft proofs blind.**
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-replaycanon @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  git rev-parse HEAD:TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean
  # must print e2cdab7b46ef1dc50e36f2504d92e78913c5bb1d
  # (the drafting base's blob, from git rev-parse; re-check at issue)
  ```

  Record the base hash in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-replaycanon.zip`. It
  contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - **the session's shared environment logs** (`evidence/logs/` at the clone's root: preflight,
    cache store, roots, cache fetch, manifest check), this item's bootstrap and final sweep logs
    with **each module's time and maximum memory**, and the axiom log;
  - the seal test's source, its controls and both outputs; both screen outputs; and
    `SHA256SUMS`.
- **Checkpoint zips.** After each checkpoint below, commit and write
  `fill-c1-replaycanon-cp<N>.zip` with the same contents as of that commit (the final sweep may
  be your module's check only), so that a lost workspace loses at most one checkpoint. Deliver
  the latest if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip ⟨BASE⟩.** Lines in this brief are those of the
  drafting base's tree, where `NDCodeSimulator.lean` is #151's landing (2,325 lines; 3 public, 22
  private); re-check them at issue. Every probe and measurement below was run there.
- **In flight, merging after your base and invisible to it:** ⟨IN-FLIGHT⟩ (at drafting: #156,
  `Build/Seam`; #135, chapter 7 onto `main`); on their own branches in this session, the other
  megafill items, among them **B5a** (`CodeSimulator`, upstream of your file: you cite only its
  unchanged `serializeK` and `serializeK_eq`). Cite nothing they add.

## Parallel batches this round

None in `NDCodeSimulator.lean`. Your consumers are landed: the core (#151) and the universal NDTM
(#154) lose their last admission when your target is proved.

## What this is

**C1's replay canonizer** (C1's design, the replay route). One target, frozen:
**`Turing.exists_replayCanonizer`** (line 96): for every effective nondeterministic scheme `c`, a
finite binary machine computing `α ↦ serializeK (c.decode α).tm.replayTM`, the fixed
three-work-tape serialization of the decoded machine's replay machine, within some time bound
`T` of `|α|` alone. `T` is arbitrary.

**The statement and its docstring, frozen verbatim** (lines 80–99):

```lean
/-- **The per-code replay canonizer.** For every effective nondeterministic scheme `c` there is
a finite binary machine computing, from a code `α`, the fixed three-work-tape serialization
`Turing.serializeK` of the decoded machine's replay machine `Turing.NDTM.replayTM` (choice tape
last), within some time bound `T` of `|α|` alone. The bound is arbitrary: each code's universal
constant absorbs it. [AB09, §1.4: a code is mapped to its canonical description]

**Proof sketch.** The scheme's canonizer computes `α ↦ (c.decode α).serialize`
(`Turing.EffectiveNDMachineCode.canonizer_computes`). A primitive recursive list function `g`
maps it to `serializeK (c.decode α).tm.replayTM`: it copies the header, splits the two tables
into records by `Turing.codeSkipActionK`, and re-emits them in the order of
`Turing.workReadsK 3`, the choice read innermost (the blank and `false` reads both select the
`false` record). Each record is decoded and re-emitted in the three-tape field order of
`Turing.actionBitsK`: the input move, the first two work-tape fields, then the choice tape's
field `(none, +1)` as the third, then the output and the successor. Compile `g` by
`Turing.codePrim_machine` and compose (`Turing.FinTM.computesFunInTime_comp`; the canonizer's
output length is at most its time). -/
theorem exists_replayCanonizer (c : EffectiveNDMachineCode) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun α => serializeK (c.decode α).tm.replayTM) T := by
  sorry
```

**Where it stands.** The route is the docstring's, and every piece of it is published. The
pre-ship's route probe (below) proves, sealed, the composition step with `g` abstract and the
record-level identities `g`'s correctness rests on. What is open is `g` itself: its definition,
its correctness on serializations, and its primitive recursiveness.

**Proved modulo, exactly:** none. The machine lemmas the route cites are admission-free
(`codePrim_machine`, `computesFunInTime_comp`, `ComputesInTime.mono`: the standard three axioms,
in the import probe's output). **A complete delivery has no `sorryAx` in your target**, and then
`Turing.exists_ndInterpreterCore` and `Turing.exists_timed_universal_NDTM` have none either.

**Read first:**
- the target's docstring, whose sketch is binding where this brief does not refine it. One
  refinement: a record is widened **at bit level** (the choice field inserted after its first ten
  bits), not decoded to an `Action`: the two are equal by `rc_widen_record` (below), and only the
  bit-level form is primitive recursive with the published building blocks;
- the route probe `C1RCRouteProbe.lean.txt`: its proofs may be copied into your home as `rc_`
  privates;
- `MathlibBridge`'s building blocks and their proofs (`codePrimRepeat`, `codePrimPrefix`,
  `codePrimDrop`, `codePrimSkipActionK`, `CodeFormat.primrec_scan`): the model for `g`'s
  primitive recursiveness;
- `NDCodes`' `exists_effectiveNDMachineCode`: the scheme's canonizer, through
  `CodeFormat.exists_canonizer`.

**Pre-ship check** (drafting agent, at the drafting base; re-run at issue;
`campaign/fills/c1/logs/c1-fill-replaycanon-preship.log`):
- **Your file** elaborates with exactly one sorry warning, the target's (line 96).
- **The import probe** (`C1RCImportProbe.lean.txt`, a standalone import of your module, **102
  checks of 102 names**: every declaration this brief cites, TCSlib's and the core and Mathlib
  lemmas it names, and five axiom prints): 0 errors, 0 warnings. **Re-run it after your
  delivery**, extended by every further name you cite (count it "N checks of M names").
- **The route probe** (`C1RCRouteProbe.lean.txt`), sealed over 14 TCSlib definitions
  (`FinTM.ComputesFunInTime`, `FinTM.ComputesInTime`, `MultiTapeTM.ComputesInTimeAndSpace`,
  `serializeK`, `NDTM.replayTM`, `NDTM.fixChoice`, `CodeNDTM.serialize`, `tableBitsK`,
  `workReadsK`, `actionBitsK`, `signBits`, `optOptBoolBits`, `pairEncode`, `unaryFin`; none carries
  `@[simp]`): 0 diagnostics; its 7 headline proofs on `[propext, Classical.choice, Quot.sound]` or
  fewer. Its controls (`C1RCSealControl.lean.txt`, 15 `rfl`/`exact` goals): every one closes
  unsealed and fails sealed, each at its own goal.
- **The definitions probe** (`C1RCDefsProbe.lean.txt`): the recommended definitions below
  elaborate, and **by evaluation** (`#eval`, not a proof) `rc_g` maps the fixed serialization of
  two concrete coded machines to their replay serializations exactly (732 → 1,407 and
  1,545 → 2,949 bits). `decide` does not reduce these terms (well-founded recursion in
  `Nat.bits`): the correctness proof is by the layouts' equations, as the route says.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `NDCodeSimulator.lean:96` | `Turing.exists_replayCanonizer` (frozen statement) |

Your regions:
- **(a) the home**, the blank line 79, between the bridge's last line (78) and the target's
  docstring (80), inside `namespace Turing`: your `private` declarations, each after what it uses
  and before its first consumer. `private` only, and no `section`, `open` or `variable` that
  leaks past one (`open … in` on one declaration is fine).
- **(b) the body**, the `sorry` on line 99.
- **(c) for a partial only, a paragraph headed `**Implementation status.**`** at the end of the
  target's docstring, before its closing ` -/` (end of line 95). It is public-facing library text:
  what is proved and what is open, in mathematical terms, with no campaign labels (brief, gate,
  finding or escalation names), no dates and no session narrative. The same holds for the docstrings
  of your new declarations; provenance goes in `REPORT.md`. **Every new declaration has a docstring,
  and every proof over 20 lines a literal `**Proof sketch.**` paragraph** (`policy.md` §3; the
  canonizer's and the seam layout's landings each needed a follow-up PR for missing ones).

Frozen: the module header, docstring and imports (none is needed: `MathlibBridge` and
`Composition` are in your closure), the bridge, the target's statement and its docstring before
(c), every other declaration (the core and its 22 privates included), and every other file. The
maintainer updates the module's status text at integration.

### The route (binding where it names a row)

**The shape.** `g` is a private `rc_g : List Bool → List Bool` with two contracts, which are all
the composition reads:
- `rc_g_serialize : ∀ M : CodeNDTM, rc_g M.serialize = serializeK M.tm.replayTM`;
- `rc_g_primrec : Primrec rc_g`.

The definitions below are **recommended**; you may restate them (report each change). The two
contracts and the composition are binding.

1. **The composition** (the probe's `c1rc_compose`, sealed; copy it): compile `rc_g` by
   `Turing.codePrim_machine` (time `TG`, arbitrary and not monotone); make the bound monotone,
   `fun n => (Finset.range (n + 1)).sup TG` (`Finset.sup_mono`, `Finset.range_subset_range`), and
   weaken to it by `Turing.FinTM.ComputesInTime.mono` with `Finset.le_sup`, through
   `Turing.FinTM.computesFunInTime_iff`; compose with the scheme's
   `EffectiveNDMachineCode.canonizer_computes` by `Turing.FinTM.computesFunInTime_comp`; identify
   `rc_g ∘ (fun α => (c.decode α).serialize)` with the target's function by `funext`,
   `Function.comp_apply` and `rc_g_serialize`. Do not use `exists_comp_on_image`: it needs the
   intermediate length bound the composition lemma already supplies.
2. **The record-level identities** (all in the route probe, sealed; copy them):
   - `rc_choiceField`: the choice tape's field `optOptBoolBits none ++ signBits 1` is
     `[false, false, true, false]` (`optOptBoolBits_none`, `← SignType.pos_eq_one`,
     `signBits_pos`);
   - `rc_signBits_length`, `rc_optOptBoolBits_length`: two bits each, by cases and the case
     lemmas;
   - **`rc_widen_record`**: for `a : Action 2 Bool (Fin (n + 1))`,
     `actionBitsK ⟨a.inputTape, Fin.lastCases (none, 1) a.workTapes, a.output, a.state⟩ =
     rc_widen (actionBitsK a)`, where
     `rc_widen r = r.take 10 ++ [false, false, true, false] ++ r.drop 10` (`actionBitsK_eq` on
     both sides, `List.finRange_succ_last`, `Fin.lastCases_castSucc`/`_last`, `List.take_left'`,
     `List.drop_left'` at the ten-bit head);
   - `rc_workReads_snoc`: `workReadsK (k + 1) = (workReadsK k).flatMap fun w =>
     [none, some false, some true].map (Fin.snoc w)` (induction; `workReadsK_succ`/`_zero`,
     `Fin.cons_snoc_eq_snoc_cons`, and at `k = 0` `rc_cons_elim0`);
   - `rc_source_table`: `tableBitsK (N.fixChoice b).tr` as the nested `flatMap` of
     `actionBitsK (N.tr b q inp w)` (`tableBitsK_eq`, `NDTM.fixChoice_tr`);
   - `rc_replay_record`, **`rc_replay_table`**: `tableBitsK N.replayTM.tr` is the same nested
     `flatMap` emitting, per key `(q, inp, w)`, `rc_widen rF ++ rc_widen rF ++ rc_widen rT` with
     `rF`, `rT` the `false` and `true` records (`NDTM.replayTM_tr`, `Fin.snoc_last`,
     `Fin.snoc_castSucc`, `Option.getD_none`/`_some`: the blank and `false` choice reads select
     the `false` record).
3. **The split** (recommended definitions; `n` the decoded state count):

   ```lean
   private def rc_widen (r : List Bool) : List Bool :=
     r.take 10 ++ [false, false, true, false] ++ r.drop 10
   /-- One lockstep round: peel one record off each table, emit the key's three replay records. -/
   private def rc_round (n : ℕ) (p : List Bool × List Bool × List Bool) :
       List Bool × List Bool × List Bool :=
     match codeSkipActionK 2 n p.2.1, codeSkipActionK 2 n p.2.2 with
     | some f, some t =>
       let rf := p.2.1.take (p.2.1.length - f.length)
       let rt := p.2.2.take (p.2.2.length - t.length)
       (p.1 ++ (rc_widen rf ++ rc_widen rf ++ rc_widen rt), f, t)
     | _, _ => p
   /-- The table rewrite: find the `true` table, then `27 (n + 1)` lockstep rounds. -/
   private def rc_table (n : ℕ) (body : List Bool) : List Bool :=
     match codeSkipRepeat (codeSkipActionK 2 n) (27 * (n + 1)) body with
     | none => []
     | some tT => ((rc_round n)^[27 * (n + 1)] ([], body, tT)).1
   /-- Keep the header (doubled count, separator, unary initial state); rewrite the tables. -/
   private def rc_g (xs : List Bool) : List Bool :=
     match pairDecode xs with
     | none => []
     | some (u, v) =>
       match codeReadUnary v with
       | none => []
       | some (_, body) => xs.take (xs.length - body.length) ++ rc_table (codeBitsNat u) body
   ```

   Its correctness, by the key list `E = (List.finRange (n + 1)).flatMap fun q =>
   [none, some false, some true].flatMap fun inp => (workReadsK 2).map fun w => (q, inp, w)`
   (length `27 (n + 1)`: `(workReadsK 2).length = 9` from `workReadsK_succ`/`_zero`):
   - `rc_source_table` and `rc_replay_table` rewrite both tables as `flatMap`s over `E`
     (`List.flatMap_assoc`, `List.flatMap_map`);
   - **the skip**: `codeSkipRepeat (codeSkipActionK 2 n) |E| (tF ++ tT) = some tT`, by induction
     on `E` with `codeSkipRepeat_succ`, `codeSkipRepeat_zero` and `codeSkipActionK_append`;
   - **the rounds**, generalized over the accumulator and both suffixes: `|E|` rounds from
     `(acc, E.flatMap bF ++ restF, E.flatMap bT ++ restT)` reach
     `(acc ++ E.flatMap (fun e => rc_widen (bF e) ++ rc_widen (bF e) ++ rc_widen (bT e)),
     restF, restT)`, by induction on `E` (`Function.iterate_succ_apply`), each round by
     `codeSkipActionK_append` and `List.take_left'` at the length difference;
   - **the header**: `M.serialize = pairEncode (bits n) (unaryFin q₀ ++ (tF ++ tT))`
     (`CodeNDTM.serialize_eq_tableBitsK`); `pairDecode_pairEncode`; `codeReadUnary_append` after
     `unaryFin_eq` and `List.append_assoc`; `codeBitsNat_bits`; the kept prefix is
     `pairEncode (bits n) (unaryFin q₀)` (`pairEncode_eq`, `List.take_left'`); and the target is
     `pairEncode (bits n) (unaryFin q₀ ++ tableBitsK replay.tr)` (`serializeK_eq`,
     `NDTM.replayTM_q₀`).
4. **Primitive recursiveness**, by `Primrec.of_eq` from a composite of the building blocks:
   - `rc_widen`: `Primrec.list_append` of `take 10` and `drop 10`. **Mathlib has no
     `Primrec.list_take` at this pin**: write `r.take 10` as `r.take (r.length - (r.length - 10))`
     and use `Turing.codePrimPrefix` with `Primrec.nat_sub` (the probe's `c1rc_widen_primrec`);
     `drop` is `Turing.codePrimDrop`;
   - `rc_round`, as a `Primrec₂` in `n` and the triple: two nested `Primrec.option_casesOn` on
     `Turing.codePrimSkipActionK 2`, with `Primrec.list_append`, `Primrec.list_length`,
     `codePrimPrefix` and `rc_widen`'s proof;
   - `rc_table`: `Primrec.option_casesOn` on `Turing.codePrimRepeat (fun n => codeSkipActionK 2 n)
     (codePrimSkipActionK 2) (fun n => 27 * (n + 1)) …`, then `Primrec.nat_iterate` with the round,
     then `Primrec.fst`;
   - `rc_g`: `Primrec.option_casesOn` on `Turing.codePrimPair`, again on `Turing.codePrimUnary`,
     then `Primrec.list_append` of `codePrimPrefix` and `rc_table ∘ (Turing.codePrimBitsNat, ·)`.

   Prove each piece's equation (`of_eq`) by unfolding **your own** definitions only; read
   `codeSkipRepeat` through `codeSkipRepeat_zero`/`_succ` or `codeSkipRepeat_iter`.
5. **Edge cases that must stay true:** `numStates = 0` (one state, 27 records per table); a
   code whose decoding is any machine (`c.decode` is total; `rc_g` only sees serializations);
   `rc_g`'s value off the serializations is irrelevant (it may be `[]`).

**Promotion candidates** (notes only, in `REPORT.md`): `rc_workReads_snoc` (a general fact about
`workReadsK`, a candidate for `Build/StepBlock`'s published layout lemmas); the running-maximum
monotonization of an arbitrary bound (no such lemma is published).

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement: the bound `T` is arbitrary and depends on
  `|α|` alone; do not strengthen or weaken it.
- **Gate 66, note 8** (the core's fill gate): the replay canonizer is "plausible literally: the
  effective scheme already computes a valid fixed serialization; a computable finite-record
  conversion adds the choice-tape action and reorders the two tables into the replay table". This
  brief's `g` is that conversion.

## Cited infrastructure (public and proved at the issue commit; all in `C1RCImportProbe.lean.txt`)

The probe's 102 names: the target, the bridge and the scheme's fields; the composition step
(`codePrim_machine`, `computesFunInTime_iff`, `ComputesInTime.mono`, `computesFunInTime_comp`, and
Mathlib's `Finset.le_sup`, `Finset.sup_mono`, `Finset.range_subset_range`, `Finset.mem_range`,
`Function.comp_apply`); the layouts and their equations; the field encoders and their case
lemmas; the header and record readers with their append lemmas; the repository's `Primrec`
building blocks; Mathlib's `Primrec` combinators; the core and Mathlib list and tuple lemmas the
record-level proofs read. (`Primrec.nat_sub` is used in the route probe, not listed in the
import probe.)

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `NDCodeSimulator.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration.
3. **No new public declaration.**
4. **Escalation, item by item:** on anything unprovable as stated, stop **on that item only**,
   record the obstruction mathematically, and continue with every item that does not depend on
   it.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added; a Mathlib import only if a needed
   lemma requires it (flag it; none is expected).
7. **One proof per shared argument.** Cite `MathlibBridge`'s building blocks; never re-prove a
   reader's or skipper's primitive recursiveness, or the parser's append and erasure laws. Never
   re-walk the core's privates.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 2,325 lines; 3 public, 22 private).
9. **Continuation budget.** A partial zip states the checkpoint reached, the open declarations
   (each with a literal "Proof sketch") and the target's axiom walk. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, and no definitional closure either (a `rfl`,
      `exact`, `show`, `decide` or `simp` step that closes only because another file's
      definition reduces). Read every definition through its published lemmas: `serializeK`
      through `serializeK_eq`; `CodeNDTM.serialize` only through `serialize_eq_tableBitsK`;
      `tableBitsK`, `workReadsK`, `actionBitsK` through their equations; `NDTM.replayTM` and
      `NDTM.fixChoice` through their field equations; `signBits`, `optOptBoolBits` through their
      case lemmas; `pairEncode`, `unaryFin`, `codeReadUnary`, `pairDecode`, `codeBitsNat`,
      `codeSkipActionK`, `codeSkipRepeat` through theirs; `FinTM.ComputesFunInTime` through
      `computesFunInTime_iff`.
    - **Scope (user, 2026-10-23):** this binds TCSlib's own definitions. Core and Mathlib
      definitions may reduce in a `rfl`, `decide` or `show` step, but are never passed to `simp`,
      `rw` or `unfold`; use their equation lemmas (`Bool.toNat_true`, not `simp [Bool.toNat]`;
      `Function.comp_apply`, not `simp [Function.comp]`; `List.finRange_succ`, not
      `unfold List.finRange`).
    - **Your own file's definitions may be unfolded** (your `rc_` definitions).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete):
      - a **seal test**: a scratch copy of your module with `attribute [local irreducible]` on
        every other-file TCSlib definition your proofs mention (start from the route probe's 14
        and extend by every one you reach: at least `codeSkipActionK`, `codeSkipRepeat`,
        `codeReadUnary`, `pairDecode`, `codeBitsNat`), and `attribute [-simp]` on any `@[simp]`
        definition among them, which must still elaborate, **with controls**: for each sealed
        definition, a goal that closes by `rfl` with nothing sealed and fails under the seal;
      - an **inspection table** of every `rw`/`simp`/`simpa`/`dsimp`/`unfold`/`show`/`change`
        argument in your diff, each other-file name classified (a theorem, or a definition: a
        finding).
      - **Ship the raw outputs** of the seal and its controls, with their commands and exit
        statuses. **A seal not run, or a seal without controls that fail sealed and close
        unsealed, is a checklist failure.**
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`, `clearTM_run`,
      `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); none is needed.
    - Cite no private declaration of another file.
    - Keep your new privates under the `rc_` prefix (unused in the tree at the drafting base).

### Checkpoints (for a partial; ground rule 9)

Each may land alone; add no admission (a helper goes in only once proved).
1. `rc_widen`, `rc_choiceField`, the two length lemmas, `rc_widen_record`, `rc_workReads_snoc`,
   `rc_source_table`, `rc_replay_record`, `rc_replay_table`, and `rc_widen`'s primitive
   recursiveness.
2. The split: `rc_round`, `rc_table`, the skip and the rounds lemmas.
3. `rc_g` and `rc_g_serialize`.
4. `rc_g_primrec`.
5. The target, by the composition.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**). Run the before
screen on your base: it must equal the screen base.
- **The population** is 16 files
  (`campaign/fills/c1/inputs/c1-fill-replaycanon/screen-population.txt`):
  - your file;
  - the files the route cites: `NDCodes`, `MathlibBridge`, `Composition`, `Finite`,
    `CodeSimulator`, `ChoiceReplay`, `Build/StepBlock`, `CodeFormat`, `CodeParser`, `Encoding`,
    `Nondeterministic`;
  - the known hazards: `Codes2Tape` (the two-tape format's canonizer route), and the private
    `Primrec` proofs and compiler compositions of `CircuitComplexity/UHaltMachine`,
    `Diagonalization/NotTimeConstructible` and `ClassNP/PolyTime`.
- **The screen** is `scripts/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `campaign/fills/c1/logs/c1-fill-replaycanon-screen-base.txt`: **541
  declarations, 173 pairs, 86,076 characters** (MEASURED at the drafting base; about 13 minutes).
  No pair has a declaration of your file on either side.

```sh
P=campaign/fills/c1/inputs/c1-fill-replaycanon
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:** `MathlibBridge`'s `CodeFormat.primrec_scan` and the `codePrim*` proofs (cite
  them; your proofs compose them, they do not repeat them); `UHaltMachine`'s and
  `NotTimeConstructible`'s private `Primrec` proofs; the composition idiom of
  `ClassNP/PolyTime` (a few lines, shared shape: show the shared text if the screen pairs them).
  No private copy of the running-maximum monotonization, of the read-order lemma or of a record
  widening exists in the tree or on the open PR branches at drafting (searched). A pair at 90% or
  more is a copy.
- This item writes no input rewind, so `Simulation` and `Build/InputRewind` are not in the
  population.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; the cache **for the queue's Mathlib roots only** (addendum v2.5,
  fetched once at the session's start; your order list's modules import 41 roots directly);
  **never `lake build`**, and never the unfiltered `lake exe cache get`. Use
  `scripts/lean_check_tree.sh` for every check, one Lean process at a time.
- **Re-bootstrap** (addendum Part 3, item 3.2) from
  `campaign/fills/c1/orders/c1-fill-replaycanon.txt` (**119 modules**: the upstream closure of
  your owned file and of every module downstream of it, without the root `TCSlib`), logging each
  module's start and end time and maximum memory:

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < campaign/fills/c1/orders/c1-fill-replaycanon.txt )
  ```

  At the drafting base this took 879 s of Lean time; the peak was 2,993,964 KiB
  (`Build/CfgRecord`). **The base sorry-warning set has 31 entries in 15 modules**
  (`campaign/fills/c1/logs/c1-fill-replaycanon-base-sorries.txt`, one per declaration). Yours is
  `NDCodeSimulator`'s only one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `NDCodeSimulator`: zero errors, **no sorry warning** (for a partial, exactly the target's),
     and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (30 for a complete delivery).
  3. Re-run `C1RCImportProbe.lean.txt` (extended by your citations): 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for the target
  and every new private, and in a probe importing `Diagonalization/NTimeHierarchy` for
  `Turing.exists_ndInterpreterCore` and `Turing.exists_timed_universal_NDTM`: within
  `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`** for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`, 0 FAIL
  (base: 0 FAIL, 68 WARN over 83 files; `NDCodeSimulator`'s is its size). No new line over 100
  characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your target: MIG-1 stage S's sorried specs
(`Simulation`, `Composition`, `Encoding`, `ClassP/TimeConstructible`, `Build/Wrappers`,
`Build/Loop`, `Build/Primitives`); `Build/RecordTable`'s four rows; `Build/ZoneRebalance`'s two;
`CodeSimulator`'s `exists_uniformSimulator`; `UniversalK`'s two; `ClassNP/NDNormalForm`'s,
`Diagonalization/NTimeHierarchy`'s and `Diagonalization/NTimeDiagonalizer`'s. If a proof seems to
*need* one of these beyond a named citation, that is an escalation, not a license.

## REPORT.md checklist

- [ ] The session's shared preflight and cache numbers (quoted from its logs, the cache store's
      log included), **the shared logs copied into this zip**, this item's bootstrap with
      per-module time and memory, and the base blob check.
- [ ] The checkpoints reached; the base hash and the ancestor check; the checkpoint zips written.
- [ ] Every new declaration with its role; any restated recommended definition, with the reason;
      the status paragraph, if a partial.
- [ ] `rc_g`'s definition as delivered, its two contracts, and the composition's bound.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file (from an elaborated-constant walk), the
      probe re-run as "N checks of M names", **the seal test with its controls and both raw
      outputs** (not run, or no controls, is a failure), and the inspection table. Rule 11: a grep
      of your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints (the target, the core and the universal
      NDTM); the lint line. The diff touches only your owned regions.

## Known pitfalls at this pin (hard-won, from the pre-ship)

- **No `Primrec.list_take` in Mathlib at this pin.** `take n` is `Turing.codePrimPrefix` at
  `xs.length - n`; in the short case state `xs.length - n = 0` first (`omega` cannot see through
  the nested subtraction inside a rewrite).
- **The layouts' field equations are pointwise.** `NDTM.fixChoice_tr` and `NDTM.replayTM_tr` are
  stated fully applied: under the tables' binders use `simp only [NDTM.fixChoice_tr]`, not `rw`.
  `replayTM_tr`'s work-tape field is `fun i => Fin.lastCases (none, 1) a.workTapes i`.
- **`signBits 1`** is not `signBits .pos` syntactically: rewrite `← SignType.pos_eq_one` first.
- **`workReadsK`'s induction:** rewrite `workReadsK_succ` on the left side only, then the
  hypothesis; rewriting both sides at once leaves an unprovable shape. At `k = 0`,
  `Fin.cons a Fin.elim0 = Fin.snoc Fin.elim0 a` by `Fin.fin_one_eq_zero` and `Fin.snoc_last`.
- **`Fin.snoc_castSucc` needs its motive:** `Fin.snoc_castSucc (α := fun _ => Option Bool)`.
- **The choice read innermost:** the replay machine's choice tape is its last tape, and
  `workReadsK` puts tape `0` outermost, so the choice read is the innermost loop; the blank and
  `false` reads both select the `false` record (`Option.getD`).
- **The canonizer's output on a fallback code** is still a serialization (`c.decode` is total),
  so `rc_g` needs no fallback case of its own.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
