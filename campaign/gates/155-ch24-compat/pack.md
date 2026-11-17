# Gate 155 · Ch2-4 compatibility: adopt pass-shelat-ch2-4's readers ahead of its merge (PR #354)

**Not yet clear to merge** · PR #354 is a draft. Seyoon dispatches and merges.

- Lean head: `718dddc66d5d4dad7ea25f299a01931be6c42658` (branch `closeout/ch24-compat`).
- Base: campaign Lean `0ac28d18` (the #350 merge). Records: see the dispatch prompt.
- This is the first audit.

## Scope

This campaign merges into `main` before `cryptography/pass-shelat-ch2-4` (Seyoon, 2026-11-17).
Both campaigns published rule-10 readers for the same shared definitions, so ch2-4's later merge
would hit 11 Lean conflicts. `campaign/closeout/CH2-4-OVERLAP.md` has the analysis. Seyoon chose to
put ch2-4's versions of those lemmas on this branch through a gated PR. The text copied from ch2-4
comes from its tip `c3689193`.

A trial merge (`git merge-tree`: main + ch2-4, then this head) now gives **4 Lean conflicts
instead of 11**. They are Build/Primitives (take ours), ClassNP/SAT (take ours), ClassP/DTIME and
the `TuringMachine` umbrella. No compile of the merged tree was run; Seyoon deferred it to merge
time.

**New public declarations (Seyoon's choice of this route, 2026-11-17):**

1. **`BoolCircuit.encodeNat_def`** (CircuitComplexity/UnaryCode): `encodeNat k` is `k` `true`s
   then `false` (`rfl`). It is ch2-4's text and repeats our `encodeNat_eq`.
2. **`Turing.MultiTapeTM.indicator_def`** (TuringMachine/Deterministic): the indicator as the
   classical `if` (`rfl`), ch2-4's text, beside our `indicator_of_mem` and `indicator_of_not_mem`.
3. **`Turing.pairEncode_ne_nil`** (TuringMachine/Encoding): no pair encoding is empty, by its
   length; ch2-4's text. Its namesake `Complexity.pairEncode_ne_nil` (Logspace/InputAccess) is in
   another namespace; ch2-4 has both too.
4. **`Turing.safeRun_iff`** (Build/EmitIterEmbed): the definition of `SafeRun` as an equation
   (`Iff.rfl`), ch2-4's text.
5. **`Turing.FinTM.exists_pairMapSnd_computesInTime`** (Build/Primitives): ch2-4's exact
   statement. For each `G` there is one machine that sends `pairEncode a b` to `pairEncode a y`
   within `40·(time + |pairEncode a b| + 1)` steps whenever `G` sends `b` to `y` within `time`.
   ch2-4 proved it on `pairMapTM`, which this campaign removed (MIG-1 F-B). Here it is proved on
   `pairMapSndTM` through the new private `pairMapSndTM_computesInTime_of` (the one-pair bound
   `5·(|x| + 1) + time`), which `pairMapSndTM_computes` now also cites.
6. **`Turing.emitCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`**
   (Build/Wrappers): ch2-4's five hand-written field equations, `rfl`. They replace
   `attribute [simps (config := { isSimp := false })] emitCfg`, which generated the same names.
   `state`, `inputPos` and `output` have the same statements as the generated ones (checked with
   `#check`). `workTapes` and `workTapePos` are now equalities of functions; the generated ones
   were pointwise.

**Changed existing declarations:**

- `Complexity.polyTimeComputable_iff` and `Complexity.polyTimeReducible_iff` (`header_changed`):
  both now use ch2-4's exact text. The docstrings change, and so does the layout of the statement:
  `M.ComputesFunInTime f fun n => …` instead of `(fun n => …)`, and the line breaks. The
  statements elaborate to the same terms.
- `Turing.SafeRun.zero`: proved by `safeRun_iff.mpr ⟨MultiTapeTM.runFrom_zero, …⟩` instead of the
  private `safeRun_iff_segment`. Run 1 used `rfl` here, which read `runFrom` directly, and its seal
  failed; this head fixes it.
- `Turing.FinTM.pairMapSndTM_computes`: the statement is unchanged; the pair case cites the
  one-pair bound.
- **Moved, unchanged:** `encodeNat_eq` (to the end of its namespace), `indicator_of_mem` and
  `indicator_of_not_mem` (past `DecidableInTimeAndSpace`), `pairEncode_drop` (past
  `pairDecode_eq_none`), and the private `safeRun_iff_segment` (past `SafeRun.zero`). Each now sits
  apart from ch2-4's insertion point, so git merges both sides.
- **Module docs:**
  - EmitIterEmbed's `Main definitions` line is ch2-4's.
  - Our note on `embedCfg`'s field equations moves to `Main results`.

`SOURCE.json`: 8 owners, 15 changed or added declarations, 10 added (the names above), none
removed, `header_changed` the two readers, no definition body changed. Net **+80 Lean lines**
(+149/−69). By file: Primitives +27, Wrappers +23, EmitIterEmbed +8, Deterministic +8, Encoding
+6, UnaryCode +5, PolyTime +2, Reductions +1.

## Brief for the auditor

1. **Fidelity to ch2-4.** Each copied block should be byte-identical to `c3689193`'s text at that
   position. Apart from the moves, nothing else in the 8 files should change.
2. **The port.** Check that `exists_pairMapSnd_computesInTime` has ch2-4's exact statement and
   that the one-pair bound implies it. Check that `pairMapSndTM_computes` keeps its statement.
3. **`emitCfg`.** Check that replacing the generated equations with ch2-4's hand-written ones
   changes nothing else: the names are the same; two statements become function equalities; the
   replay passes every user.
4. **Rule 10.** The changed proofs, with seals, controls and both sweeps (counts below).
5. **The forecast.** `CH2-4-OVERLAP.md` and the claimed 11 → 4 reduction are records, not Lean;
   check them only for accuracy against the trial merge described there.
6. **Copy screen** (population: the 8 changed files): `evidence/PAIR-DISPOSITIONS.json`.

## Evidence

- **`evidence/REPLAY.json`:** the merged-tree replay of the 8 owners' downstream closure on
  `oleans-c0ac28` (the #350 merge's snapshot).
  - 411 modules replayed: 411 passed, 0 failed, 28 inherited admissions (pre-existing).
  - 874 objects in and 874 out.
  - Pool 3 of 4 cores under the 2026-11-17 parallelism rule; peak memory 6.1 GB of 16.9 GB; no
    back-off.
- **Seals:** 14 changed or added proofs in 7 owners pass with every other-file definition they
  reach made irreducible. UnaryCode's proofs reach no other-file definition.
- **Controls:** one part, **20 sealed definitions and 40 paired identities**, each native-PASS and
  sealed-FAIL.
- **Proof-syntax sweep:** 15 roots, 0 read candidates.
- **Lean-backed sweep** (`evidence/DEFSWEEP-SUMMARY.json`): 12 identifiers (Primitives 11,
  Encoding 1) and **no flag**; the other owners' changed proofs name no constant.
- **Citation homes** (`evidence/CITATION-HOMES.json`): Configuration (`Turing.Cfg`) and Finite
  (`Turing.FinTM.k`), both bundled. The scope pass has namespace errors in one block each of
  Deterministic and EmitIterEmbed (`unknown namespace`), the same kind gate 154 recorded.
- **Lint:** no new finding. One campaign warning is gone: EmitIterEmbed's `SafeRun` now has its
  reader beside it.
- **Copy screen:** 213 → 214 directed pairs, 1 new and 0 gone. The new pair is
  `pairMapSndTM_spaceUsed` → `pairMapSndTM_computesInTime_of` at 50%. It is the payload-launch
  prelude (`fwdMap_launch`, the `VirtualTag` fact, `fwdMapVirtual_run`) that the space proof
  already shared with the time proof. The prelude moved unchanged into the shorter one-pair
  bound, so the same text now crosses half of it.
- **Run 1** (head `ab0ed440`) passed its replay (411/411), but the seal failed on `SafeRun.zero`
  (`rfl` for `runFrom c 0 = c`). `718dddc6` cites `runFrom_zero`; this pack's evidence is from
  the rerun on `718dddc6`.
- `evidence/DATA-CARRIER.json` and its recovery map (1,405 logical files): decode each
  gzip+base64 blob, then check its SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate155-ch24-compat-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
