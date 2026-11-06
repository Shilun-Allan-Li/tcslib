# Review: B6's H fill brief draft (`b6-fill-hierarchy.DRAFT.md`, `Complexity.space_hierarchy` and its two corollaries)

Read-only review, 2026-11-06. Nothing tracked was edited, committed or pushed.

**Inputs read.** The draft (366 lines); the pre-ship `preship-d43a1374/` (the overlay and its `.out`,
the import, route, duplication and seal-control probes and their `.out`s, `order.txt`, `roots.txt`,
`base-sorries.txt`, `screen-base.txt`, `screen-population.txt`, the lint logs, `runs.txt`); the
route note `campaign/items/b6hosts/H/H-route-design.md`; and the source at `wt-hk` (`33b3b32a`, the
overlay on `d43a1374`). For every host the route cites I read its statement, and also the
statements of the neighbouring hosts the route needs but does not name.

**The previous brief review** (`campaign/fills/h/reviews/brief/REVIEW.md`) covers a different item:
C1-E's H, the **nondeterministic time hierarchy** `Complexity.ntime_hierarchy`
(`h-fill-hierarchy.DRAFT.md`, `campaign/items/c1/c1e/H-route-design.md`). It does not cover this
file, so none of its findings are carried over. Note that the two items share the name "H".

**Lean.** I ran one scratch elaboration through `leanelab.sh`:
`wt-hk/rvprobe/hreview/HRevProbe.lean` against `oleans-lcamp1`, which imports the base `Hierarchy`
plus the overlay's four modules. Its raw output is `HRevProbe.out` next to this file. The output
confirms three things:
- 22 names exist with the stated types. The brief needs them but does not name them.
- `seamCompTM_spaceUsed_le_add` rejects a machine over `RecSym P (Fin 3)` with "expected
  `MultiTapeTM 2 Bool P`".
- With `captureCfg` sealed, `exact?` finds no reading for its capture-tape contents, its head or
  its state (3 errors, by design).

**What checks out.**
- Every count the brief quotes from the pre-ship reproduces from the pre-ship files: 72 names and
  0 errors; 4 sorry warnings at 154/271/288/318; 5 sealed definitions and 9/9 controls; 6 `exact?`
  calls of which 2 close; 220 modules, 63 roots, 26 sorries in 10 modules; 1,345 declarations,
  740 pairs and 207,247 characters with none on `Hierarchy`; lint 0 FAIL and 80 WARN over 111
  files.
- The base blob is `287acce8`. `sph_` is unused in the tree and `sh_` is used.
- The targets' line numbers are right, as are the bodies at 271/285/315.
- The mathematics of `space_hierarchy` closes (§4).
- The `LOGSPACE ⊂ PSPACE` route is already proved under the seal by the route probe.

---

## Blocker

**B1. The radius phase's capture cannot be read under rule 10** (draft 145–148; also 171, 237).
- **What the brief says.** The brief binds "`g`'s witness, lifted to the record alphabet …, under
  the capture wrapper (`Turing.capture_run`, `capture_visitedByTapeHead`)".
- **Both lemmas are `Bool`-only.** Their signatures are `tm : MultiTapeTM k Bool S`,
  `host : MultiTapeTM (k + 1) Bool H` and `input : List Bool` (`Build/Wrappers.lean:183`,
  `Build/Catalog.lean:2103`). So a *lifted* witness cannot sit under them. The only usable order
  would be to capture over `Bool` and then lift the host.
- **Even that order fails.** The conclusions are equations on `Turing.captureCfg`
  (`Wrappers.lean:128`), and `captureCfg` has **no published field lemmas**: no `simps`, no
  `captureCfg_*`. Its in-tree consumers (`ClassNP/SAT.lean:719–727`) unfold it, together with
  `MultiTapeTM.initCfg`, `Cfg.init` and `FinTM.bufferTape`. Rule 10 forbids exactly that unfolding.
  The probe confirms there is no reading under the seal.
- **Consequence.** Rule 10's own escalation clause (line 258) then stops the radius phase. That
  stops checkpoint 2, and with it everything from checkpoint 4 on.
- **Fix.** Bind the generic R1′ capturing embedding instead. It exists for any `Symbol`, has
  published readings, and its docstring says it degenerates to `captureCfg`:
  - run `embedSilentRetTM ι cap (M_g.tm.liftSymbols (RecSym.digitEmb Q₀ (Fin 3)))` with
    `embedSilentRetTM_run`;
  - read it through `embedSilentCfg_cap`, `embedSilentCfg_unselected`,
    `embedSilentCfg_selected_tape`/`_pos` and the `simps` state/input/output equations
    (`Build/Embed.lean:983–1051`);
  - bound its space with `embedSilentTM_spaceUsedByTape_cap` and
    `embedSilentRetTM_visitedByTapeHead`;
  - transport the lift with `MultiTapeTM.liftSymbols_runFrom`/`_initCfg`.
  
  The captured word is then `bufferTape ((bits (g n)).map digitEmb)`, which is
  `ws.map RecSym.digit` by `RecSym.digitEmb_apply`. That is the form `exists_recordInitTM`
  expects. Also:
  - Reword rule 7's "capture" ban (line 238) so that it does not forbid this host.
  - Note that `Contract.liftSymbols` needs input-blind machines, so it does not apply to the
    witness.
  - Add `Build/Embed` and these names to the probe and to the screen population.

## Major

**M1. The binding composition lemmas do not apply to `D`, and no tape-embedding host is named**
(lines 151–152, 169).
- **The space lemmas are `Bool`-only.** `seamCompTM_spaceUsed_le_add`,
  `_spaceUsedByTape_le_add` and `_le_max` are stated over `MultiTapeTM k Bool _` and `Cfg.ofWords`
  (`Seam.lean:437–510`). `D` runs over `RecSym Q₀ (Fin 3)` on `x.map digitEmb`, and its
  configurations hold records, so they are not `ofWords`. The probe shows the type mismatch.
- **The phases have different tape counts, and the seam needs equal ones.** The phases are:
  - the fold, on `k` tapes;
  - the witness bank plus its capture tape;
  - `exists_recordInitTM`, on `K+2` tapes;
  - the runner, on `K+1` tapes. It **requires every tape but its record tape to be blank**
    (`WindowClock.lean:1512`), so it must avoid the radius tape and the witness's dirty tapes;
  - `exists_recordTestTM`, on 1 tape.
- **What exists.** The generic composition API is:
  - `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg`
    and `seamCompTM₂_run_ofCfg`, the last for the fold's verdict and the runner's three exits;
  - R1, `embedEmitTM_runFrom`/`_frame`/`embedEmitCfg_*`;
  - or the `Turing.Contract` layer (`Build/Contract/{Basic,Seam,Embed}`,
    `Contract.spaceUsedByTape_le`). Checkpoint 2's "as contracts" (line 282) presumably means this
    layer, but the brief never names it.
- **Fix.**
  - Bind these generic forms and drop the `Bool` corollaries.
  - Name the space route: a union of visited sets, or `Contract.spaceUsedByTape_le` from head
    envelopes.
  - Give a tape plan: record tape, radius tape, witness bank plus capture tape, and the runner's
    blank bank.
  
  E-D's brief needed the same addition ("the hosted runs' embedding and tape plan").

**M2. `D` has unstated phases and unnamed hosts** (lines 143–144, 168–174).
- **Input rewind.** `exists_recordInitTM` requires `d.inputPos = 1` (`RecordTable.lean:5811`), and
  the witness leaves the input head anywhere. `inputRewindTM_run` is `Bool`-only and needs
  `1 ≤ inputPos`, so on `D` it has to run lifted. Name it, and say what happens at position 0.
- **Radius-tape rewind.** The record initializer reads `ws` from the head (`p ∈ [-1, |ws|]`), but
  the capture leaves the head at `|ws|`. Use `rewindTM_run_ofCfg` or `skipBackTM_run_ofCfg`.
- **The verdict's tag read.** Step 5 names no host. Use `exists_recordTestTM` with
  `P q τ := decide (q = none ∧ τ = 1)`, hosted on the record tape (via R1). The tag it reads must
  be identified with `windowRun_summary_of_halts`'s tag. The runner's last clause gives *some*
  `N`, so this needs `windowRun_stop_unique`. On `exhausted`, tape 0 is unspecified, so answer
  `true` without the test. Add a one-step emitter leaf.
- **Small readings the route needs.** Name these and add them to the probe:
  - `MultiTapeTM.initCfg_eq`: the record is of `Cfg.init q₀ x`, while the window facts use
    `initCfg`;
  - `Cfg.inWindow_init`: the runner's `InWindow` premise for small `g n`;
  - `ComputesInTime.spaceUsed_le_of_halt`: the space at time `configBound`. `spaceUsed_mono`
    points the wrong way past the halt;
  - `recordAt_iff`;
  - `recordLength_eq`, `posWidth_eq` and `Complexity.LogProg.length_bits_le_log`: `posWidth n` is
    `O(logSpace n)`, which the floor absorbs;
  - `length_pairEncode` (`n ≥ N₀`) and `length_bits_le_self`.

**M3. The summary update is not named, and the window lemma fixes it** (lines 137–138, 173).
`windowRun_summary_of_halts` is stated only for `upd := Turing.summaryTag` and the initial tag `0`
(`WindowClock.lean:95`). An agent that writes its own "summary of `τ` followed by `b`" cannot use
it. Bind `T := Fin 3` and `upd := summaryTag`, with these lemmas:
- `hupd := summaryTag_none`;
- the verdict through `outSummaryCode_eq_one_iff`;
- the empty-output tag through `outSummaryCode_nil`.

**M4. The normalization re-proves a published lemma, by way of a dependent-index cast** (lines
155–157, 180).
- **The lemma exists.** `Turing.exists_codeTM_spaceUsed` (`Encoding.lean:741`, public at the base)
  states exactly the space clause that the brief says "`exists_codeTM` does not state":
  ```
  ∀ M : FinTM Bool, M.k = 1 → ∃ M' : CodeTM,
    (∀ x out t, M'.toFinTM.ComputesInTime x out t ↔ M.ComputesInTime x out t) ∧
    ∀ x t, M'.toFinTM.tm.spaceUsed (M'.toFinTM.tm.initCfg x) t = M.tm.spaceUsed (M.tm.initCfg x) t
  ```
- **The brief's route is costly and against the rules.** Its route through
  `relabelState_runFrom_init` needs the `M.k = 1` tape-count cast, which means destructuring the
  bundle and `subst`. That is the cross-index trap. It also breaks rule 5 ("never re-prove") and
  the duplication rules.
- **Fix.** Cite `exists_codeTM_spaceUsed`, and `MachineCode.decode_encode` for
  `decode (encode N) = N`.

**M5. `SPACE_linear_ne_NP` names no host for its machine obligations** (lines 192–198).
- **What is missing.** Line 21 says every host is proved. But nothing is named for these:
  - the padded language's validation, which must test that the pad's length is `|x|²`;
  - running `L`'s decider on the **first component** of the input (a virtual-input device);
  - the padding map's `PolyTimeComputable`.
- **Consequence.** Under rule 10's escalation clause, checkpoint 8 is likely to stop.
- **Fix.** Either name the hosts, or say plainly that checkpoint 8 may end in a named escalation.
  The extraction itself is sound:
  - `f ⁻¹' L' = L` follows from `pairEncode_injective`;
  - `A(n+1) ≤ n²+1` holds for `n ≥ A+1`;
  - the instance is `spaceConstructible_poly 2 (by norm_num)`.

## Minor

- **m1 (lines 165, 187 against 275).** The copied privates are `hr_*`, but rule 11 requires
  `sph_`. Say "rename to `sph_`".
- **m2 (line 189).** "`logSpace n ≤ n + 1` from `logSpace_le_succ`" has nothing to replace: none of
  the route probe's lemmas states or uses it. Delete the sentence or say where it applies.
- **m3 (lines 117, 121).**
  - The `space_hierarchy` docstring starts at base line 163 (162 is blank).
  - `LOGSPACE_ssubset_PSPACE`'s "spec, fill pending" is at base line **274**. Line 279 is
    "of phase P4.1".
  - Region (d) leaves other public-facing labels outside its scope, but its rule ("no phase, gate,
    round, finding") seems to cover them. Examples: the module docstring at base 23–28 and 60–65
    ("round-1 confirmed", "P4.1 gate"); "decision O6", "R8.5d", "§12.8a decision O4",
    "§12.7 and R8.0b" and "P0 convention". Say whether they are in scope.
- **m4 (lines 3–6, 64).** The base `d43a1374` is after #175, #177, #181, #191, #196, #202 and #207,
  not only #175/#177.
- **m5 (line 76).** `SavitchARM/Deepen` is not in the order list (it is new in #208); only
  `Savitch` is.
- **m6 (line 301).** The population is **27** files, as `screen-population.txt`'s header and its
  path count show. That file counts `TimeHierarchy/Diagonal` as "already cited", not as a hazard.
- **m7 (lines 215–222, 252).** The import probe contains neither `mem_NP_iff_exists_length_le` nor
  any `≤ₚ`/`PolyTimeReducible` name, though the section says "all in `HImportProbe`".
- **m8 (line 100, route note).** `exists_configWindowRunnerTM` is at `WindowClock.lean:1503`, and
  `exists_recordInitTM` is at `:5805`.
- **m9 (line 105).** The route probe has four lemmas, with three axiom prints
  (`hr_sq_le_two_pow` is not printed). Line 324 will require a print for it.
- **m10 (line 182).** "`c`" in `A := C_α (c · c₀ + c + 1)` is the normal form's constant, not the
  packaging `c` of line 154. Name it.
- **m11 (lines 262–263).** "the route probe's five, `SpaceConstructible`, … `PSPACE`" lists the same
  five twice.

## Notes

- **n1 (lines 322–323).** Only `TCSlib/Complexity/SpaceComplexity.lean` imports `Hierarchy`. "The
  order list's tail from your module on" is 52 modules per edit, most of them independent of it.
- **n2.** Recommend defining `L_D` through `D`'s output, not through `windowRun`. The runner pins
  its exit only for non-exhausted `N ≤ configBound + 1`.
- **n3 (§4, the mathematics).** The contradiction closes:
  1. Take `s ≤ c(c₀ f n + 1)`.
  2. Then `U₀` runs within `C_α(s+1) ≤ A f n ≤ g n` (using `1 ≤ f n`).
  3. `of_spaceUsed_le` puts the halt at `configBound U₀ n (g n)`, and `spaceUsed_le_of_halt` gives
     the space at that time.
  4. `windowRun_summary_of_halts` at `N = configBound + 1` then forces `out = halted` with tag
     `[x ∈ L_D]`.
  
  On the space side: `D`'s space is `O(g n)` uniformly in `α`, because the runner's constants
  depend only on `U₀` and `Fin 3`; and `L_D ∈ SPACE g` follows from
  `decidesInSpace_of_alphabetReduction` and `mono_const`. The inclusion and `LOGSPACE ⊂ PSPACE`
  are right as stated.
