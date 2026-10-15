# Ch3–4 fill campaign — B3a: space-constructibility of `log` and of `n + 1` (`SpaceComplexity/Constructible.lean`, 2 targets)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor 3ba353460e2d7a877cada66de214dbd3152fe8a7 HEAD`
  succeeds. That commit contains:
  - R8.5c (`Turing.exists_inputLengthTM`, `Build/InputLength.lean`), proved;
  - the §13 Z1 virtual-input host (`Build/VirtualInput.lean`), proved;
  - the §12.8 Catalog Part 3, Seam and Scan rows, proved (their A–C fill gate is open; cite only);
  - the §12 Catalog space rows (`computesFunInTime_*_spaceUsed`), proved;
  - this round's order list `briefs/orders/ch34-b3a.txt`, base sorry set `audits/logs/ch34-b3a-base-sorries.txt`, screen base
    `audits/logs/ch34-b3a-screen-base.txt` and pre-ship log.

  If the check fails, **stop**.
- Create your working branch off the campaign branch (`fill/ch34-b3a`). Record the base
  hash in `REPORT.md`. Never rebase.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-ch34-b3a.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against your base, a git
  bundle, the final sweep log, the axiom log, and `SHA256SUMS`.

## Parallel batches this round (disjoint files; never edit another batch's file)

| Batch | Brief | Owns |
|---|---|---|
| S1b, the configuration-graph simulation | `briefs/ch34-s1b.md` | `SpaceComplexity/ConfigGraph.lean` |
| **B3a, constructibility** | `briefs/ch34-b3a.md` | `SpaceComplexity/Constructible.lean` |
| B4, TQBF membership | issues later, after a pre-issue promotion | `ClassPSPACE/TQBF.lean` (target `TQBF_mem_PSPACE` only) |
| B5b, the `EXPCOM` summit | `briefs/ch34-b5b.md` | `Diagonalization/EXPCOM.lean`, by declaration: the summit, its new privates and imports (the module header is not theirs) |

Also in flight: the §12.10 W2-S continuation (`briefs/w2-fill-oraclesim-cont.md`,
`Build/OracleSim.lean`); the §12.8b record-table continuation
(`briefs/w1-fill-recordtable-cont.md`, `Build/RecordTable.lean`); the B5a continuation
(`briefs/b5a-fill-cont.md`, `CodeSimulator.lean`, plus status text in `Codes2Tape.lean` and
`EXPCOM.lean`); and maintainer PRs touching `TuringMachine.lean` (the facade), `Build/Embed.lean`
(one additive export) and an audit program. A further maintainer PR, B4's pre-issue promotion, will add public CNF-grammar facts to `Formulas/CNFEncoding.lean` and one head-interval lemma to a core file; it is additive. **Not yours** (the §12.8 A–C files, whose fill
gate has closed): `Build/Catalog.lean`, `Build/Seam.lean`, `Build/Scan.lean`, `Build/CfgRecord.lean`,
`Build/InputCall.lean`. Cite them; never edit them. A parallel batch's work is invisible to your
base and your screen.

**S1b cites your `spaceConstructible_logSpace`** (for `NL_subset_P`); it reports itself proved
modulo it until you land. Nothing you do may change that statement.

## What this is

**Batch B3a**: the constructibility half of plan §4e's cluster B3. Savitch and
`spaceConstructible_poly` are a later batch. Fill the two audited-true P4.1 statements:
- `Complexity.spaceConstructible_logSpace`: `logSpace` is space-constructible;
- `Complexity.spaceConstructible_linear`: `n ↦ n + 1` is space-constructible.

Both are **assemblies of proved public rows**. **The proved-modulo set is empty**: a complete
delivery has no `sorryAx`.

| Row | Home | Role |
|---|---|---|
| `Turing.exists_inputLengthTM` (R8.5c) | `Build/InputLength.lean` | `Nat.bits |x|` on a work tape, framed, with logarithmic head range |
| `Turing.writeConstTM_run_ofCfg` (R8.4) | `Build/Scan.lean` | overwrites a word at the head, "whatever it held before" |
| `Turing.vhostEmitTM` (Z1) | `Build/VirtualInput.lean` | runs a machine on a **work-tape word** as its input and **forwards its emissions to the physical output**, with the coefficient-one space ledger `vhostEmitTM_spaceUsed_le` |
| `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed` | `Build/Catalog.lean` | the binary length counter as a `FinTM`, time `c(n+1)`, space `c(Nat.size n + 1)` |
| `Turing.FinTM.computesFunInTime_prepend_spaceUsed` | `Build/Catalog.lean` | `x ↦ w ++ x` in linear time |
| `Turing.FinTM.bufferedCompTM`, `bufferedCompTM_computesInTime` | `Simulation.lean`, `Composition.lean` | timed sequential composition |
| `Turing.MultiTapeTM.spaceUsed_le_mul_succ` | `Finite.lean` | `spaceUsed ≤ k·(t + 1)` |
| `embedEmitTM` (R1), `seamCompTM` / `phaseHostTM` (R2) | `Build/Embed.lean`, `Build/Seam.lean` | tape selection and sequencing |

**The output question, resolved.** Putting a work-tape word, or a function of it, onto the output
tape under a space bound is **Z1 itself**. `Turing.vhostCfg` lays the virtual input out as
`Turing.FinTM.bufferTape y` on the buffer tape, read from cell `0` (head at the source's input
position minus one). Its output is `pre ++` the source's output, at every time
(`vhostEmitTM_runFrom`), and a halting emission is forwarded before the host halts
(`vhostEmitTM_emitting_halt`). R8.5c, started at head `0` on a blank tape, **exits with exactly that
buffer layout**. A time-only alternative also exists: `Turing.FinTM.exists_emitCallTM`
(`Build/Loop.lean`) forwards `f arg` for a tape-resident `arg`. It is not needed; if you use it,
its space comes only from its time through `spaceUsed_le_mul_succ`.

**Read first:**
- `SpaceComplexity/Constructible.lean` in full;
- `audits/ch4-p41-findings.md` (findings 1–3) and `audits/ch4-p41-resolutions.md` (minors 1–3):
  your **binding audit**;
- `Build/InputLength.lean`'s R8.5c contract;
- `Build/VirtualInput.lean`'s module docstring and contracts;
- `audits/wave1-statements-resolutions.md` notes 41 and 44;
- the B2b precedent `briefs/ch34-b2b.md`, route 1 (R1/Z1 phases sequenced by `phaseHostTM`);
- `policy.md`; `workflow.md` §4.

**Pre-ship check (maintainer, executed at this brief's ancestor):** re-run at the issue tree (`audits/logs/ch34-wave5-preship.log`): 0 errors, 0 warnings
(`audits/evidence/ch34-wave5/B3aPreShip.lean.txt`: every cited name and both targets `#check`ed, under the sanctioned
imports).

## Owned file and targets (modify this file and nothing else)

Lines are at the issue commit.

| # | File:line | Target | Route | Uses |
|---|---|---|---|---|
| 1 | `SpaceComplexity/Constructible.lean:76` | `Complexity.spaceConstructible_logSpace` | R8.5c, one overwrite, Z1-hosted length counter | — |
| 2 | `SpaceComplexity/Constructible.lean:92` | `Complexity.spaceConstructible_linear` | the length counter on `true :: x` (counter initialized at `1`); space from linear time | — |

- **Owned:** `SpaceComplexity/Constructible.lean`, for the two targets' bodies, new `private`
  declarations and the sanctioned imports.
- **Not yours:** every `Build/*` file, `Simulation`, `Composition`, `Finite`, `TimeConstructible`,
  `ConfigGraph` (S1b), `Savitch` (`spaceConstructible_poly` is a later batch), and the facades.
- `Complexity.SpaceConstructible` (`:56`) is frozen.
- Fill 2 (short), then 1.

### Proof routes (binding: the docstrings' sketches with P4.1 minors 1–2; the realizations below are sanctioned and need a flagged Fill appendix)

**Target 2, `n + 1`.** The docstring's route is "the input-scan counter **initialized at `1`**"
(minor 2: an uncorrected length counter emits `bits n`). It is realized as the binary length
counter on the virtual input `true :: x`, which needs no new machine:
- **Dominance.** `logSpace n ≤ n + 1`: `1 ≤ 1` at `n = 0`; otherwise `Nat.log 2 n ≤ n`.
- **Machine.**
  - `obtain` `M_p` from `computesFunInTime_prepend_spaceUsed [true]` and `M_ℓ` from
    `computesFunInTime_lengthBits_spaceUsed`.
  - `bufferedCompTM_computesInTime` gives
    `(bufferedCompTM M_p M_ℓ).ComputesInTime x (Nat.bits (|x| + 1)) (t₁ + (|x| + 1) + 2 + t₂)`,
    with `t₁ ≤ c_p(|x| + 1)` and `t₂ ≤ c_ℓ(|x| + 2)`.
- **Space.** `spaceUsed ≤ k·(t + 1)` (`spaceUsed_le_mul_succ`) at that `t`, so it is at most
  `A·(n + 2) ≤ 2A·(n + 1)`. This is exactly the docstring's ledger, and it includes the boundary
  and width cells (minor 2).
- **Fill appendix:** the counter initialized at `1` is the length counter run on `true :: x`, and
  the space ledger is the linear time bound.
- **Alternative (also sanctioned):** R8.5c, then one `incrementTM` with the one-cell overflow
  extension (wave-1 note 26's idiom), then emission through Z1 hosting
  `computesFunInTime_id_spaceUsed`'s witness. Prefer the main route: it adds no glue machine.

**Target 1, `logSpace`.**
- **Dominance:** `le_refl`.
- **The function.** `Nat.bits 0 = []`, so the bits-length identity holds **only for `n > 0`**
  (minor 1).
- **Main realization: a uniform overwrite instead of a separate branch.** Three phases on one host
  (`phaseHostTM`, the B2b precedent, or nested `seamCompTM`). Each phase is R1-embedded
  (`embedEmitTM`) onto fixed tapes. The buffer tape is shared by phases 1–3.
  1. **Count.** `exists_inputLengthTM`'s module, entered at its `entry` with input position `1`,
     its tape `0` (the buffer) blank, and its head at `0`. It exits with
     `FinTM.bufferTape (Nat.bits n)` on the buffer, the head back at `0`, and every other tape,
     the input position and the output unchanged. Up to its exit every head stays within
     `C(|bits n| + 1)` of its entry.
  2. **Overwrite** cell `0` with `true`: `writeConstTM k buf [true]`, `writeConstTM_run_ofCfg`, in
     `4` steps, head range `[0, 1]`. The buffer now holds a word `y` with `|y| = logSpace n` **for
     every `n`**:
     - `n = 0`: `y = [true]`, and `logSpace 0 = 1`;
     - `n > 0`: `y` is `bits n` with its first digit set, and
       `|bits n| = Nat.log 2 n + 1`.
  3. **Emit.** `vhostEmitTM M_ℓ.tm` from `vhostCfg (M_ℓ.tm.initCfg y) true 1 []`, embedded so that
     its buffer is phase 1's tape `0` and its bank is fresh blank tapes. The seam's handover
     configuration is that `vhostCfg` exactly: buffer head `0 = inputPos − 1`, bank blank at `0`,
     output `[]`. `vhostEmitTM_runFrom` runs `M_ℓ` to its halt with output `Nat.bits |y|`, and the
     host halts with it.
- **Fill appendix:** "(ii) the empty input is special-cased" is realized by the overwrite, which
  makes the counter word nonempty, so `n = 0` needs no branch.
- **Alternative (also sanctioned, the literal special case):**
  `computesFunInTime_cond_spaceUsed` with `p x := decide (x = [])`, `f₁ := fun _ => [true]`
  (`computesFunInTime_const_spaceUsed`) and `f₂` the count-then-emit composite without the
  overwrite. It needs a one-step zero-work-tape emptiness decider as a new `private` machine:
  **no public emptiness decider exists**.
- **Space ledger** (minor 1: bound by `A·(logSpace n + 1)` before absorbing). Per tape, through
  `seamCompTM_visitedByTapeHead_ofCfg` (or the phase-host analogue) and the R1 visited lemmas:
  - phase 1: an interval of `2C(|bits n| + 1) + 1` cells around each entry;
  - phase 2: `{0, 1}`;
  - phase 3: the buffer interval `[-1, |y|]` (`vhostCfg_buffer_head_mem`), and the bank's
    `M_ℓ.spaceUsed (initCfg y) ≤ c(Nat.size |y| + 1)`.

  Everything is at most `A·(logSpace n + 1) ≤ 2A·logSpace n`, since `logSpace n ≥ 1` and
  `|bits n| ≤ logSpace n` (`Complexity.LogProg.length_bits_le_log`).
- **Time** is irrelevant to the statement beyond halting: take the halting time.
- **Arithmetic** (private, in-file): `(Nat.bits n).length = Nat.log 2 n + 1` for `n ≠ 0`. Prove it
  from `Nat.size_eq_bits_len`, `Nat.lt_size` and `Nat.pow_log_le_self` for the lower bound, and
  `length_bits_le_log` for the upper bound.

## Gate guidance (binding; `audits/ch4-p41-resolutions.md`)

- **Minor 1:** the bits-length identity is stated for `n > 0` only. The empty input outputs `[true]`.
  The workspace ledger is bounded by `A·(logSpace n + 1)`, boundary cells included, before
  absorbing.
- **Minor 2:** the `n + 1` counter must start at `1`; an uncorrected counter emits the wrong word.
  The final counter width and boundary cells are in the ledger.
- **Minor 3:** constant slack implements [AB09]'s own convention. No appendix may claim an
  exact-space refutation.
- **Wave-1 note 41:** R8.5c is "a construction ingredient, not by itself a proof". Keep its
  input-position-`1` convention and its low import boundary. The final configuration must be a
  genuine halt with the full output.
- **Wave-1 note 44:** R8.5c's counter is paired with Catalog's private `f2_counterTM` for 12.2c.
  Copy no counter proof; cite the two rows.
- **Intercept every verdict** (§12.8 statement gate, round-2 note 7). R8.5c's head clause holds up
  to its exit only, so redirect exactly at its exit time.

## Cited infrastructure (public and proved at the issue commit)

- **Targets' surface:** `Complexity.SpaceConstructible`, `Complexity.logSpace`, `Complexity.logSpace_mono`,
  `Turing.FinTM.ComputesInSpace`, `Turing.FinTM.ComputesInTime`, `Turing.FinTM.ComputesInTime.mono`,
  `Turing.FinTM.ComputesFunInTime`, `Turing.MultiTapeTM.spaceUsed`, `Turing.MultiTapeTM.visitedByTapeHead`,
  `Turing.MultiTapeTM.spaceUsed_le_mul_succ`, `Turing.MultiTapeTM.exists_first_halt`.
- **R8.5c:** `Turing.exists_inputLengthTM`.
- **R8.4:** `Turing.writeConstTM`, `Turing.writeConstTM_run_ofCfg`.
- **Z1:** `Turing.vhostEmitTM`, `Turing.vhostCfg`, `Turing.vhostBuffer`, `Turing.vhostBank`,
  `Turing.vhostEmitTM_runFrom`, `Turing.vhostEmitTM_visitedByTapeHead_bank`,
  `Turing.vhostEmitTM_visitedByTapeHead_buffer`, `Turing.vhostEmitTM_spaceUsed_le`,
  `Turing.vhostCfg_buffer_head_mem`, `Turing.vhostEmitTM_emitting_halt`, `Turing.FinTM.VirtualTag`,
  `Turing.FinTM.bufferTape`.
- **R1/R2:** `Turing.embedEmitTM`, `Turing.embedEmitCfg`, `Turing.embedEmitTM_runFrom`,
  `Turing.embedEmitTM_frame`, `Turing.embedEmitTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead_frame`, `Turing.seamCompTM`, `Turing.seamCompTM_run_ofCfg`,
  `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.seamCompTM_visitedByTapeHead_ofCfg`,
  `Turing.phaseHostTM`, `Turing.phaseHostTM_run`.
- **Catalog space rows (`Turing.FinTM`):** `computesFunInTime_lengthBits_spaceUsed`,
  `computesFunInTime_prepend_spaceUsed`, `computesFunInTime_const_spaceUsed`,
  `computesFunInTime_id_spaceUsed`, `computesFunInTime_cond_spaceUsed` (alternative only).
- **Composition:** `Turing.FinTM.bufferedCompTM`, `Turing.FinTM.bufferedCompTM_computesInTime`.
- **Counters (alternatives only):** `Turing.incrementTM`, `Turing.incrementTM_run_succ_ofCfg`,
  `Turing.incrementTM_run_overflow_ofCfg`; `Turing.FinTM.exists_emitCallTM` (time-only).
- **Arithmetic:** `Complexity.LogProg.length_bits_le_log` (`SpaceComplexity/Machines/Bin.lean`).
- **Do not cite** anything in `ConfigGraph`, `Savitch`, `Hierarchy`, `ClassPSPACE` or the record
  layer (`CfgRecord`, `RecordTable`): none is needed, and the record layer is far above this
  file's import boundary.

## Ground rules (binding)

1. **File ownership.** Only `SpaceComplexity/Constructible.lean`. Change only the two targets'
   bodies, and add new `private` helpers there. List every new declaration with its role. A lemma
   that genuinely belongs in a shared file is written privately, flagged in `REPORT.md` as a
   promotion candidate, and promoted by the maintainer at integration (`workflow.md` §4, rule 1).
2. **Statement freeze** over every target and every landed declaration: no renames,
   re-signatures, restatements or attribution edits. Docstrings stay. A flagged
   **"Fill appendix"** is **required** on both targets (the sanctioned realizations refine the
   sketches).
3. **Status text.** Only your file's status text may change: the module's
   "Main results (sorried; phase-P4.1 statements)" heading, each to "proved". Flag it. No new
   public declaration.
4. **Escalation** on anything unprovable as stated, including a cited row that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** **Sanctioned additions, exactly:**
   `import TCSlib.Complexity.TuringMachine.Build.InputLength` (it brings `CounterLoop`, `Catalog`,
   `Scan`, `Embed`, `Loop`, `Composition` and `SymbolLift`),
   `import TCSlib.Complexity.TuringMachine.Build.VirtualInput` and
   `import TCSlib.Complexity.TuringMachine.Build.Seam`. Optionally also
   `import TCSlib.Complexity.SpaceComplexity.Machines.Bin` (Mathlib-only), if you cite
   `length_bits_le_log`.
   - All are acyclic at the issue tree: no module in their closures imports any `SpaceComplexity`
     module (maintainer-checked by reading the import lines). Flag each.
   - They enlarge the closure of every module downstream of `Constructible`: `ConfigGraph`,
     `Savitch`, `TQBF`, `Hierarchy`, `ImmermanSzelepcsenyi`, `Path` and the facades. Final check 2
     covers it.
   - No other TCSlib import may be added. A Mathlib import is allowed only if a needed lemma
     requires it; flag it.
7. **One proof per shared argument.** Cite the landed rows the route names; never re-walk a
   landed contract inside a target, and never write a second counter, host, loop or trace for
   something already public.
8. **Size.** No cap; file size alone is not a driver (user, 2026-10-11). Report the file's final
   line count and its public and private declaration counts.
9. **Continuation budget.** If your budget runs out, deliver a partial zip whose `REPORT.md`
   states which targets are proved, which `private` helpers remain `sorry` (each with a literal
   "Proof sketch"), and which proved targets are proved modulo them. A partial is expected and
   fine; an unreported gap is not.

## Duplication governance (binding)

Run the text-level screen **before and after** (`audits/TEMPLATE.md` failure mode 5; `policy.md`,
**Duplication**). The base, at this brief's issue tree, is `audits/logs/ch34-b3a-screen-base.txt`: **1,228 declarations, 1,520 pairs, 597,328 characters**.

Population (`audits/evidence/ch34-wave5/ch34-b3a-screen-population.txt`): the owned file, every
file a route reuses, and every duplication hazard.

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/SpaceComplexity/Constructible.lean \
  TCSlib/Complexity/ClassP/TimeConstructible.lean \
  TCSlib/Complexity/SpaceComplexity/Basic.lean \
  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean \
  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean \
  TCSlib/Complexity/SpaceComplexity/Examples.lean \
  TCSlib/Complexity/SpaceComplexity/Inclusions.lean \
  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean \
  TCSlib/Complexity/SpaceComplexity/Savitch.lean \
  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean \
  TCSlib/Complexity/ClassNP/TMSAT.lean \
  TCSlib/Complexity/TuringMachine/Finite.lean \
  TCSlib/Complexity/TuringMachine/Encoding.lean \
  TCSlib/Complexity/TuringMachine/Simulation.lean \
  TCSlib/Complexity/TuringMachine/Composition.lean \
  TCSlib/Complexity/TuringMachine/Build/InputLength.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Primitives.lean \
  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean \
  TCSlib/Complexity/TuringMachine/Build/Scan.lean \
  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean \
  TCSlib/Complexity/TuringMachine/Build/Loop.lean
```

- **No new cross-file pair** with an owned-file declaration on one side, except a pair this
  brief pre-discloses (measure it and report it). **Pre-disclosed:** none.
- **Known hazards:**
  - `TimeConstructible`'s private `counterTM`/`counterInc`, Catalog's private `f2_counterTM` and
    R8.5c's counting phase: never build a counter; cite R8.5c and the Catalog rows.
  - `ZeroSpace`'s and `Examples`' tiny zero-tape machines (`constTrueTM`, `evenScanTM`), if you take
    the alternative's emptiness decider: it must not reproduce their tables.
  - B2b's private glue machines in `Inclusions` (anchor, rewind, verdict readers) and the Z1
    seams there: reuse the public rows, never their privates.
  - `Composition`'s and `Simulation`'s `bufferedComp*` internals: cite
    `bufferedCompTM_computesInTime`, do not re-walk them.
  - `logSpace`/`Nat.bits` arithmetic: `Complexity.LogProg.length_bits_le_log`,
    `length_bits_le_self` (`Encoding`) and `Complexity.logSpace_mono` exist; do not re-prove them.
- **Later consumer:** `spaceConstructible_poly` (Savitch.lean, a later batch) will need the same
  "space from linear time" packaging as target 2. If you factor it as a private helper, flag it as
  a promotion candidate.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy:
  factor it.
- Parallel batches are invisible to your screen. A cross-file pair between your private helpers
  and another batch's, found at integration, is the maintainer's to factor.
- Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pre-disclosed pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/ch34-b3a.txt` (**113 modules**: the upstream closure of
  your owned file, including the sanctioned imports, and every module downstream of it, at the
  issue tree):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/ch34-b3a.txt )
  ```

  **Base sorry-warning set, 20** (`audits/logs/ch34-b3a-base-sorries.txt`, one entry per declaration). Yours:
  `SpaceComplexity/Constructible` 2. Record the base list by name first. If anything else has landed
  by your base, report the difference.
- **Final checks:**
  1. Your owned module: zero errors, zero sorry warnings (or exactly your partial's).
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours. The new imports reach every downstream module, so a name clash there is an
     escalation, not a rename.
  3. Re-run the pre-ship probe `audits/evidence/ch34-wave5/B3aPreShip.lean.txt` (copied to a scratch `.lean` path): 0 errors.
- **Axiom prints** for both targets: within `[propext, Classical.choice, Quot.sound]`. **No
  `sorryAx`** (the modulo set is empty).
- **Lint:** `python3 scripts/campaign_style_lint.py TCSlib/Complexity/SpaceComplexity`, 0 FAIL.

## Out-of-scope sorries you will see (leave every one untouched)

- `SpaceComplexity/ConfigGraph`: NSPACE_subset_exp_dtime, NL_subset_P, polyTimeReducible_of_mem_NL
- `ClassPSPACE/TQBF`: TQBF_mem_PSPACE, TQBF_PSPACEHard, TQBF_PSPACEComplete
- `SpaceComplexity/Savitch`: spaceConstructible_poly, savitch, PSPACE_eq_NPSPACE
- `SpaceComplexity/Hierarchy`: space_universal, space_hierarchy, LOGSPACE_ssubset_PSPACE, SPACE_linear_ne_NP
- `SpaceComplexity/Logspace/Path`: PATH_mem_NL, PATH_NLComplete
- `SpaceComplexity/Logspace/ImmermanSzelepcsenyi`: compl_PATH_mem_NL, NL_eq_coNL, NSPACE_compl_eq

(The base set minus the two targets. Note in particular: `ConfigGraph`'s three targets, which are
S1b's and cite yours; `Savitch`'s three, including `spaceConstructible_poly`.)

If a proof seems to *need* one of these, that is an escalation, not a license.

## REPORT.md checklist

- [ ] 2/2, or the partial frontier (rule 9); the base hash and the ancestor check.
- [ ] Every new declaration with its role; every flagged appendix, status update and import; which
      realization each target used (main or alternative).
- [ ] Requested shared lemmas, escalations and promotion candidates, or "none".
- [ ] Duplication: both screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the re-run probe; both axiom prints; the lint line. The
      diff touches only your owned file.
- [ ] Sanity cases, executed (`decide`/`rfl` where they evaluate, otherwise as proved lemmas):
  - `x = []` gives output `[true]` for both targets;
  - `|x| = 1` and `|x| = 2^j - 1, 2^j`, around the width change (`n + 1` overflowing for target 2,
    `Nat.log 2 n` stepping for target 1).

## Known pitfalls at this pin (hard-won)

- `Cfg.inputPos : Fin (|input| + 2)` starts at `1`; `0` and `|input| + 1` are the clamped blanks
  (`moveInputPos`); compare positions by `.val`. `Cfg.init` has every head at `0` and every tape
  blank.
- `Nat.bits` is little-endian and `Nat.bits 0 = []`. `decide` cannot evaluate `Nat.bits`/`Nat.size`:
  use `Nat.size_eq_bits_len`, `Nat.lt_size_self`, `Nat.lt_size`, `Nat.size_one`.
- `FinTM.bufferTape w z = w[z.toNat]?` for `0 ≤ z`, blank otherwise. R8.5c's finish writes
  `bufferTape (bits |x|) (q - pos)` over `[pos, pos + |bits|x||)`. At `pos = 0` on a blank tape
  that is exactly `vhostCfg`'s buffer.
- `vhostCfg`'s buffer head is the source's `inputPos − 1`. The source starts at `inputPos = 1`
  with tag `true` (`VirtualTag 1 true`). Its state type is `S × Bool`.
- `vhostEmitTM` is defined on `1 + m` tapes, buffer first (`vhostBuffer`). Relocate by R1, never
  inside the transformer.
- `embedEmitCfg`'s output is `pre ++ c.output`. Start every embedded phase with output `[]`.
- `writeConstTM` overwrites "whatever it held before". Its contract is exact at `2|w₀| + 2` steps
  and ends at the live anchor `done`, not a halt: redirect it.
- `phaseHostTM` takes `q0` explicitly. The composite `FinTM`'s `initCfg` uses `q₀`, so set it to
  phase 1's `entry`: `exists_inputLengthTM`'s `entry` need not be its `q₀`. States `Σ i, Ph i`
  need `[Fintype I]`, `[∀ i, Fintype (Ph i)]` and `DecidableEq`. `FinTM` wants `State : Type`.
- `ComputesInSpace` asks for **one** `t` with `ComputesInTime x (f x) t` and
  `spaceUsed (initCfg x) t ≤ s |x|`. Take the halting time. `spaceUsed` is cumulative over
  `[0, t]`, per tape, summed.
- `bufferedCompTM_computesInTime`'s time is `t₁ + |y| + 2 + t₂`, with `|y| = |x| + 1` here.
- `computesFunInTime_cond_spaceUsed` (alternative only) wants its space bounds `∀ x t`, after
  halting too. Halting is absorbing, so these follow from the bound at the halting time by
  monotonicity.
