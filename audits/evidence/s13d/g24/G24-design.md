# §13d G2–G4: design note for the statement phase (2026-10-14)

**Status: a statement-phase design note, with its gate unit.** Nothing is landed. The unit is
`audits/evidence/s13d/g24/G24Statements.lean.txt` (scratch `G24Statements.lean`); every claim
below about what elaborates is from `audits/logs/s13d-g24-statements-*.log`. **Rebuilt
(2026-10-14) at the campaign tip** `f2d48ad5` (the local `origin/complexity/arora-barak-ch3-4`,
whose Lean files equal `1b6b972c`'s: PR #92, the B6 hosts, and PR #93, the ARM comments, are
merged), from a read-only `git archive` export, with the olean snapshot `oleans-lb6`, Lean
`v4.25.0`; and **restructured** after the user's decision on the first pack's duplication
question (§0, §2). The first build (`759471be`, `oleans-lm0b`) is superseded.

## 0. What is decided, and what this note adds

In force (verbatim sources: `machine-library-design.md` §13d, §16a, §16b; plan decision log):

* **13d.1–13d.7** (user, 2026-10-10): blank separators between zones; a laid-out `ℓ` plus an
  extension row; **total** rebalance contracts (the pure cascade at the scanned index, on every
  input); the track index in finite control; `ZoneSym k := Bool ⊕ ZoneCell k`; the superseded
  declarations deleted through the G3/G4 gate; G1 limited to Seam, Embed, `bufferTape` and the
  R3 sweeps (done, gated, PR #15).
* **Q7** (user, 2026-10-11): G2's one-tape core is `Turing.scanTM`; `copyMapTM`/`transferMapTM`
  stay for the cross-tape G3/G4 consumers, with `merge : Option Γ → Δ → Γ`, and share one trace
  with the scan.
* **§16b item 5** (user, 2026-10-12) and backlog RD-5: G2–G4 after MIG-0b, stated as
  `Turing.Contract`s from the start. MIG-0b landed (PR #90): the core `Build/Contract/Basic`
  imports only the machine core.
* **Start now** (user, 2026-10-14; plan decision log, backlog RD-5): the G2–G4 statements, with
  a two-tape universal design note in parallel (not here).
* **Process rule** (§13d, binding): every Lean change from the revision is a PR the user merges
  **and** a separate audit gate.
* **Plan §2.1** (user, 2026-10-08, CH34-Q3): Thm 3.1 is strengthened to `f log f`; this layer is
  the Hennie–Stearns half of that route.
* **On the first pack** (user, 2026-10-14): **remove both duplication families before the audit,
  do not acknowledge them** — (a) the mapped sweep tables must not repeat the plain ones (define
  the plain rows as the mapped rows at the identity map; every existing public statement of
  `Build/Catalog.lean` unchanged apart from definitional restatements, shown by the freeze; no
  proved plain row may come to depend on the sorried mapped rows, shown by axiom prints before and
  after); (b) the new contract instances must not repeat `clearTM_contract`'s field proofs (one
  shared constructor in `Build/Contract/Catalog.lean`, `clearTM_contract` re-pointed, proof only);
  re-run the screen. The other open questions go to the auditor with the recommendations as
  written. Rebuild at the tip, with `oleans-lb6`.

This note fixes what the decisions left open: the physical layout and packing, the statement
form of each row as a contract (fields named below), the case where the feeding side is
exhausted, the homes, and the retirements' mechanics. Open choices are §8.

## 1. Homes, imports and layering

| Part | Home | Imports (beyond itself) | Content |
|---|---|---|---|
| Z | appended to `Build/Zone.lean` | none; the module's own imports **narrow** to `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Mathlib.Data.List.FinRange` | G3/G4 pure layer |
| M1 | `Build/Catalog.lean`, **inserted before `transferTM`**; `transferTM` and `copyTM` then defined as these rows at the identity | none | G2: the mapped tables |
| M2 | appended to `Build/Catalog.lean` (after the scan) | none | G2: identity instances, framed theorems |
| C1 | `Build/Contract/Catalog.lean`, **inserted before `clearTM_contract`**, which is then defined through it | none (it imports `Catalog` and the core) | the shared sweep-contract constructor |
| C2 | appended to `Build/Contract/Catalog.lean` | none | G2 rows as contracts |
| T | new `Build/ZoneTape.lean` | `Build/Zone`, `Simulation` | G3 carrier |
| R | new `Build/ZoneRebalance.lean` | `Build/ZoneTape`, `Build/Contract/Basic` | G4 rows |

* **No cycle.** `Zone` (narrowed) imports two Mathlib modules; `ZoneTape` imports `Zone` and
  `Simulation`; `ZoneRebalance` imports `ZoneTape` and the core contract module
  `Build/Contract/Basic` (whose closure is `Configuration`, `Deterministic`, `Finite`,
  `Simulation`, `StateRenaming`). Neither new module is imported by anything but the facade.
  Parts M and C sit where the R3 rows and their contract instances already are.
* **The core contract module only.** Part R needs no adapter (`Contract.Seam`, `Contract.Embed`,
  `Contract.Catalog`) and no `Build/Catalog`: its cut check elaborates in the closure
  {`Zone`, `Simulation`, `Contract.Basic`} (cutcheck.log). The G4 fill will add `Build/Catalog`
  (the mapped sweeps, the scan) and `Build/Contract/Seam` (the compositions); both are below
  `ZoneRebalance` and do not import it, so no cycle arises then either.
* **Why narrow `Zone`'s imports.** After the retirements the pure layer uses no machine module
  (MEASURED: the landed `Zone.lean` elaborates on the two Mathlib imports alone, cutcheck.log).
  `Zone`'s only importer is the `TuringMachine` facade, which imports `Build/Catalog`,
  `Build/Embed`, `Build/Seam` and `Simulation` directly (elaboration.log §9), so nothing
  downstream loses a declaration. The narrowing exposed one dependence: `ZoneTape` used `ring`
  and `push_cast`, reachable only through `Zone`'s old imports; both were replaced by `omega`,
  and the **landed chain** (landed `Zone` + `ZoneTape` + `ZoneRebalance` in one file, on the
  narrowed closure) elaborates with 0 errors.

## 2. G2: mapped sweeps (Parts M1, M2, C1, C2)

**Rows.** `Turing.copyMapTM k src dst extract merge` and
`Turing.transferMapTM k src dst extract merge rest`, over any `Symbol : Type*`, `Δ : Type*`,
with `extract : Symbol → Δ`, `merge : Option Symbol → Δ → Symbol`, and for the transfer a
source residue `rest : Symbol → Option Symbol`. Real bodies, in the house idiom of the R3 rows
(phase alphabet `Turing.SweepPhase`): the forward pass reads the source cell `γ` and the
destination cell `c` (possibly blank) and writes `merge c (extract γ)`; the transfer's return
pass rewrites each source cell to `rest γ`.

**The tables are written once** (the user's decision (a)). At landing the mapped tables are
inserted before `Turing.transferTM`, and the plain rows become
`transferTM k src dst := transferMapTM k src dst id (fun _ s => s) (fun _ => none)` and
`copyTM k src dst := copyMapTM k src dst id (fun _ s => s)`. This is a definitional restatement:
the types are unchanged and the old and new bodies are definitionally equal
(`copyMapTM_plain`, `transferMapTM_plain`, `rfl`, which elaborate against the old definitions in
the unit and against the new ones in the landed file). Three private proofs of `Build/Catalog`,
which unfold the plain tables by name (`catalog_copy_forward`, `catalog_copy_trace`,
`catalog_transfer_trace`), are repaired minimally: the mapped table is added to their `simp`
sets, at 9 sites (freeze.log). No other proof changes; the plain rows' proofs keep their own
traces, so no proved declaration comes to depend on the sorried mapped rows (axioms.log: the 92
public declarations of the two Catalog files have the same axioms before and after). Downstream
of `Build/Catalog`, the plain rows are used through their theorems and in `change` steps, which
are definitional; no downstream proof unfolds them by name (freeze.log, last section).

**Framed theorems** (sorried, §12.6 shape; `G24Statements.lean.txt:673`, `:706`): from any
configuration in `sweep` whose source carries `w` delimited at relative `-1` and `|w|`, the row
reaches `done` at exactly `2|w| + 2`, not earlier; the destination interval
`[pos, pos + |w|)` holds `(bufferTape w (q - pos)).map fun γ => merge (d.workTapes dst q)
(extract γ)` (the merge with the **original** destination cell), the transfer's source interval
`(bufferTape w (q - pos)).bind rest`; everything else unchanged; the two touched heads in
`[pos - 1, pos + |w|]`, the others fixed.

**One contract constructor** (the user's decision (b); Part C1). `Turing.sweepContract M entry
done src touched x post hpost hrun` builds the contract of any two-pass sweep row of the §12.6
shape from its framed theorem `hrun`: index the word read on `src`, time `2|w| + 2`, exit `done`,
touched heads within one cell of the word interval, the others fixed; `Turing.sweepPost` is the
endpoint shape every such row has (one tape's word interval overwritten, everything else kept).
`Turing.sweepContract_traj` gives every such contract its joint trajectory, and
`Turing.sweep_ite_keep` the frame of an interval overwrite. At landing `Turing.clearTM_contract`
is `sweepContract _ _ _ i (fun j => j = i) x (sweepPost .done i fun _ _ _ _ => none) (fun _ _ =>
rfl) (clearTM_run_ofCfg i)` (its type unchanged; the new body is definitionally the old, the
sanity probe `clearTM_contract_via_sweepContract`, `rfl`), and `clearTM_contract_frames` and
`clearTM_contract_traj` are re-proved by the shared lemmas (proofs only). The mapped contracts
are the same constructor at `sweepPost` with `Turing.sweepMapWrite` (the transfer nests two
`sweepPost`s, the source's residues over the destination's merges).

**As contracts** (Part C2), through the shared constructor:

| Field | `copyMapTM_contract src dst hne extract merge x` |
|---|---|
| machine, entry | `copyMapTM k src dst extract merge`, `SweepPhase.sweep` |
| exits | `{some SweepPhase.done}` |
| index `ι` | `List Γ` (the source word) |
| `pre w d` | `w` delimited at the head of `src` |
| `time w d` | `2 * w.length + 2` (exact; the cut is the field) |
| `post w d` | `d` with state `done` and the destination interval merged |
| `lo`/`hi` | `src`, `dst`: `[pos - 1, pos + |w|]`; others: the start position |
| frames (proved) | `copyMapTM_contract_frames`: footprint `Ico pos (pos + |w|)` on `dst`, `∅` elsewhere; the transfer's on `src` and `dst` |
| trajectory (proved) | `copyMapTM_contract_traj`: every other head fixed |

**The shared trace.** The fills prove the framed theorems through the public
`Turing.catalog_trace_run`, the trace the scan and every two-pass row cite, by generalizing the
private copy and transfer families of `Build/Catalog` to the mapped forms; the plain framed rows
`Turing.copyTM_run_ofCfg`/`Turing.transferTM_run_ofCfg` then become their instances (statement
unchanged, proof-body swap; plan 12.2c item 5's "one mapped-sweep trace"), so no second trace
family arises (open question 7). `clearTM` is a one-tape row, not a mapped one; it stays.

**Per-track instance** (G3's names): `extract := zoneSlotOf t`, `merge := zoneSlotSet t` copies
track `t`'s column of a zone to a scratch tape, and back into a zone keeping every other track
(sanity probes: the merged cell holds the slot on `t` and `⊠`/the old slot elsewhere).

## 3. G3: the multi-track zoned carrier (Part T, and Part Z's track tape)

**Alphabet** (13d.5). `ZoneCell k := Fin k → Option (Option Bool)`; per track, `none` is `⊠`,
`some v` an occupied slot storing `v : Option Bool` (`none` the virtual blank).
`ZoneSym k := Bool ⊕ ZoneCell k` (`abbrev`s, so `Fintype` and `DecidableEq` are inferred;
`|ZoneSym k| = 2 + 4^k`: 3, 6, 18 for `k = 0, 1, 2`, probes).

**Layout** (13d.1). Home at cell `0`. One blank separator precedes every zone: the right zone `i`
occupies `[zoneStart i, zoneStart i + zoneCapacity i)` with
`zoneStart i = zoneBase i + i + 2 = 2^(i+1) + i` (`zoneStart_eq`), the left zone `i` the mirror
image; `zoneStart (i+1) = zoneStart i + zoneCapacity i + 1`. For `ℓ = 2`:

```
cell:   -9   -8 -7 -6 -5   -4   -3 -2   -1    0    1    2  3    4    5  6  7  8    9   10 …
         |  [    L_1    ]   |  [ L_0 ]   |   home   |  [ R_0 ]  |  [    R_1    ]   |   blank
```
(`|` a blank separator; offset `p` of a left zone is at `-(zoneStart i + p)`, so the inner end of
`L_1` is `-5`; with `ℓ = 2` every cell from `±9` outward is blank, and the extension would lay out
`R_2` at `10…17`.) Zone cells are always `Sum.inr _`, so nonblank: each zone is a delimited
word.

**Packing.** Track `t`'s stored cells occupy the innermost slots of each zone, the rest `⊠`
(`zoneCells side z i` holds `((z t).words side i)[p]?` at offset `p`). Then: emptiness of a zone
on a track is one slot (the innermost), fullness one slot (the outermost), and the encoding is a
**function** of the contents, so a row's endpoint is an exact tape.

**Encoding.** `zonedTape z : ℤ → Option (ZoneSym k)` for `z : Fin k → ZoneContents ℓ`; the
owning zone of a distance is `zoneOwner ℓ n := Fin.find …` (computable; `decide` evaluates it).

**Invariants** (all proved, Part T): the home cell (`zonedTape_zero`); zone cells
(`zonedTape_right`/`_left`); separators blank for every `i`, laid out or not
(`zonedTape_right_sep`/`_left_sep`); blank outside the layout, `|c| ≥ zoneStart ℓ - 1`
(`zonedTape_blank_outside`, the replacement of the retired `zoneTape_blank_outside`); **each zone
a delimited word** in the sweep direction (`zonedTape_right_word`, and `zonedTape_left_word`
with the cells reversed), the precondition form of the framed sweeps; **track independence**
(`zonedTape_update_slot`); a contents-independent layout (`zonedTape_isSome`); the home write
as a one-cell write (`zonedTape_homeWrite`); what the extension writes (`zonedTape_extend`); and
**faithfulness** (`zonedTape_injective`). The fullness invariant is not a carrier invariant: it
is G5's (§5).

**The represented-word function per track** (Part Z). `zoneSide` (kept) gives a side's
half-word; `zoneTrackTape z : ℤ → Option Bool` is the virtual tape relative to the head (home at
`0`; stored blanks and positions beyond the words read blank). Proved: empty contents represent
the blank tape; the mirror reverses it (`zoneTrackTape_swap`); the extension does not change it
(`zoneTrackTape_extend`); a home write changes position `0` only; and, modulo one cascade fact
(`zoneCascadeRight_home`, sorried), a rebalance moves it by one cell
(`zoneTrackTape_rebalance_right`/`_left`, under the classical hypotheses at the index).

## 4. G4: the rebalance and extension rows (Part Z pure, Part R rows)

**Pure additions** (Part Z, proved unless marked): `ZoneContents.swap` and `zoneCascadeLeft :=
(zoneCascadeRight j z.swap).swap` with `zoneSide_cascadeLeft`, `zoneCascadeLeft_lengths` derived
by symmetry (13d: "never copied"); `zoneCascade dir`; the scanned index
`zoneShiftIndex dir z := (List.finRange ℓ).findIdx (fun i => !(z.words dir i).isEmpty)` (least
nonempty feeding zone, `ℓ` if none) with `_le`, `_empty`, `_nonempty`, `_eq`,
`_eq_length_iff`, `_extend`, `_extend_of_lt`; the **total guarded rebalance**
`zoneRebalance dir z := if zoneShiftIndex dir z < ℓ then zoneCascade dir (zoneShiftIndex dir z) z
else z`, with `zoneRebalance_false` (the mirror), `zoneRebalance_of_le`, `zoneRebalance_frame`
(levels above the index untouched), `zoneSide_rebalance_right`/`_left`; the extension
`ZoneContents.extend` (new level half full of virtual blanks) with `zoneSide_extend`; the cascade
frame `zoneCascadeRight_frame` (**a promotion**: the private lemma made public at landing with its
proof; sorried in the unit only); and `zoneCascadeRight_home` (**sorried**, the one new cascade
fact: the new home is the right word's head).

**The exhausted feeding side.** When every feeding zone is empty, the scanned index is `ℓ` and
the book's precondition (`R_{i₀}` exists) fails. The rebalance row then realizes the identity
and exits at a distinct `short` exit; the assembly runs the extension row and the rebalance
again, which scans to the new level `ℓ < ℓ + 1` and exits `done`
(`zoneRebalanceIndex_extend_of_short`). This keeps 13d.2's separate extension row and 13d.3's
totality: the pure operation is total, with an identity branch, in the A-S2 form (open question
2 records the alternatives).

**The rows** (sorried; `:1596`, `:1630`), with index `ZoneData k := Σ ℓ, Fin k → ZoneContents ℓ`:

| Field | rebalance `(dir, t)` | extension |
|---|---|---|
| statement | `∀ k, ∃ C, ∀ dir t, ∃ S [Fintype S] [DecidableEq S] (M : MultiTapeTM 2 (ZoneSym k) S) entry done short, done ≠ short ∧ ∀ x, ∃ R : Contract M entry {some done, some short} (ZoneData k) x, …` | `∀ k, ∃ C S … M entry done, ∀ x, ∃ R : Contract M entry {some done} (ZoneData k) x, …` |
| `R.pre` | `zoneRowPre`: tape 0 `= zonedTape D.2`, its head at `0`; tape 1 blank everywhere, head anywhere | same |
| `R.post` | `zoneRebalancePost dir t done short`: state `done` if `i₀ < ℓ` else `short`; tape 0 `= zonedTape (update D.2 t (zoneRebalance dir (D.2 t)))`; all else of `d` | `zoneExtendPost done`: tape 0 `= zonedTape (fun t => (D.2 t).extend)` on `ℓ + 1` levels |
| exits | `{some done, some short}`, live, distinct | `{some done}` |
| time | the field (exact, with the cut), `≤ C · (2^{i₀} + 1)`, `i₀ := zoneShiftIndex dir (D.2 t)` | `≤ C · (2^ℓ + 1)` |
| `R.lo`/`R.hi` | `zoneRowLo/Hi (zoneRebalanceIndex dir t) C`: tape 0 in `[-zoneStart (i₀+1), zoneStart (i₀+1)]`; tape 1 within `C · (2^{i₀} + 1)` of its start | the same at level `ℓ` |
| frames (proved from the post) | `zoneRebalancePost_frames`: tape 0 outside `[-zoneStart (i₀+1), zoneStart (i₀+1)]` and all of tape 1 | `zoneExtendPost_frames`: tape 0 outside the two new zones, all of tape 1 |
| chaining (proved) | `zoneRowPre_rebalancePost` (any state renaming) | `zoneRowPre_extendPost` |

Remarks. (i) `entry ∉ {done, short}` is not stated: it is forced, since a contract whose entry is
an exit has time `0` (`Turing.Contract.time_eq_zero_iff`), hence `post = d`, which fails for
`k ≥ 1` on the empty contents (`short`) or on any movable track. (ii) The tape-1 envelope is the
trivial one implied by the time bound (one cell per step); the informative space clause is tape
0's, the layout extent. (iii) The constant is uniform in `dir` and `t`, as G5 wants (one machine
per pair, same control up to the component read). (iv) The rows are `∃` statements, as the B6
hosts' (user, 2026-10-13: named machines at fill time); open question 5.

**Truth, briefly** (the auditor argues it in full). The rebalance is the composition of the
`2i₀ + 1` guarded steps of `zoneCascadeRight` at `i₀` (or their mirror), each local to levels
`i - 1` and `i` of both sides: under inner packing each guard reads single slots — the innermost
slot of zone `i - 1` (empty), its outermost slot (full), the slot at three quarters of zone `i`
(room for `2^(i-1)` more), the outer slot of zone `0` (room for the home) — at offsets a scratch
ruler of a zone measures; its move is a column copy to scratch (`copyMapTM`, `extract := zoneSlotOf t`), a re-pack there
(scans and rulers), and a column copy back (`merge := zoneSlotSet t`), all within the two zones
and their delimiters. Reaching level `i` on the mirror side costs `O(2^i)` (a ruler of the
distance to home). The scan to `i₀` costs `O(2^{i₀})`, and the short scan `O(2^ℓ)`, both
within `zoneStart (i₀ + 1)`. The sum is `O(Σ_{i ≤ i₀} 2^i) = O(2^{i₀})`
(`Turing.zoneCascade_cost_le`), with a constant independent of the contents.

## 5. How G5 consumes the rows (sketched; checked for fit by the probe)

One simulated step of a `k`-work-tape machine `M` on the two-tape `ZoneSym k` simulator:
1. **read the home tuple**: cell `0` is `inr c` with every `c t = some (home of t)`;
2. **transition** in finite control: writes `w t`, moves `m t`, input move, output;
3. **write the home tuple** (one step; `zonedTape_homeWrite`, `zoneTrackTape_homeWrite`);
4. **rebalance each moving track** `t` (`m t ≠ 0`): its row; on `short`, the extension and the
   row again — the per-track step of the fit probe;
5. input and output handled directly (`ComputesFunInTimeVia` with `e := Sum.inl`).

Startup writes the home cell `inr (fun _ => some none)` (`ℓ = 0`, all tracks `ZoneContents.empty
0`). After `T` steps, `Turing.FinTM.alphabet_reduction` gives a two-tape binary machine; with the
Z3 two-tape codes and the two-tape universal machine, Thm 3.1 at `f log f` (plan §2.1).

**The fit probe** (`probes/G24FitProbe.lean.txt`; its own declarations sorry-free, axioms.log):
* `trackStep_fit`: from the two rows **taken as given**, `Turing.Contract.branch` (on
  `done`/`short`) of the rebalance row into a zero-time stop and into `Turing.Contract.seq`
  (extension; rebalance) is a contract whose precondition is `zoneRowPre`, whose time is at most
  `(2C + C' + 2) · (2^{i₀} + 1)`, and whose endpoint satisfies `zoneRowPre` at the exact next data
  `zoneTrackStepData` — so per-track steps chain into the next track's;
* `amortized_le` (layer cake): if every index is at most `L` and at most `T/2^i + 1` of the `T`
  indices exceed `i`, then `Σ_s 2^{idx s} ≤ (L + 1)·T + 2^L` — [AB09]'s
  `Σ_i T/2^{i-1} · 2^i = O(T log T)`;
* `run_cost_le`: with a per-step cost of at most `A · Σ_t (2^{idx t s} + 1) + k`, the run costs at
  most `k · (A · ((L + 2)·T + 2^L) + T)`, `O(k · T log T)` for `L ≤ log₂ T + 2`.

**G5-internal facts, entering the probe as hypotheses** (none is sorried): (a) the classical
invariant per track and level (empty/half/full, `|R_i| + |L_i| = 2 · 2^i`) holds initially and is
preserved — by `zoneCascadeRight_lengths`/`zoneCascadeLeft_lengths` and the half/half extension;
(b) under it the rebalance moves the represented tape (`zoneTrackTape_rebalance_right`/`_left`,
whose hypotheses the invariant supplies); (c) the count bound `#{s | idx s > i} ≤ T/2^i + 1` per
track (between two shifts of index above `i` at least `2^i - 1` shifts of that track occur, since
the levels below are then half full); (d) at most `log₂ T + 2` levels are ever laid out; (e) the
controller's chaining cost: the sum of the per-track steps plus a dispatch step each, plus `O(1)`
for steps 1–3. A zero-time stop contract (`stopContract`) is defined in the probe as glue.

*Annotation at landing (2026-10-15; the gate's finding 1, carried to G5's statement phase):* the
probe's `run_cost_le` covers the rebalance phase only. Its step budget cannot absorb a fixed
per-step controller cost at `k = 0`, so (e) does not follow from it as stated. G5 either treats
machines with no work tape separately, or carries a fixed overhead (`B + A·Σ(2^idx + 1) + k`,
with `B·T` in the conclusion). `0 < k` is never assumed silently.

**One caution for G5, from the probes.** A `done` exit does not mean that the head moved: on a
non-classical input (`L_0` full, `R_0` nonempty) the scanned index is `0 < ℓ`, the cascade's move
is blocked by its guard, and the contents are unchanged (probe `zC`). G5's correctness rests on
the invariant (a), not on the exit.

## 6. Retirements (13d.6) and what stays

Deleted from `Build/Zone.lean` at landing (MEASURED: 281 lines in 5 blocks, retire.log):
the paired-cell codec `zoneCellBits`, `zoneCellOf`, `zoneCellOf_bits`; the binary realization
`zoneTape`, `zoneTape_empty`, `zoneTape_blank_outside`, `zoneTape_homeWrite`; ZF-A2's seven
private staging-window lemmas (`zoneStageWord`, `_length`, `_getElem`, `zoneStageSlot`,
`zoneStage_rightWindow`, `_leftWindow`, `zoneStage_window_bounds`); and the two rows
`Turing.FinTM.exists_zoneShiftInTM`, `exists_zoneShiftOutTM`, superseded by the G4 rows.

**Consumers**: none in Lean outside `Build/Zone.lean` (retire.log §1, every name, whole-word,
over `TCSlib/` and `TCSlib.lean`); the facade's docstring entry for `Build/Zone` mentions "its two
superseded shift rows" without naming them (revised at landing). Records mention them (design, plan, backlog, briefs, audits); those stay as
history. Z4's original consumer of `zoneTape_blank_outside` no longer exists (A-S2-2 replaced its
route); its successor is `zonedTape_blank_outside`.

**Kept unchanged** (statements): the layout arithmetic, `ZoneContents`, `ZoneContents.empty`,
`zoneSlot`, `zoneIndex`, `zoneIndex_eq_iff`, `zoneSide`, the pairwise ops and their lemmas, the
head steps, the cascade and its lemmas, `zoneCascade_cost_le`. `zoneSlot`, `zoneIndex` and
`zoneIndex_eq_iff` lose their only consumers (open question 6). **Changed at landing, besides
the deletions** (comment-stripped statements: identical except the promotion, retire.log §2):
`zoneCascadeRight_frame` public; the module docstring rewritten; doc-only fixes in `zoneSlot`
("physically blank … through the pairing" → `⊠` on the zoned tape), `zoneCascade_cost_le` ("the
row budget" of the retired rows), and the `**Proof sketch.**` label of the private
`zoneSide_adjacent`; the imports narrowed (§1).

## 7. Sequencing and overlaps

1. **This gate** (statements). On a clean round: **one landing PR** for the seven parts, the
   retirements, the restructure of the two Catalog files and the facade lines
   (`landed/TCSlib/Complexity/TuringMachine.lean`: the two imports after `Build.Zone`, the
   `Build/Zone` entry revised and two entries added; built on PR #92's facade), merged by the user
   (process rule). Then the user's downstream replay of `Build/Catalog`, `Build/Contract/Catalog`
   and `Build/Zone` (this gate cannot elaborate their downstream: no olean is written).
2. **PRs #92 and #93 are merged** into the base (`f2d48ad5`). This rebuild elaborates against
   `oleans-lb6`, which carries #92's `StateRenaming` (in this gate's closure through
   `Contract/Basic`); the facade edit is rebased onto #92's additions.
3. **MIG-1 stage S** (being built now; it owns `Build/Catalog.lean`). Per its design
   (`audits/evidence/mig1/MIG1-design.md` §8) and its gated unit
   (`audits/evidence/mig1/gate/MIG1Statements.lean.txt`, Part 8), S's Catalog edits are: the two
   endpoint lemmas `Cfg.ofWords_copy_endpoint` (after `Turing.copyTM_run_ofCfg`, base line 1078)
   and `Cfg.ofWords_transfer_endpoint` (after `Turing.transferTM_run_ofCfg`, base 1035), and the
   move of the head lemmas `rewind_scan_heads` and `rewind_heads` (base 10356, 10395) to
   `Simulation`; no row's proof changes in S. Its fill F-D later deletes the `f2_` region (from
   base line 1785), adds the `Build/Primitives` import, writes the twenty space corollaries and
   retires the six canonical R3 rows (`copyTM_run`, `transferTM_run` and four others, base
   1277–1700), with docstring edits at `:1047`, `:1093`, `:1135`. Its rename map
   (`data/moved-names.json`) moves `f2_`-region and forwarding-controller declarations to
   `Primitives` and `TimeConstructible`, and renames no declaration this gate touches. This
   gate's Catalog edits are: Part M1 inserted before `transferTM` (base line 174), the bodies of
   `transferTM` and `copyTM` (180–233), nine `simp`-set repairs in three private trace lemmas
   (base 545–680), and Part M2 at the end of the file. **The hunks are disjoint, and so are the
   semantics**: S's endpoint lemmas and F-D's corollaries use the framed theorems' statements,
   never the tables' bodies; S's gated unit and MIG-1's draft never name `copyTM`, `transferTM` or
   `clearTM_contract` (whole-word search: no occurrence), so they cannot unfold them; F-D, not yet
   written, must not either (a brief rule). *Recommended order: S first* (it is in flight and owns the file), *then this
   gate's landing PR rebased on S*, re-running the landed-Catalog check, the freeze and the axiom
   comparison at S's tip (minutes); the G2 fill after S. If S slips, this gate can land first:
   S's rebase is then trivial, since its edits never touch lines this gate changes.
4. **Fills** (after landing): G2 (the two framed rows, the plain rows as instances); the cascade
   home fact; G4 (the rebalance row, then the extension row); then a fill gate.
5. **G5**: its own statement phase (the simulation theorem, the invariant, the count bound), then
   alphabet reduction, the Z3 codes and the two-tape universal (design note in parallel).

## 8. Open questions for the user (maintainer recommendations in italics)

1. *G2's home*: `Build/Catalog` (Parts M1 and M2, as proposed; the 2026-10-10 plan put G2 there
   for the shared trace, and the plain rows are now defined through it) or a new `Build/MapSweep.lean` importing `Catalog`. *Catalog, landed after or
   rebased on MIG-1 stage S; the plain rows can then become instances of the mapped ones.*
2. *The exhausted feeding side*: a `short` exit (proposed), or the cascade at index `ℓ` (a
   well-defined but non-classical operation, after which G5 cannot extend), or a rebalance row
   that extends lazily (the alternative 13d.2 declined). *The `short` exit.*
3. *Narrow `Build/Zone`'s imports at landing* to the two Mathlib modules. *Yes: the pure layer
   then sits below every machine module.*
4. *Packing*: stored cells at each zone's inner end (proposed), or at its outer end, or free
   placement with a representation relation instead of an encoding. *Inner packing: one-slot
   emptiness and fullness tests, exact endpoints.*
5. *Named machines now, or `∃`*: the G4 rows as existentials (proposed, the B6 precedent),
   named at fill time. *`∃` now.*
6. *`zoneSlot`, `zoneIndex`, `zoneIndex_eq_iff`*: kept by 13d's list, but consumer-free after
   the retirements. *Keep them until the Zone split (12.2c item 9) decides; they are proved and
   cost nothing.*
7. *One trace for copy and transfer*: the G2 fill re-derives `copyTM_run_ofCfg` and
   `transferTM_run_ofCfg` from the mapped rows (statements frozen, proof bodies swapped), so that
   the mapped rows add no second trace family. *Yes, in the G2 fill (12.2c item 5's sweep half).*
8. *The rows' scratch envelope*: the time-implied radius (proposed) or an explicit tighter
   radius. *Time-implied: G5 needs only `O(2^{i₀})`; a tighter radius would fix the fill's route.*
9. *Doc-only fixes inside `Build/Zone.lean`* (three docstrings, §6) in the landing PR. *Yes.*
10. *Duplication*: **decided by the user (2026-10-14): both families removed before the audit**
    (§2); the remaining pairs and their dispositions are in the pack's attestations.

## 9. Size estimate for the fills (ESTIMATE, lines landed)

| Target | Estimate | Basis |
|---|---|---|
| G2: `copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`, the plain framed rows as their instances | +200 to +400 net | `Build/Catalog`'s private copy/transfer trace material is 160 lines (base `:518–680`, MEASURED; after the restructure its `simp` sets already name the mapped tables), generalized in place to the mapped families; the plain framed proofs then become instances; the scan's framed proof, 202 lines (`:12372`), is the from-scratch alternative |
| `zoneCascadeRight_home` | 30 to 70 | the induction of `zoneSide_cascadeRight`, home only |
| G4 rebalance row | 2,500 to 4,500 | 2 level loops, 4 guarded pair ops (2 per side and direction, mirrored by one parameter), the home move, scan and short exit, rulers, cleanup; contract composition through `Contract.seq`/`branch`/`inPhase` and a round host for the level loops; ZF-A3's 952 lines of infrastructure for the old design as a floor |
| G4 extension row | 400 to 900 | walk, ruler doubling, two writes, cleanup |
| **Total** | **about 3,100 to 5,900** | 5 fill targets (the promotion is not one) |
