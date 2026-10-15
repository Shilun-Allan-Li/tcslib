# External audit pack — §13d G2–G4: mapped sweeps, the multi-track zoned carrier, the rebalance rows (statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, §2.1 (user decision CH34-Q3, 2026-10-08: Thm 3.1 at
`f log f`, through the Hennie–Stearns `k`-tapes-to-2 simulation of [AB09] §1.7). The zone layer
was revised at the book's design (`machine-library-design.md` §13d, decisions 13d.1–13d.7 of
2026-10-10); its G1 step (the alphabet-generic library) is landed and gated. **This gate audits
the statements of G2 (mapped sweeps), G3 (the multi-track zoned carrier over `Γ`) and G4 (the
rebalance and extension rows), stated as `Turing.Contract`s over MIG-0b's library (§16b item 5);
the retirement of the superseded zone declarations (13d.6); and a duplication-free restructure of
`Build/Catalog.lean` and `Build/Contract/Catalog.lean` that the user required before the audit.**
Every sorried theorem stands under a proof sketch; definitions have their real bodies; 68 public
theorems and all 34 definitions and abbreviations are proved or defined, and 6 theorems are
sorried (one of them a promotion that is proved at landing). Nothing is landed.

| File (bundle path) | Content |
|---|---|
| `audits/evidence/s13d/g24/G24Statements.lean.txt` (1,763 lines, MEASURED) | **the unit**: seven parts, each the body of one landing module or one addition to an existing module; 108 public declarations, 0 private |
| `audits/evidence/s13d/g24/landed/TCSlib/Complexity/TuringMachine/Build/Zone.lean.txt` (1,324 lines) | **the landed `Build/Zone.lean`**: the deletions, one promotion, the narrowed imports, the revised module docstring, three doc-only fixes, and Part Z |
| `audits/evidence/s13d/g24/landed/TCSlib/Complexity/TuringMachine/Build/Catalog.lean.txt` (12,863 lines) | **the landed `Build/Catalog.lean`**: Part M1 inserted, the plain rows restated through it, nine `simp`-set repairs, Part M2 appended |
| `audits/evidence/s13d/g24/landed/TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean.txt` (261 lines) | **the landed `Build/Contract/Catalog.lean`**: Part C1 inserted, `clearTM_contract` restated through it, its frames and trajectory re-proved, Part C2 appended |
| `audits/evidence/s13d/g24/G24-design.md` | **the design note**: decisions, homes, the statements with their contract fields, the restructure, G5's consumption, the retirements, sequencing, open questions, fill estimates |

Supporting evidence: `audits/logs/s13d-g24-statements-elaboration.log` (every check; §-numbers
below refer to it) with its companions `…-cutcheck.log`, `…-freeze.log`, `…-axioms.log` (and
`…-axioms-catalog-{before,after}.txt`), `…-names.log`, `…-retire.log`, `…-lint-baseline.log` and
`…-screen-{before,after}.txt`; `audits/evidence/s13d/g24/probes/G24Sanity.lean.txt` (the unit plus
42 `example`s) and `…/probes/G24FitProbe.lean.txt` (the unit plus the fit); the other landed forms
(`ZoneTape`, `ZoneRebalance`, the `TuringMachine` facade); `audits/evidence/s13d/g24/scripts/`
(`runall.sh`, which regenerates every log; `screens.sh` and `lintbase.sh`; the landing writers;
the freeze, axiom-comparison and chain scripts; the C1 gate's cut check, landing writer, name
screen, widths and cited scripts, and the retrofit copy-text screen, verbatim) and `…/parts/`
(the part files the unit is assembled from).

**Bundle:** this pack first, then the standards (`audits/TEMPLATE.md`, `policy.md`, `workflow.md`),
the design records (`machine-library-design.md`, `backlog.md`, `AroraBarakChapters3-4Plan.md`),
the files under audit, the probes, logs, scripts and parts, the library files the unit, the design
note or this pack cite (`Build/Zone.lean`, `Build/Catalog.lean`, the five `Build/Contract` modules,
`Simulation.lean`, `Configuration.lean`, `Deterministic.lean`, `Finite.lean`, `StateRenaming.lean`,
`Build/Seam.lean`, `Robustness/AlphabetReduction.lean`, the `TuringMachine` facade), the G1 gate
records, the A-S2 zone gate's findings, the B6, C1 and MIG-0b packs as precedents, and MIG-1's
design and gated unit (`BUNDLE-FILES.txt` lists them in order).

**Base and provenance (maintainer).** Rebuilt on 2026-10-14 at the campaign tip `f2d48ad5` (the
local `origin/complexity/arora-barak-ch3-4`; its Lean files equal `1b6b972c`'s, with PR #92, the B6
hosts, and PR #93, the ARM comments, merged; MEASURED, `git diff --name-only`), exported read-only
by `git archive` into the gate folder, with the olean snapshot `oleans-lb6` (Lean `v4.25.0`). No
fetch was run (it would write outside the gate folder); the local remote-tracking ref already had
the expected Lean content. A maintainer sub-agent wrote the files. The first build (at `759471be`
with `oleans-lm0b`) is superseded; its records are kept under the gate folder's
`work/superseded-r0/`. **Every check reported here is from the final run of `runall.sh` and
`screens.sh`**, after the last edit of any Lean part (elaboration.log header).

## The user's decisions on the first pack (2026-10-14)

1. **Open question 10 (duplication): remove both families before the audit; do not acknowledge
   them.**
   - (a) The mapped sweep tables must not repeat the plain ones: define the plain rows as the
     mapped rows at the identity map, keep every existing public statement of
     `Build/Catalog.lean` unchanged apart from definitional restatements (shown by the freeze),
     repair any broken proof minimally and report it, and let no proved plain row come to depend
     on the sorried mapped rows (shown by axiom prints before and after); if this is impossible
     without a regression, stop and report.
   - (b) The new contract instances must not repeat `clearTM_contract`'s field proofs: one shared
     constructor in `Build/Contract/Catalog.lean`, used by the new instances, with
     `clearTM_contract` re-pointed to it (proof only, statement unchanged).
   - Re-run the copy-text screen, one run at a time, niced; show both families gone and list
     every remaining pair with its disposition.
2. **Open questions 1–9** go to the auditor with the maintainer's recommendations as written.
3. **Rebuild at the tip** with `oleans-lb6`; rebase the facade edit onto #92's additions; state how
   this gate's Catalog edits and MIG-1 stage S interact, and recommend an order.

**Done** (attestations below): (a) without a regression, and (b); one stop condition was checked
and did not arise.

## What the gate covers

1. **G2, the mapped sweeps**: `Turing.copyMapTM`, `Turing.transferMapTM` (real bodies), their
   identity-map instances (`rfl`), their framed theorems (sorried), and their contracts with frames
   and a joint trajectory (proved from the framed theorems).
2. **The restructure**: the plain rows `Turing.copyTM`, `Turing.transferTM` defined as the mapped
   rows at the identity map, with three private proofs repaired; the shared constructor
   `Turing.sweepContract` with `Turing.sweepPost`, `Turing.sweepContract_traj`,
   `Turing.sweep_ite_keep`; `Turing.clearTM_contract` restated through them.
3. **G3, the carrier**: the alphabet `ZoneCell`/`ZoneSym`, per-track access, the layout with
   separators, the inner-packed encoding `Turing.zonedTape` and its invariants (all proved), and
   the represented virtual tape per track `Turing.zoneTrackTape` (proved).
4. **G4's pure layer**: the mirror and the left cascade, the scanned index, the total guarded
   rebalance, the extension by one level, the cascade's frame (a promotion) and its new home (the
   one new cascade fact, sorried), and the represented-tape statements of a rebalance.
5. **G4's rows**: the rebalance row per direction and track and the extension row, as
   existential `Turing.Contract`s (sorried), and what their endpoints imply (proved).
6. **The retirements** of 13d.6 and the landed form of `Build/Zone.lean`.
7. **Homes, imports, layering**, the landing obligations, the facade, and the sequencing with
   MIG-1 stage S.
8. **The fit**: G5 (the Hennie–Stearns assembly, not in this gate) consumes the G4 contracts
   (probe).

Out of scope: proofs and fill routes beyond the sketches; G5's statements (its own statement
phase); the two-tape universal machine (its design note runs in parallel); MIG-0b's library and
G1's generalization (landed and gated; cited only).

## Decisions in force (verify that the files reflect them)

**§13d, all taken by the user on 2026-10-10 as proposed:** 13d.1 blank separator cells between
zones; 13d.2 a laid-out `ℓ` plus an extension row; 13d.3 total rebalance contracts (the rows
realize the total pure cascade at the scanned index for every input); 13d.4 the track index in
finite control; 13d.5 `ZoneSym k := Bool ⊕ ZoneCell k`; 13d.6 the superseded declarations deleted
through the G3/G4 gate; 13d.7 G1's extent (landed). **Q7** (user, 2026-10-11): G2's one-tape core
is `Turing.scanTM`; `copyMapTM`/`transferMapTM` stay for the cross-tape consumers, with
`merge : Option Γ → Δ → Γ`, sharing one trace with the scan. **§16b item 5** (user, 2026-10-12;
backlog RD-5): G2–G4 after MIG-0b, stated as contracts from the start; the two open zone rows
retire through the G3/G4 gate. **2026-10-14** (user): start G2–G4 now; the decisions on the first
pack above. **The process rule** (§13d, binding): every Lean change from the revision is a PR the
user merges and a separate audit gate. **Plan §2.1**: `f log f`. **Policy**: hosts first (§1),
attribution ([AB09] §1.7 and Claim 1.5), statement prose and proof sketches, 100-character lines,
no unacknowledged duplication.

## Dependencies

* **MIG-0b** (landed, PR #90): `Turing.Contract` (`Build/Contract/Basic`), and for the fit
  `Turing.Contract.branch`, `Turing.Contract.seq` (`Build/Contract/Seam`). Part R imports only the
  core module.
* **G1** (landed, PR #15): the alphabet-generic sweep rows and their framed contracts,
  `FinTM.bufferTape`; the §12.8 public trace `Turing.catalog_trace_run` and the scan.
* **The pure zone layer** (landed under tranche A-S2): `ZoneContents`, the pairwise ops, the
  cascade `zoneCascadeRight` with `zoneSide_cascadeRight`, `zoneCascadeRight_lengths` and the
  regressions, all proved.
* **PR #92** (merged): `StateRenaming.lean`'s two new theorems lie in this gate's closure through
  `Build/Contract/Basic`; `oleans-lb6` carries them.

## Homes and module names (proposed; the auditor rules on them)

| Part | Lands as | Namespace | Size at landing (MEASURED) |
|---|---|---|---|
| Z | appended to `Build/Zone.lean`, with the retirements and narrowed imports | `Turing` | 1,175 → 1,324 lines (281 deleted, the docstring rewritten, Part Z appended minus its sorried copy of the promoted lemma) |
| M1 | inserted in `Build/Catalog.lean` before `transferTM`; `transferTM`, `copyTM` restated | `Turing` | together with M2: 12,732 → 12,863 |
| M2 | appended to `Build/Catalog.lean` | `Turing` | (above) |
| C1 | inserted in `Build/Contract/Catalog.lean` before `clearTM_contract`; `clearTM_contract` restated | `Turing` | together with C2: 104 → 261 |
| C2 | appended to `Build/Contract/Catalog.lean` | `Turing` | (above) |
| T | new `Build/ZoneTape.lean` | `Turing` | 492 |
| R | new `Build/ZoneRebalance.lean` | `Turing` | 331 |

**Why one unit holds seven parts**, and the cut: as in the C1 pack. Each part becomes its module;
each landing module's import closure is elaborated on its own (cutcheck.log). Three checks
complement the cut check, because the landings also *edit* existing files: the **landed
`Build/Zone.lean`** standalone and the **landed zone chain** (landed `Zone` + `ZoneTape` +
`ZoneRebalance` in one file, on the narrowed closure); the **landed `Build/Catalog.lean`**
standalone; and the **Catalog chain** (landed `Build/Catalog.lean` with the core contract import,
then the landed `Build/Contract/Catalog.lean`'s body), since the snapshot's olean of
`Build/Catalog` does not hold the restructure.

**Why these homes** (design note §1). The pure additions belong with the pure layer. The carrier
is a separate module because it needs `Simulation` and the pure layer, after the retirements,
needs no machine module. The rows need the carrier and the core contract module only. G2 lives
with the rows it generalizes, so that one table serves both (and, at the fill, one trace).

**Landing obligations** (outside the audited statements): the facade
(`landed/TCSlib/Complexity/TuringMachine.lean`, built on #92's facade: two imports after
`Build.Zone`, the `Build/Zone` entry revised and two entries added; retire.log §4);
`Build/Catalog`'s module docstring lists the two rows in Part 3; `Build/Contract/Catalog`'s
`## Main definitions`/`## Main results` gain Part C's names; design §13d and backlog RD-5 record
the landing; **a downstream replay of `Build/Catalog` (80 modules), `Build/Contract/Catalog` and
`Build/Zone`** by the user, since this gate writes no olean.

## What the files state (verify)

**Part Z** (`Turing`; `G24Statements.lean.txt:58–545`; 37 declarations: 29 theorems, 8 definitions):
- `ZoneContents.words side z` (def), `words_le`; `ZoneContents.swap` (def), `swap_swap`.
- `zoneCascadeLeft j z := (zoneCascadeRight j z.swap).swap` (def); `zoneSide_cascadeLeft`,
  `zoneCascadeLeft_lengths` (by the right lemmas at the mirror). `zoneCascade dir` (def).
- `zoneShiftIndex dir z` (def, `List.findIdx` over `List.finRange ℓ` of "the feeding zone is
  nonempty"); `_le`, `_empty`, `_nonempty`, `_eq`, `_eq_length_iff`.
- `zoneRebalance dir z` (def: the cascade at the scanned index if `< ℓ`, else `z`);
  `zoneRebalance_of_le`, `zoneRebalance_false`, `zoneSide_rebalance_right`/`_left`.
- `zoneCascadeRight_frame` (**sorried in the unit; at landing the private lemma of
  `Build/Zone.lean:661` made public with its proof; statement identical**, elaboration.log §8);
  `zoneRebalance_frame` (from it).
- `ZoneContents.extend` (def: one more level, each new zone `replicate (2^ℓ) none`);
  `extend_words_castSucc`, `extend_words_last`, `zoneSide_extend`, `zoneShiftIndex_extend`,
  `_extend_of_lt`.
- `zoneTrackTape z p` (def); `_empty`, `_swap`, `_extend`, `_homeWrite`.
- `zoneCascadeRight_home` (**sorried**): under `zoneSide_cascadeRight`'s hypotheses, the new home
  is `(zoneSide z.right).headI`. `zoneTrackTape_cascadeRight`/`_cascadeLeft`,
  `zoneTrackTape_rebalance_right`/`_left` (proved, modulo the home).

**Part M1** (`:546–634`; 2 definitions): `copyMapTM k src dst extract merge`,
`transferMapTM k src dst extract merge rest` — the copy's and transfer's tables with the write
`merge (w dst) (extract b)` and the residue `rest b`. **At landing** they precede the plain rows,
and `transferTM k src dst := transferMapTM k src dst id (fun _ s => s) (fun _ => none)`,
`copyTM k src dst := copyMapTM k src dst id (fun _ s => s)`.

**Part M2** (`:635–734`; 4 theorems): `copyMapTM_plain`, `transferMapTM_plain` (`rfl`; in the unit
against the old definitions, in the landed file against the new); `copyMapTM_run_ofCfg`,
`transferMapTM_run_ofCfg` (**sorried**): the §12.6 framed contracts, with the destination's
original cell merged.

**Part C1** (`:735–857`; 4 declarations): `sweepPost done a v w d` (def: `d` at `done` with tape
`a`'s word interval overwritten by `v`); `sweepContract M entry done src touched x post hpost hrun`
(def: the contract of any §12.6 sweep row from its framed theorem); `sweepContract_traj`
(untouched heads fixed); `sweep_ite_keep` (a cell outside an overwritten interval keeps its value).
**At landing** `clearTM_contract i x := sweepContract _ _ _ i (fun j => j = i) x (sweepPost .done i
fun _ _ _ _ => none) (fun _ _ => rfl) (clearTM_run_ofCfg i)`; `clearTM_contract_frames` is
`fun _ _ _ _ _ _ hq => sweep_ite_keep _ _ hq`, `clearTM_contract_traj` is `sweepContract_traj …`.

**Part C2** (`:858–949`; 6 declarations): `sweepMapWrite` (def: a mapped sweep's written values);
`copyMapTM_contract`, `transferMapTM_contract` (defs, the constructor at `sweepPost`; the transfer
nests two); `copyMapTM_contract_frames`, `transferMapTM_contract_frames`,
`copyMapTM_contract_traj` (one-line proofs from the shared lemmas).

**Part T** (`:950–1437`; 37 declarations, all proved or defined): `ZoneCell k`, `ZoneSym k`
(abbrevs); `zoneSlotOf t`, `zoneCellOfCell`, `zoneSlotSet t` with `zoneSlotOf_slotSet_self`/`_ne`;
`zoneStart i := zoneBase i + i + 2` with `_succ`, `_eq` (`= 2^(i+1) + i`), `_add_lt`, `_mono`,
`two_le_zoneStart`; `zoneOwner ℓ n := Fin.find …` with `_of_mem`, `_of_not_mem`, `_sep`,
`_beyond`, `_succ`; `zoneCells`, `zoneCellAt`, `zonedTape`; the invariants `zonedTape_zero`,
`_right`, `_left`, `_right_sep`, `_left_sep`, `_blank_outside`, `_right_word`, `_left_word`,
`_update_slot`, `_isSome`, `_homeWrite`, `_injective` (with `ZoneContents.ext'`), `_extend`, and
`zoneCells_length`.

**Part R** (`:1438–1763`; 18 declarations):
- `ZoneData k := Σ ℓ, Fin k → ZoneContents ℓ` (abbrev); `zoneRowPre`, `zoneRebalanceIndex`,
  `zoneRebalanceData`, `zoneExtendData`, `zoneRebalancePost`, `zoneExtendPost`, `zoneRowLo`,
  `zoneRowHi` (defs; design note §4's table).
- `exists_zoneRebalanceTM k` (**sorried**): `∃ C, ∀ dir t, ∃ S, Fintype S, DecidableEq S,
  M : MultiTapeTM 2 (ZoneSym k) S, entry done short, done ≠ short ∧ ∀ x, ∃ R : Contract M entry
  {some done, some short} (ZoneData k) x, R.pre = zoneRowPre ∧ R.post = zoneRebalancePost dir t
  done short ∧ R.lo = zoneRowLo (zoneRebalanceIndex dir t) C ∧ R.hi = zoneRowHi … ∧ ∀ D d,
  d.state = some entry → R.pre D d → R.time D d ≤ C * (2 ^ zoneRebalanceIndex dir t D + 1)`.
- `exists_zoneExtendTM k` (**sorried**): the same shape with exit `{some done}`, `zoneExtendPost
  done`, envelopes at level `D.1`, time `≤ C * (2 ^ D.1 + 1)`.
- Proved from the definitions: `zoneRowPre_rebalancePost`, `zoneRowPre_extendPost`,
  `zoneRebalancePost_state_done`, `zoneRebalanceData_of_short`,
  `zoneRebalanceIndex_extend_of_short`, `zoneRebalancePost_frames`, `zoneExtendPost_frames`.

## The restructure (verify against `freeze.log` and `axioms.log`)

- **Freeze, `Build/Catalog.lean`**: of 480 declarations, 475 identical (comment-stripped), **0
  statements changed**, 5 bodies changed: `transferTM` and `copyTM` (the restatements) and the
  three private trace lemmas `catalog_copy_forward`, `catalog_copy_trace`,
  `catalog_transfer_trace`; 6 added (Parts M1, M2). freeze.log prints each changed body's diff.
- **The repairs** (minimal, the only proofs that broke): the three private lemmas unfold the
  plain tables by name (`simp only [copyTM, hs]`, `simp [MultiTapeTM.step, copyTM, …]`, and the
  transfer's); with the restated tables they must also unfold the mapped one, so `copyMapTM`
  (`transferMapTM`) is added to those `simp` sets, at 9 sites (4 + 1 in the copy lemmas, 3 + 1 in
  the transfer's). No other proof changed; the landed file's warnings are the base's 90 plus the
  two new `sorry`s, so no repair introduced an unused `simp` argument.
- **Freeze, `Build/Contract/Catalog.lean`**: 3 declarations, **0 statements changed**, 3 bodies
  changed (`clearTM_contract`'s body; `clearTM_contract_frames`' and `clearTM_contract_traj`'s
  proofs); 10 added (Parts C1, C2). The re-pointed `clearTM_contract` is definitionally the old
  one: the sanity probe `clearTM_contract_via_sweepContract` proves `sweepContract … =
  clearTM_contract i x` by `rfl` against the snapshot's definition (and `copyTM = copyMapTM …`,
  `transferTM = transferMapTM …` likewise).
- **Axioms**: the 92 public declarations of the two base files have **the same axioms before and
  after** (`axcompare.py`; 0 changed, 0 missing, **0 gain `sorryAx`**); the plain rows' proofs keep
  their own private traces, so none depends on the sorried mapped rows. The 16 new declarations'
  axioms are listed; `sorryAx` reaches exactly the mapped framed rows and what is built on them.
- **Downstream**: 58 lines in 8 files outside the two Catalog files name `copyTM`, `transferTM` or
  `clearTM_contract` (whole word); none inside `simp`, `unfold`, `rw`, `delta` or an equation
  lemma (freeze.log, last section). The others are applications and `change` steps, which are
  definitional, so the restatement cannot break them; the user's replay at landing is the
  confirmation. `clearTM_contract` has no consumer outside `Build/Contract/Catalog.lean`.

## The retirements (verify against `retire.log`)

Deleted from `Build/Zone.lean` at landing (281 lines in 5 blocks, MEASURED): `zoneCellBits`,
`zoneCellOf`, `zoneCellOf_bits` (the paired-cell codec); `zoneTape`, `zoneTape_empty`,
`zoneTape_blank_outside`, `zoneTape_homeWrite` (the binary realization); the seven privates
`zoneStageWord`, `zoneStageWord_length`, `zoneStageWord_getElem`, `zoneStageSlot`,
`zoneStage_rightWindow`, `zoneStage_leftWindow`, `zoneStage_window_bounds` (ZF-A2's staging
window); `Turing.FinTM.exists_zoneShiftInTM`, `exists_zoneShiftOutTM` (the two sorried rows). No
Lean file of the base tree outside `Build/Zone.lean` names any of them (retire.log §1); records do,
and stay as history. The statement comparison of old and landed `Zone.lean` finds 36 declarations
identical, 1 changed (`zoneCascadeRight_frame`, `private` removed), 16 missing (the list), 36 added
(Part Z minus the promoted lemma). §3 prints the retired rows beside their replacements.

## Brief for the auditor

Restate every definition in your own words before reading its docstring, argue each sorried
theorem true in 2–5 sentences or exhibit a counterexample, and attempt at least the adversarial
instantiations of point 13 (failure modes 1–5 of `audits/TEMPLATE.md`). Have [AB09] §1.7 at hand:
the maintainer could not open the PDF in this session (no PDF renderer in the tool chain), so the
book locations come from the design records and the A-S2 gate's verified excerpt
(`audits/zone-infra-findings.md`: empty/half/full zones, paired occupancies summing to capacity, a
head move rebalancing through the first nonempty donor zone). Points to rule on:

1. **Fidelity to [AB09] §1.7** (failure mode 1). Zone `i` holds `2 · 2^i` cells and half full
   means `2^i`; the index is the least nonempty zone on the feeding side; a shift of index `i₀`
   costs `O(2^{i₀})`; fresh zones are half full of blanks. Are the declared deviations benign: one
   blank separator per zone (13d.1), inner packing, the `short` exit, the encoding `zonedTape`
   (one cell per slot, all tracks), the virtual blank as a stored `none` distinct from `⊠`?
2. **The restructure** (the user's decision). Is the restatement of `copyTM`/`transferTM` truly
   definitional (the `rfl` probes, `copyMapTM_plain`), and is every public statement of the two
   Catalog files unchanged (freeze.log)? Are the nine repairs minimal and confined to the three
   private lemmas? Is the axiom comparison complete (all 92 publics) and does it show that no
   proved row depends on the sorried mapped rows? Can any downstream proof depend on the old
   table's syntax (freeze.log's search; `change` is definitional)? Is `clearTM_contract`'s
   restatement through `sweepContract` faithful (the `rfl` probe, by proof irrelevance on the
   proof fields), and are the re-proved frames and trajectory the same statements?
3. **The shared constructor.** Does `sweepContract` say what each instance needs, for any
   `touched`, any `post` at `done`, any read tape `src`? Is `sweepPost` the endpoint of all three
   rows (the transfer's as two nested overwrites, source over destination)? Is `sweep_ite_keep`
   enough for every footprint stated?
4. **The G2 framed theorems.** True as stated? The merge with the **original** destination cell
   (read once, before it is written); `w = []` (time `2`, no write); a residue `rest` that blanks a
   cell (the source is read before it is rewritten, so the return pass still finds the left
   delimiter); arbitrary `Δ`.
5. **The carrier's invariants.** `zonedTape_right_word`/`_left_word` are what the framed sweeps need
   on tape 0 (delimiters at `-1` and `zoneCapacity i`, the left zone reversed in the sweep
   direction). Is `zonedTape_blank_outside`'s bound `zoneStart ℓ - 1` tight? Does
   `zonedTape_injective` say what a faithful encoding should, for a fixed `ℓ`?
6. **The represented tape.** Is `zoneTrackTape` the right per-track word for G5? Is
   `zoneCascadeRight_home` true under exactly the hypotheses of `zoneSide_cascadeRight` (including
   `j = 0`, the `2^(j-1)` room form, a donor shorter than `2^(j-1)`)?
7. **The scanned index and the total rebalance** (decision 13d.3). Is `zoneRebalance` the "total
   pure cascade at the scanned index"? Rule on the identity branch when every feeding zone is empty
   and on the `short` exit (open question 2). Check `zoneShiftIndex` at `ℓ = 0` and on empty
   contents.
8. **`exists_zoneRebalanceTM`** (sorried). True as stated, for **every** contents? The time bound
   `C · (2^{i₀} + 1)` uniform in `dir` and `t`, also in the `short` case (`i₀ = ℓ`); the tape-0
   envelope `zoneStart (i₀ + 1)`; the scratch tape blank before and after with its head restored;
   the input head and output untouched; `done ≠ short`; the absence of an `entry ∉ exits` clause
   (design note §4, remark (i)). Is anything about the fill route unsound or more expensive than
   `O(2^{i₀})`?
9. **`exists_zoneExtendTM`** (sorried). True as stated, at `ℓ = 0` and in general? Does
   `zonedTape_extend` describe exactly the cells it writes?
10. **The contracts' fields.** Exit sets, index `ZoneData k`, precondition, exact time with its cut,
    envelopes, frames lemmas. Is an existential contract with fields pinned by equalities adequate
    for G5 (the fit) and non-trivial (failure mode 2)?
11. **The fit** (`probes/G24FitProbe.lean.txt`). Does `trackStep_fit` show what G5 needs of one
    track's step? Are the G5-internal facts (design note §5, (a)–(e)) true and correctly classified,
    in particular the count bound `#{s | idx s > i} ≤ T/2^i + 1`? Is `amortized_le` the book's
    `Σ_i T/2^{i-1} · 2^i = O(T log T)`?
12. **Retirements, homes and sequencing.** No consumer outside `Zone` (retire.log §1); the landed
    `Zone.lean` changes nothing else; the narrowed imports; the homes (open questions 1, 3);
    `zoneSlot`, `zoneIndex`, `zoneIndex_eq_iff` left consumer-free (open question 6); the stated
    interaction with MIG-1 stage S and the recommended order (below).
13. **Adversarial instantiations** (at least these; the probes run several): **`k = 0`** (three
    symbols; the zoned tape records only the layout); **`k = 1`** (six symbols; probe `zA`);
    **`ℓ = 0`** (home only; every scan short; the extension writes cells `±2`, `±3`; probe `D0`);
    **empty contents** (index `ℓ`, identity, blank represented tape); **a non-classical input**
    (`L_0` full, `R_0` nonempty: exit `done`, contents unchanged, probe `zC`); **a donor shorter
    than half**; **a zone at capacity on one side and empty on the other**; **stored virtual blanks
    versus `⊠`**; **a full top receiver**; **`w = []`** and **a blanking residue** for the mapped
    sweeps; **`dir = false`** (probe on `zB.swap`); **an arbitrary scratch head and input head**;
    **two tracks** (track independence, the per-track merge probes); **the identity-map
    instances** (`copyTM` as `copyMapTM id`, probe by `rfl`); **`clearTM_contract` through the
    constructor** (probe by `rfl`).
14. **Duplication** (failure mode 5): the screen's delta and the dispositions below.
15. **Documentation and policy** (`policy.md`): module headers, statement prose, [AB09] locations,
    a literal `**Proof sketch.**` on every sorried or nontrivial theorem, the doc-only fixes,
    100-column lines; and report anything else the files, this pack or the design note misstate.

**Open questions (maintainer recommendations in italics; design note §8; as written, per the
user).**
1. *G2's home*: `Build/Catalog` (proposed) or a new `Build/MapSweep.lean`. *Catalog, landed after
   or rebased on MIG-1 stage S, which owns the file; the G2 fill only after stage S lands.*
2. *The exhausted feeding side*: the `short` exit (proposed), the cascade at `ℓ`, or a lazily
   extending row (the 13d.2 alternative). *The `short` exit.*
3. *Narrow `Build/Zone`'s imports* to `Mathlib.Algebra.BigOperators.Group.Finset.Basic` and
   `Mathlib.Data.List.FinRange` (the first alone gives 3 errors: a maintainer probe during
   drafting, not in the logs). *Yes.*
4. *Packing*: inner (proposed), outer, or free with a relation. *Inner.*
5. *The G4 rows as `∃` now, named at fill time* (the B6 precedent). *Yes.*
6. *`zoneSlot`, `zoneIndex`, `zoneIndex_eq_iff`*: keep or retire. *Keep until the Zone split.*
7. *One trace for copy and transfer*: the G2 fill derives the plain framed rows from the mapped
   ones (statements frozen, proof bodies swapped), so that no second trace family arises (the
   tables are already one). *Yes, in the G2 fill.*
8. *The scratch envelope*: time-implied (proposed) or explicit. *Time-implied.*
9. *The three doc-only fixes in `Build/Zone.lean`* in the landing PR. *Yes.*

(Question 10, duplication, was decided by the user: the families are removed.)

## Sequencing (design note §7)

* **PRs #92 and #93 are merged** into the base. The facade edit is built on #92's facade
  (retire.log §4: two imports after `Build.Zone`, the `Build/Zone` entry revised, two entries
  added; no hunk touches #92's lines).
* **MIG-1 stage S** (being built now; it owns `Build/Catalog.lean`). S's Catalog edits, per
  `audits/evidence/mig1/MIG1-design.md` §8 and its gated unit (`MIG1Statements.lean.txt`, Part 8):
  the endpoint lemmas `Cfg.ofWords_copy_endpoint` (after `copyTM_run_ofCfg`, base line 1078) and
  `Cfg.ofWords_transfer_endpoint` (after `transferTM_run_ofCfg`, base 1035), and the move of
  `rewind_scan_heads` and `rewind_heads` (base 10356, 10395) to `Simulation`; no row's proof
  changes in S. Its fill F-D later deletes the `f2_` region (from base 1785), adds the
  `Build/Primitives` import, writes the twenty space corollaries and retires the six canonical R3
  rows (base 1277–1700), with docstring edits at `:1047`, `:1093`, `:1135`; its rename map
  (`data/moved-names.json`) renames no declaration this gate touches. This gate's Catalog edits:
  Part M1 inserted before `transferTM` (base line 174), the bodies of `transferTM` and `copyTM`
  (180–233), the nine repairs (base 545–680), and Part M2 at the end. **The hunks are disjoint and
  the semantics independent**: S's endpoint lemmas and F-D's corollaries use the framed theorems'
  statements, never the tables' bodies; S's gated unit and MIG-1's draft never name `copyTM`,
  `transferTM` or `clearTM_contract` (whole-word search: no occurrence); F-D, not yet written, must
  not unfold the tables either (a brief rule). *Recommended order: S first* (in flight, owns the
  file), *then this gate's landing PR rebased on S*, re-running the landed-Catalog check, the
  Catalog chain, the freeze and the axiom comparison at S's tip; the G2 fill after S. If S slips,
  this gate can land first, and S's rebase is trivial, since its edits never touch lines this gate
  changes.
* After landing: the G2 fill, the cascade-home fill, the G4 fills (rebalance, then extension), a
  fill gate; then G5's statement phase.

## Repository-side attestations (verify or challenge)

Every number below is MEASURED from the logs of the final run; the only ESTIMATEs in this gate
are the fill sizes (design note §9: about 3,100 to 5,900 lines over five fill targets).
- **Elaboration** (log §1): the unit gives exit 0 and 0 errors; the only warnings are 6
  `declaration uses 'sorry'` (`zoneCascadeRight_frame`, `zoneCascadeRight_home`,
  `copyMapTM_run_ofCfg`, `transferMapTM_run_ofCfg`, `exists_zoneRebalanceTM`, `exists_zoneExtendTM`).
- **Cut checks** (`cutcheck.log`): each of the seven parts, in exactly its own import closure, gives
  0 errors, and the unit's imports are exactly the union of the parts' (5). **Landed forms**: the
  landed `Zone.lean` (narrowed imports) standalone 0 errors, 1 sorry (`zoneCascadeRight_home`; the
  promoted lemma is proved); the landed zone chain 0 errors, 3 sorries; the landed `Catalog.lean`
  standalone 0 errors, 92 warnings = the base's 90 (byte copy, same run) + the 2 sorries; the
  Catalog chain 0 errors, the same 92.
- **Freeze** (`freeze.log`): as in "The restructure" above.
- **Axioms** (`axioms.log`): 108 prints for the unit's public declarations, 6 for the fit probe and
  6 for the landed zone chain; every proved declaration depends on at most `propext`,
  `Classical.choice`, `Quot.sound`; `sorryAx` appears exactly through the 6 sorried theorems (the G2
  contracts, frames and trajectory; the represented-tape statements through
  `zoneCascadeRight_home`; `zoneRebalance_frame` and `zoneRebalancePost_frames` through the
  promoted lemma, sorry-free in the landed chain; the fit's `trackStep_fit`, through the rows). The
  fit's `amortized_le`, `run_cost_le`, `two_pow_eq_succ_sum`, `stopContract`, `zoneTrackStepData`
  are sorry-free. The Catalog before/after comparison: 92 unchanged, 0 gaining `sorryAx`.
- **Probes** (log §3–4): 42 sanity `example`s, 0 errors (the alphabet sizes at `k = 0, 1, 2`; the
  layout; `zA`'s tape cell by cell; the delimited-word lemma at a concrete zone; the index-0 move
  and its represented tape; a stay step; empty contents; the boundary extension at `ℓ = 0` and the
  retry; the classical index-1 shift `zB`; the mirror; the blocked non-classical `zC`; the plain
  copy as the mapped copy's instance; the per-track merge; the two `rfl` restructure probes). Four
  negative controls fail (1 error each). The fit probe elaborates with 0 errors; its declarations
  carry no `sorry`.
- **Names** (`names.log`): 108 declarations, all public; one full-name clash with the base tree,
  `Turing.zoneCascadeRight_frame`, the private lemma this unit promotes (by design); none shared
  with the pending units (MIG-1, the C1 assembly, the H1 harvest, the B5a canonizer overlay, RD-2,
  stage 2); three short-name overlaps in other namespaces (`ZoneContents.swap`, `swap_swap`,
  `extend`); a positive control catches both planted clashes.
- **Cited names** (log §7): every backticked identifier of the unit's comments was `#check`ed; those
  that do not resolve are variables and notation (`C`, `M`, `L_i`, `R_i`, `_left`), a module name
  (`Simulation`) and the sanity probe's label `clearTM_contract_via_sweepContract`.
- **Style lint** (log §5): `scripts/campaign_style_lint.py` over the landed modules, the facade and
  the base's `Build/Contract.lean` facade: 1 FAIL, 2 WARN (sizes: `Build/Catalog` 12,863 lines,
  `Build/Zone` 1,324). **The FAIL is pre-existing** (`lint-baseline.log`): the facade rule looks
  for an intermediate facade at `<dir>/<dir>.lean`, so the base's facade already fails it for all
  five `Build/Contract/` children (and two `EmitIter` modules); ours is one of those.
  `scripts/style_lint.py` on the four zone and contract files: 1 finding (`Build/Zone` over 1,000
  lines); on the base's `Zone.lean` it reports 3, which the landed form repairs except the size.
  **Widths** (log §6): no line over 100 characters in the unit, the probes, the four zone and
  contract files or the facade; the landed `Catalog.lean` has the base's 100 long lines, no new one.
- **Duplication** (`screen-{before,after}.txt`; the retrofit copy-text screen, verbatim, niced, one
  run at a time; labels are file basenames, so `Catalog.lean` covers both Catalog files). Before
  (the base's `Zone`, `Catalog`, `Contract/Catalog`): 455 declarations, 302 pairs, 106,512
  reproduced characters. After (the five landed files): 506 declarations, 319 pairs, 108,813
  characters; **24 new pairs, 7 gone, none across files**. By family:
  - **(a) the sweep tables — gone.** No pair involves `copyTM` or `transferTM` any more (their bodies
    are now one line each): the base's six table pairs among `copyTM`, `transferTM` and `clearTM`
    (73–100%) are gone, and six pairs among `copyMapTM`, `transferMapTM` and `clearTM` appear with
    the same reproduced amounts (369, 344, 478 characters). *Disposition*: the base's pre-existing
    sibling pairs (copy, transfer and clear differ in one write or one pass), carried over under
    the mapped names; the tables are now written once each, and no mapped table reproduces a
    plain one.
  - **(b) the contract instances — gone.** No pair involves `clearTM_contract`, its frames or its
    trajectory, and no field proof remains in any instance. Two pairs remain between the two new
    G2 instances: `transferMapTM_contract` ⊇ `copyMapTM_contract` (120 of 139 characters, 86%; the
    other way 120 of 233, 52%). *Disposition*: the two applications of the shared constructor
    with the same arguments (the transfer's endpoint nests the copy's), no proof text; inherent to
    two sibling instances.
  - **(c) 16 small in-file pairs in the new zone code** (`ZoneTape`'s right/left cell and separator
    lemmas, 50–95%, 11 pairs; `Zone`'s index lemmas, 54–72%, 3 pairs; the two right-rebalance
    bridges, 97–99%, 2 pairs; every body under 530 characters). *Disposition*: short mirror and
    sibling proofs, not covered by the user's decision; *recommended: accept, or factor by a
    `zonedTape_swap` mirror lemma and a rebalance-bridge helper in the fill window* (the auditor
    rules).
  - The base pair `zoneStage_leftWindow`/`_rightWindow` is gone with the retirement.
- **Nothing in the checkout was changed**; no lake or elan command and no fetch was run; git ran
  read-only (`rev-parse`, `diff --name-only`, `archive`); `lean` ran only through
  `tools/leanelab.sh`, which writes no olean; Python only as `python3 -I`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s13d-g24-statements-findings.md`. The gate closes when a round reports zero blockers and
zero majors; the parts then land as cut (homes as ruled), with the retirements and the restructure,
by a PR the user merges (the §13d process rule), followed by the user's downstream replay.
