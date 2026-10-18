# External audit pack — MIG-0b, round 2: the layering split made real, and the repairs

Repair round for `audits/mig0b-findings.md` (round 1: **0 blockers, 2 majors, 4 minors; does not
close**). The round-1 pack and bundle are unchanged and immutable; this pack supplements them. The
gate closes on a round with **zero blockers and zero majors**. Record findings in
`audits/mig0b-r2-findings.md`.

Round 1 found the segment, round and trajectory layers mathematically sound. Its majors concerned
the relocation:
- the planned split could not keep the proofs (private helpers, a fit-namespace bridge, and a probe
  that left out the seam consumers);
- the release export was narrower than the lemma it replaces.

In round 2 **the split is the draft.** It is one landing unit of 13 parts, generated from the
**landed** `Build/Contract.lean` (MIG-0a, PR #83) and the round-1 evidence. Each part is
elaborated in exactly its own import closure, with the fit namespace absent and the seam consumers
in their own module. The campaign commit is `1781a230` (PR #84, fills-8, merged while the round was
drafted; only `CodeSimulator.lean` and `Build/RecordTable.lean` changed, and every check was re-run
there).

**Bundle:** `audits/mig0b-r2-bundle.md`, in the order of `BUNDLE-FILES.txt`: this pack, the
standards, the design and backlog, the round-1 findings, the draft resolutions, the evidence
(`audits/evidence/mig0b/r2/`), the landed `Build/Contract.lean`, round 1's evidence, and every
source the unit moves, edits or cites.

## Resolutions (detail: `audits/mig0b-resolutions.md`, `NOTES-r2.md`)

| # | Finding | Resolution |
|---|---|---|
| 1 | major: the split could not keep the proofs | The three private helpers are deleted; their 12 uses cite Mathlib's `Finset.Icc_subset_Icc` and `Finite`'s `MultiTapeTM.runFrom_state_ne_none_of_le`. `counterLoopTMVia_done_witness` derives its round hypothesis from `Round.cut_some`. 13 parts are cut-checked; `MIG0bFit` does not occur in the unit |
| 2 | major: release export over `Type` | `Build/Seam`'s private `seamRelease_run_pos` is promoted as `seamReleaseTM_runFrom_pos` with its universes and step-commutation proof (and its two step lemmas). Round 1's export is dropped; the consumers' statements are unchanged |
| 3 | minor: lockstep entry | `Contract.lockstep_admissible`, `_map`; the condition is documented |
| 4 | minor: "two live exits" | Qualified to a singleton live escape distinct from the anchor |
| 5 | minor: alphabet sketch and attribution | A literal proof sketch (intermediate controls live, halted source, every exit set); full [AB09] entries |
| 6 | minor: records | Nine corrections listed (NOTES-r2 §10). The maintainer applied items 1–8 to `backlog.md` and `machine-library-design.md`, both bundled; item 9 concerns round 1's notes, which NOTES-r2 supersedes |
| Q11, Q14 | rulings "yes" | `counterLoopOrbit` is an `abbrev` of `roundOrbit`, its four unfolding proofs edited and checked; `ReturnContract.release`'s envelope through the pointwise lockstep |

**Also new** (NOTES-r2 §5). Raw-layer exports moving into `Build/Embed` and `Build/Seam` take
those modules' universes (`Type*`), by finding 2's principle:
- MIG-0a's `seamCompTM_runFrom_right` is replaced by the promotion of its polymorphic private twin
  `seamComp_right`;
- MIG-0a's `embedEmitCfg_unselected`, `Cfg.select` and `embedEmitCfg_select`, and the R1 lemma
  trio, are stated over `Type*`. fills-8 added a private `Type*` copy of the R1 lemma,
  `RecordTable.rt_embed_matches`.

Every earlier statement is an instance of its generalization (checked). The two raw-layer lemmas go
to `Finite`, not the vendored `Deterministic`.

## The unit and how it is checked

`Contract-mig0b-r2-unit.lean.txt` (5,792 lines). Each part has a rule line, `-- @landing`, an
optional `-- @moved-from`, and `-- @imports`. Its kind follows from these:
- **appended** to an existing module that it imports: `Finite` ×2, `StateRenaming`, `Build/Embed`,
  `Robustness/AlphabetReduction`;
- the **whole edited file** of an existing module that it does not import: `Build/Seam`,
  `Build/CounterLoop`, and `Build/Contract`, which becomes the facade;
- **new**: `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`.

`build.py` takes each MIG-0a declaration by name from the landed file and each MIG-0b declaration
by name from D and A, applies asserted edits, and records sources in `manifest.json`. It fails if
any landed or round-1 declaration is lost.

`cutcheck2.py` extends the stage-2 method (`audits/evidence/stage2-gate/scripts/cutcheck.py`):
- the closure is followed through existing modules too, so an appended part reaches every check
  whose closure holds its module;
- a `@moved-from` part is omitted where its old home is already imported (byte identity and
  printed-type identity are checked separately);
- a check stops if an existing module in it imports a module that an included part replaces.

`extras.lean` (generated) checks:
- the edited existing files whole, in their own closures;
- five downstream probes of Q11's consumers;
- three negative controls;
- the fit file over every landing module.

The files the landing PR would write are in `landing/`, with a diff for each existing file.

## Brief for the auditor

1. **Finding 1: is the split real?** Check that:
   - `MIG0bFit` is absent from the unit;
   - each part's check (`elaboration.log` §2) contains exactly that part's closure;
   - `Build/Contract/Seam` compiles over `Contract/Basic` and `Build/Seam` alone;
   - the helper rewrites (`trans`, `seq`, `seq_traj`, `live`, `branch_traj`, `branch`,
     `Segment.live`, `ReturnContract.toRound`) prove the unchanged statements;
   - `counterLoopTMVia_done_witness` no longer needs the fit namespace.

   **Challenge the extended cut-check method**: the closure through existing modules, the
   moved-part omission, the whole-file parts, and the clash assertion. Is a check against the old
   oleans of the lower modules plus the parts an adequate per-module check before the landing
   replay, which remains a separate obligation?
2. **Finding 2.** Is the promoted `seamReleaseTM_runFrom_pos` exactly the private lemma, universes
   and proof included? Are `seamReleaseTM_firstReturn` and `seamReleaseTM_visitedByTapeHead`
   unchanged (statements, printed types)? Does the fit file's `Type`-carrier instance meet your
   round-1 example?
3. **The generalizations of NOTES-r2 §5.** For each, is the new statement a pure universe
   generalization with the old one an instance, and is it right to make it now? The cases are
   `seamCompTM_runFrom_right`, the three MIG-0a Embed exports, the R1 trio and
   `workTapePos_runFrom_mem_Icc`. Rule on open question 2.
4. **Minors 3–5.** Check the admissibility lemmas, the qualified `RoundContract.release`
   docstring, and the admitted lockstep's sketch: is the intermediate-control claim (live, never
   `arReady q`) correct for `arTM`'s read, write and move controls, with `none ∈ X`, a halted
   source and zero work tapes?
5. **Q11.**
   - Are the four one-token edits the only proof changes `counterLoopOrbit`'s abbreviation needs?
     The sites are `CounterLoop:1156`, `CfgRecord:716` and `:729`, and `CodeSimulator:5841`
     (fills-8).
   - Do the negative controls show that they are needed?
   - Is it right that `Inclusions:2553` needs none?
   - Is the downstream probe set (`InputCall`, `CfgRecord`, `Inclusions`, `CodeSimulator`,
     `InputLength`) adequate before the landing replay?
6. **Q14.** `ReturnContract.release`'s new envelope proof and sketch.
7. **Identity against the landed file** (`elaboration.log` §3). Check that:
   - the landed file is the gated round-2 file with only its status paragraph changed;
   - each MIG-0a declaration's new home and edit flags are as stated: 33 moved, 4 retired, 3
     generalized, and proof edits only where findings 1 and Q14 and the R1 re-derivation of
     `embedEmitCfg_select` require them;
   - the round-1 declarations' fates are as stated: 91 kept, 2 retired, 4 generalized, 12 edited;
   - the moved lower-module lemmas are byte for byte unchanged.
8. **The revised layering plan** (NOTES-r2 §3). Check:
   - `Finite` rather than `Deterministic` (open question 3);
   - `StateRenaming` importing `Simulation`;
   - `Robustness/AlphabetReduction` importing the core, which puts the core in 170 modules'
     closures (open question 1);
   - the facade and its `## Contents`;
   - the core's 5-module closure and the acyclic graph (§7).
9. **fills-8** (NOTES-r2 §7). Are the re-located references right? Is
   `RecordTable.rt_embed_matches` correctly a member of the acknowledged R1 family (an
   accounting minor), retired at MIG-13 by `embedEmitCfg_eq` at its own signature?
10. **Records** (NOTES-r2 §10). Are the nine corrections right and complete, and is the head-bound
    coordination with H2 (ruling O9) right?
11. **Open questions 1–5** (NOTES-r2 §11): rule on each.
12. **Documentation and policy:**
    - docstrings with statement prose;
    - literal `**Proof sketch.**` paragraphs;
    - [AB09] and [AFM26] attributions with References entries in each new module;
    - ≤ 100 columns for new and changed lines.

    The lint delta is §6 of `elaboration.log`.
13. Report anything else the unit or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

All MEASURED, from `audits/logs/mig0b-r2-elaboration.log` (generated by `runall.sh` in one run)
and `audits/logs/mig0b-r2-axioms.log`:

1. **Environment.**
   - Commands: `bash tools/leanelab.sh <checkout> <oleans> <file>` only (direct `lean`, no `-o`,
     no olean written); no `lake`, git or network.
   - Checkout at `1781a230`, olean snapshot `oleans-f8`, toolchain `leanprover/lean4:v4.25.0`.
2. **Cut checks.**
   - The 13 landing parts: exit 0, 0 errors.
   - The 13 extras: the five edited existing files whole, the five downstream probes, the fit
     file, and two negative controls. A third negative control is the `CounterLoop` part without
     its edit. All exit 0 with 0 errors, except the three negative controls, which fail as
     required: without their Q11 edits, `CfgRecord` gives 2 errors, `CodeSimulator` 1 and
     `CounterLoop` 1.
   - Warnings are exactly those that the worktree's own files give when elaborated as copies
     (`Build/Seam` 5, `Build/Embed` 2, `Finite` 2, `Build/Catalog` 90, `CodeSimulator` 3), plus
     the one `sorry` warning in each check whose closure holds part 7.
3. **Identity** (`identity.py`). See item 7 of the brief. No landed or round-1 declaration is lost
   (asserted by `build.py`); the moved lemmas are byte-identical.
4. **Signatures** (`sigprobe.py`: `#check @Name` under `pp.all`, the old modules against the new
   closure). Printed types are identical for:
   - 23 of 27 MIG-0a public declarations;
   - 18 of 18 `Build/Seam`;
   - 31 of 31 `Build/CounterLoop`;
   - 2 of 2 moved;
   - 85 of 92 round-1 public declarations.

   Every difference is one of the stated generalizations, except `Traj.embed`, whose type differs
   only by the universe instantiation `.{0, 0}` of `Cfg.select`.
5. **Axioms.** 201 prints (every public declaration of the parts, and the 28 fit declarations).
   Only `FinTM.exists_alphabetReduction_lockstep` and `FinTM.alphabetReduction_contract` depend on
   `sorryAx`, and none depends on anything outside `propext`, `Classical.choice` and `Quot.sound`.
6. **Lint.** The repository's `scripts/style_lint.py`, on a copy of the landing files and of the
   same files at the worktree. One new finding: `Build/Contract/Basic` is 1,309 lines, over the
   1,000-line split threshold. One finding goes: the landed `Build/Contract.lean`'s size. File
   size alone is not a reason to split (user rule).
7. **Graph.** With the landing files substituted, the import graph (629 modules) is acyclic. The
   core's closure is `Configuration`, `Deterministic`, `Finite`, `Simulation` and
   `StateRenaming`, so `Build/Loop` and `Build/CounterLoop` can import it.
8. **Sizes.** Net +2,081 lines over 16 files (+3,260 / −1,179); MIG-0 totals about 3.2k with
   MIG-0a.
9. **Not established here:** the landing PR's full replay (the 170 modules that gain the core, and
   the 26 that depend on `Build/CounterLoop`).
10. **The maintainer's re-check.** With the same tool, checkout and snapshot, the maintainer
    re-elaborated all 26 cut files, the two `CounterLoop` negative controls, the axiom probe and
    the six signature probes. Results:
    - every count above is reproduced, and the three Q11 negative controls fail with 1, 2 and 1
      errors;
    - each negative control differs from its passing twin only by the one-token edit (checked by
      diff);
    - the six signature-probe outputs are byte-identical to the drafter's, so the printed-type
      comparisons of attestation 4 rest on reproduced output;
    - the axiom probe gives 201 prints, with `sorryAx` only in the two alphabet-reduction
      declarations.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Accounting corrections inside an acknowledged
duplication family (the R1 family) are minors. Findings go verbatim into
`audits/mig0b-r2-findings.md`. The gate closes when this round reports zero blockers and zero
majors.
