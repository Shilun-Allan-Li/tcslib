# Overlap with `cryptography/pass-shelat-ch2-4` (2026-11-17)

This note looks ahead to the merge of `cryptography/pass-shelat-ch2-4` into `main`. It assumes
the merge order Seyoon set on 2026-11-17: this campaign merges into `main` first (W4, then W7),
and ch2-4 merges afterwards. It uses static analysis and trial merges only (`git merge-tree`,
with temporary commit objects; nothing pushed). No Lean was compiled.

Revisions: campaign `0ac28d18` (after #350); ch2-4 `c3689193`; main `b986b862` (after #353).
The campaign forked from main at `abd2bd3d` (#179). ch2-4 last synced with main at `2e3bfebd`.
`main` has no `TCSlib/Complexity/` change since either fork point.

## Summary

- **Lean overlap.** 18 `TCSlib/Complexity/` files are changed on both branches. Seven merge
  cleanly: Logspace/InputAccess, Logspace/QueryReshape, Build/Convention, Build/EmitIterBody,
  CodeSimulator, Simulation and UniversalBlock. Eleven conflict, and the set is the same in either
  merge order.
- **Records and tooling.** In the agreed order, ch2-4's merge meets **no** conflict outside Lean.
  The trial merge (campaign into main, then ch2-4) conflicts only in the 11 Lean files. In the
  other order, git's directory-rename detection would raise about 21 spurious file-location
  conflicts between `campaign/` or `devtools/` and ch2-4's `briefs/pass-shelat-ch5-8/`.
- **Exposure.** On the ch2-4 tree, 857 modules sit downstream of the 204 campaign-changed modules
  that tree contains. 421 of those 857 are in Cryptography, and 457 are files that ch2-4 changes
  or adds but the campaign does not touch. The static scans below found no broken name outside
  the 11 files, but a statement change can only be confirmed by compiling.
- **Order.** I see no reason to reverse the order. The Lean conflicts are the same either way.
  This order also spares ch2-4 the records and tooling conflicts.

## The eleven Lean conflicts

Both campaigns ran rule-10 reader work and dedup harvests on the same shared files. Most hunks
are therefore two independently added readers for the same definition.

| File | What each side did | Resolution | Effort |
|---|---|---|---|
| CircuitComplexity/UnaryCode | ch2-4 `encodeNat_def` (4 users); campaign `encodeNat_eq` (2 users), the same fact | Keep both (a duplicate fact), or keep one and re-point the other side's users (a rename, so it needs approval) | small |
| ClassNP/PolyTime | Both add `polyTimeComputable_iff` with the same statement | Keep one; choose the docstring | trivial |
| ClassNP/Reductions | Both add `polyTimeReducible_iff` with the same statement | Keep one | trivial |
| ClassP/DTIME | Both add `FinTM.decidesInTime_iff`. **The statements differ**: ch2-4's says `∀ x, ComputesInTime …`, the campaign's says `ComputesFunInTime (fun x => [indicator L x]) T` | Keep the campaign's statement, which Ladner, NTIME and NTimeHierarchy use. Re-derive ch2-4's form in its one ch2-4-only user (Randomized/SeedMajority) through `computesFunInTime_iff`, or add it under a second name | small, but a decision |
| TuringMachine (umbrella) | Each adds one import and its catalog entry (ModuleHost; UniversalParts) | Keep both | trivial |
| Build/EmitIterEmbed | ch2-4 public `safeRun_iff`; campaign private `safeRun_iff_segment`; doc-list line | Keep both; merge the doc line | trivial |
| TuringMachine/Deterministic | ch2-4 `indicator_def`; campaign `indicator_of_mem`, `indicator_of_not_mem` | Keep all three | trivial |
| TuringMachine/Encoding | ch2-4 `pairEncode_ne_nil` (used in 25 ch2-4 files); campaign `pairEncode_drop` | Keep both. Taking one side drops the other's lemma. | trivial |
| Build/Wrappers | ch2-4 hand-writes `emitCfg_state/_inputPos/_workTapes/_workTapePos/_output`; the campaign generates the same names with `attribute [simps (config := { isSimp := false })] emitCfg` | Keep one form; both together give duplicate names. ch2-4's ModuleHost uses `emitCfg_state`, so check that the generated statement has the same shape. | small |
| Build/Primitives | The campaign rewrote the pair map (MIG-1 F-B: `pairMapTM` removed, now `pairMapSndTM`/`fwdMapTM`; +2962/−1669). ch2-4 added the public `exists_pairMapSnd_computesInTime` (per-input time `40 · (time + \|pairEncode a b\| + 1)`), **proved through `pairMapTM`** and used by Build/WordTiming and Cryptography/Asymptotic/UniversalPadding/Machine | Take the campaign's file and re-prove ch2-4's lemma on `pairMapSndTM` with the same statement (the forwarding run is `fwdMapVirtual_run`). The campaign's `pairMapSndTM_computes` is a per-function bound, `22 · (n + 1 + Tg n)`, and does not give the per-input form directly. | **medium**: a proof port |
| ClassNP/SAT | **Two harvests of the same private clean-module layer to different homes.** ch2-4 (`dd5be2eb`, gate 03l) moved it to the new public `Build/ModuleHost` (672 lines; also used by Randomized/Build/IterateFind, IterateFindHost, Randomized/Repetition and Cryptography/…/Yao/HybridProof/ChunkScanner). The campaign (R4-1, R4-2, kind 3) moved it to `ClassNP/CleanCall` (374 lines) and `Build/EmitIterEmbed`, then added later work (the linear SAT verifier, RO-1, rule-10 repairs). | Take the campaign's SAT. ch2-4 made no other change to SAT and adds no public SAT declaration. `ModuleHost` stays for its Randomized and Cryptography users. | small textually; it **leaves a duplicate family** (below) |

## Debt this creates

**A duplicate family (new).** After both merges, `Build/ModuleHost` and `ClassNP/CleanCall` would
both publish the clean-module contract and its install/emit modules. Their names are `Clean`,
`clean_install` and `clean_emit` against `SatClean`, `satClean_install` and `satClean_emit`.
SAT's host (`satHostTM`, `satHost_call`) also parallels `ModuleHost.hostTM` and `host_call`. The
two can be collapsed later, with one citing the other. That needs a home decision across both
campaigns, so I have not proposed one.

**Duplicate readers.** If both reader pairs are kept, `encodeNat_def`/`encodeNat_eq` and the
indicator readers add small duplicate facts.

## What the campaign could do before W7 to ease ch2-4's merge (each needs approval)

1. **Adopt ch2-4's names where both sides published the same reader.** This is possible only
   for readers this campaign added after its fork and before it lands in main. It is a rename of
   our API. Saving: three trivial hunks and the duplicate facts.
2. **Publish `exists_pairMapSnd_computesInTime` on our side** with ch2-4's exact statement,
   proved on `pairMapSndTM`. This is new public API. ch2-4's Primitives hunk would then resolve
   to "take ours", with no proof port on their side.
3. **Settle `decidesInTime_iff`'s statement** with the ch2-4 maintainer before either branch
   lands.

None of these is required. Without them, ch2-4's merge resolves eight trivial or small hunks, the
SAT hunk, the DTIME reader and one proof port.

## Recommended verification (not run yet)

The static scans cannot see a changed statement. The definitive check is a trial compile of the
merged tree: campaign into main, then ch2-4, with the provisional resolutions above.
`exists_pairMapSnd_computesInTime` stays `sorry` until it is ported. The compile covers about
900 modules (the downstream closure plus main's own) through `leanelab-o.sh` within the pool,
about 2 to 3 hours with three workers. This snapshot is for the trial only and would be discarded.

## Method

- **Trial merges.** `git merge-tree --write-tree` gave four results:
  - main + campaign: 21 conflicts, all records, tooling, `AGENTS.md` or blueprint (the known W4
    set);
  - main + ch2-4: clean;
  - (main + ch2-4) + campaign: 11 Lean conflicts plus about 21 directory-rename file-location
    conflicts;
  - (main + campaign) + ch2-4: the same 11 Lean conflicts only.
- **Removed names.** I scanned the campaign's removed public declarations against ch2-4's code,
  with comments stripped. The hits were false matches: ch2-4 keeps its own same-named lemmas, as
  in `ComposeMachines.polyTimeComputable_flatMap_range`. The exception is `pairMapTM`, removed by
  the campaign and used by ch2-4's new Primitives lemma. ch2-4 removes one public declaration;
  no campaign file uses it.
- **Imports of deleted modules.** The campaign deleted `FormulaKit`, `FormulaKit/Emit` and
  `FormulaKit/Gate` (the RD-2 removal). Their only ch2-4 importers are files that ch2-4 does not
  change (`TCSlib.lean`, TQBF), so the campaign's versions win.
- **Duplicate declarations.** I scanned the trial-merged tree for duplicates. With the conflicts
  resolved on the campaign's side, it has no duplicate that is new relative to either branch.
  `controlAction_def`, added identically on both sides in Simulation, merges to one copy.
