# Gate 161 resolutions

## Round 1: CLEAR (0 blockers, 0 majors, 3 minors, 4 notes; `findings.md`, verbatim)

The auditor found all 21 proofs correct against their frozen statements (V161-02, V161-03), the
evidence consistent with the submitted source (V161-04), and the statement freeze and imports
as disclosed (V161-01). **#371 is clear to merge at `24aa4050`.** Its precondition, #370 first,
holds: #370 merged at `ccbf930c` on 2026-11-18. The `ConfigCount` import was confirmed by Seyoon
on 2026-11-18 (`STATUS.md`, HANDOFF).

All three minors concern the gate's packaging and records. None touches the Lean, so none needs
a new head or round.

- **G161-01 (minor), recorded; kit follow-up.** The bundle carried only 3 of the 22 indexed
  citation homes, and the index missed `TuringMachine/ConfigCount.lean`. `WordSize.lean:897`
  cites `ComputesInSpace.computesFunInTime_and_forall_spaceUsed_le` in method notation, which
  the citation probe's syntax pass did not resolve. The auditor fetched the sources at the
  audited head and found no unresolved dependency.
  - **Follow-up (kit, `seyoon-devtools`):** resolve citation homes from the constants the
    compiled proofs reference, not from proof syntax, so that method notation is counted; and
    bundle every indexed home. Until then, packs list method-notation citations by hand.
- **G161-02 (minor), recorded.** The copy screen's population was the two owners. Extended to
  the indexed homes, both owners and `ConfigCount` (25 files, 536 declarations), it gives 14
  owner-target pairs, five more than the nine dispositioned. The auditor inspected the five and
  found no further re-proof of a published result. Their dispositions:

  | Target (owner) | Source | Class | Note |
  |---|---|---|---|
  | `space_with_start` (WordSize) | `redirectTM_spaceUsedByTape` | boilerplate | visited-set and field-comparison steps around a different machine |
  | `scale_computes` (WordSize) | `Turing.Cfg.mapState_mapState` | citation context | the lemma is cited; the overlap is the surrounding configuration rewriting |
  | `logarithmic_computation` (WordSize) | `Turing.Cfg.mapState_mapState` | citation context | as above |
  | `XSteps.trans` (Extended) | `WordRAM.Steps.trans` | parallel induction | the same induction on run length for a different relation (`XSteps` over `xstep`) |
  | `StepsIn.trans` (Extended) | `WordRAM.Steps.trans` | parallel induction | the same induction for the footprint-indexed relation `StepsIn` |

  The auditor indicates that no new duplication-debt acknowledgment is needed. **Follow-up (kit):**
  `screen.sh`'s population includes the citation homes from now on.
- **G161-03 (minor), corrected here.** The pack's "the Lean-backed sweep flags nothing" was
  wrong. The proof-syntax sweep found 0 read candidates. The Lean-backed sweep
  (`evidence/DEFSWEEP-SUMMARY.json`) lists five foreign identifiers in `WordSize.lean`. All five
  are benign:

  | Identifier | Where it occurs | Disposition |
  |---|---|---|
  | `Fin.castAdd` | tape-index arguments | Core; an argument, not unfolded |
  | `List.length` | equality arguments | Core; an argument, not unfolded |
  | `Turing.Cfg.init` | `congrArg` arguments and lemma instances | an argument to published lemmas, not unfolded |
  | `Turing.vhostEmitTM` | a machine argument to published lemmas | not unfolded |
  | `rfl` | proof terms | a term, not a definition read |

  None is passed as an unfolding argument, so none is a rule 10 read.

## Merge

Seyoon merges #371. After the merge, the RAM branch's build is the gate's replay output,
`oleans-cl161-cl160`, provided the merge's Lean equals the audited head's. The maintainer checks
this and records it.
