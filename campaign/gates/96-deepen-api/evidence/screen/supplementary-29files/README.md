# Supplementary screen (after staging; not in the dispatched bundle)

The pack cites four files that the 18-file population did not include: `TuringMachine/Simulation`
(`Action.apply_workTapes`), `Machines/ARMLoops` (`AHalt.embed_guardLe`), `Machines/ARMProof`
(`RegExt`) and `Codec/Langs` (the code languages). This screen widens the population to 29 files:
those four, `Machines/ARM`, `Codec/Word`, `ClassNP/NTIME`, `Nondeterministic`, `SavitchARM/Run`,
`Savitch` and `ExpBFS/Run`. It keeps only the pairs with a declaration of one of the PR's nine
Lean files on one side (`screen-changed-pairs.py.txt`), at base `7a14e855` and at head `89f4ebbc`.

**Result:** 51 pairs at base and 52 at head. The one new pair is the one already in the pack,
`NoEdge` against `Rel` (85%, the codec's query layout, an idiom).
