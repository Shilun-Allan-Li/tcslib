# Three-reader InputLength proposal — awaiting human API approval

**The complete public consumer now passes. No public API has been adopted.** This replaces the earlier single-reader proposal's unresolved returnScan action gap with exactly two further owner equations. It is a concrete three-reader approval artifact, not source/gate/merge clearance.

| Proposed non-simp public equation | Exact home | Formula |
|---|---|---|
| Turing.FinTM.controlAction_eq | TuringMachine/Simulation | controlAction m q = ⟨m, work actions constantly(none,0), no output, q⟩ |
| Turing.inputMoveAction_eq | TuringMachine/Build/Catalog | inputMoveAction inp q = ⟨inp, work actions constantly(none,0), no output, some q⟩ |
| Turing.inputFoldTM_tr_bwd | TuringMachine/Build/Scan | backward table row is inputMoveAction(-1)(.bwd a) on a symbol, inputMoveAction1(.done a) on blank |

All three proofs are rfl at their owning definitions, with empty AX and no simp/unfold registration. The complete existing definitions, imports, headers and other declaration bytes are preserved. `THREE-READERS.lean.txt` gives exact statements/proofs; all four full BASE/candidate owners, the full consumer doc/header/body and the exact final patch are supplied. BASE9b5 and dispatched FE9 d64 have identical source in these four owners.

The InputLength proof uses the three equations, existing Action.mapState field readers and pointwise funext. Actual import probing shows Action.ext/eta are absent; no new ext API/import/private generic bridge is introduced. Every needed reader home is already in the consumer import closure, with explicit routes in SOURCE-BINDING.json. InputSymbol is read through Cfg.inputSymbol_of_end. The historical fixed-stop first-entry body is reused as source data, with the actual original public doc/header and all preceding declarations preserved.

Actual bounded checks:

- Complete Simulation/Catalog/Scan candidate owners compile with0 errors/0 admission warnings. Raw linter warnings are0/28/9, respectively; no baseline lint rerun or global warning-clean claim.
- Full InputLength native and compiled source pass0 errors/0 admission warnings (5 ordinary linter warnings). Its complete public doc/header/body passes with all11 ordinary foreign TCSlib heads irreducible (1 linter warning).
- Fresh22 direct controls cover the11 heads:22 kernel-closed positive goals and22 matching intended negative rfl errors. The goals are byte-identical except the seal attribute, with common smartUnfolding=false. Metadata confirms no active definition simp/unfold row for any guard head.
- Fresh bounded footprints for the three new readers have0/0/1 ordinary foreign heads; the Scan reader's inputMoveAction guard passes in the final context. The two primitive constructor readers have no ordinary foreign TCSlib definition footprint to guard. No vacuous executed seal is invented for them.
- Four selected HEAD metadata/footprint roots are byte-identical in two fresh actual captures. Three proposed names are absent on actual MAC8 BASE. The existing consumer's complete raw type Expr/universes/name/owner and standard AX triple equal BASE exactly; all three new readers have empty AX. No all-owner/global ABI or theorem-value closure is claimed.

The full consumer seal covers the selected theorem and all its preceding source context; preceding private helper proofs themselves are not newly sealed. Footprints traverse the selected root type/proof, all reached types and own definition-helper values, stopping other theorem proof values (including generated same-owner ones) and foreign RHS. Projections/abbreviations are reported separately. Explicit public-target simp/rw/change arguments were reviewed: own inputLength definitions, local facts and published equations are used; no foreign definition unfolding exception is introduced.

All18 own wrapper calls have exited. Each runs one own Lean job at a time under shared local3/machine5 locks, nice10/j4 through byte-exact approved helpers; every shell sources the scratch environment and uses python3-I. Only a fresh complete APFS wholeMAC8 clone was compiled; own outputs were unlinked before writes. All895 original objects are physically rehashed unchanged; private output has895 members and changes exactly Simulation/Catalog/Scan/InputLength. No partial overlay or snapshot composition, whole downstream replay, copy-text screen, source/Git/R/X edit, public adoption, audit dispatch or mathematical fill occurred.

Earlier failed consumer drafts are preserved with their exact inputs/logs: initial missing SignType reflexivity, functional work-tape field transport, and rw's first-occurrence handling of an unreduced input match. They are implementation attempts, not successful seals. The final native4/sealed4/compiled4 are the actual passing inputs; initial Action.ext source was never elaborated after its absence was probed. The earlier frozen single-reader packet remains unchanged and historical.

Seyoon must approve these exact three public APIs before any source adoption. The existing definitions and imports require no proposed change. Root still owns source integration, appropriate downstream/current-tree validation, gate supplement/review and publication. No old scope/debt ruling is extended, and any follow-up auditor choice remains per item rather than inferred from the morning batch.
