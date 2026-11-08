<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.cfgProg_wf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Program Well-Formedness

**Claim.** Under the stated validity assumption on the input sources, every source used at program index $i$ is valid for that index, and every instruction has source-list length equal to the configuration arity.

**Proof.** We prove the two assertions separately.

1. Fix an index $i$ in the program and a source in the source list of its instruction. The program-entry identity (`Complexity.cfgProg_getElem`) identifies that instruction with the one constructed at index $i$; the program-length formula (`Complexity.length_cfgProg`) puts $i$ in the range required by the index classification theorem (`Complexity.cfgIdx_cases`). That theorem says that the index is either a work-cell position, an input position, or a snapshot position. In each case, the corresponding index decoding result (`Complexity.cfgPos_cellIdx`, `Complexity.cfgPos_inpIdx`, or `Complexity.cfgPos_snapIdx`) identifies the instruction’s position with that type of location.

   Padding introduces only false constants: any source in a padded list either belongs to the original source list or is such a constant. In the cell case, the cell-source validity theorem (`Complexity.cellSrcs_valid`) gives validity for every original source. In the input case, `Complexity.inpSrcs_valid` gives validity, using the assumed validity of the sources in $\ell$. In the snapshot case, `Complexity.snapSrcs_valid` gives validity. False constants are valid by definition, completing all cases.

2. Every instruction is obtained by mapping the instruction constructor over a range, so any instruction in the program comes from some index. Its position determines one of the three source-list constructions, and padding gives each list length equal to the configuration arity (`Complexity.length_padSrcs`). For cell sources, their explicit list and the previous-snapshot sources have total length equal to the arity. For input sources, the explicit entries and previous-snapshot sources likewise total the arity. For snapshot sources, counting the fixed entries, the two entries for each work tape, and the previous-snapshot sources gives the same length. These counts use the definitions of the source lists and configuration arity.

**Key facts.** `Complexity.cfgProg_getElem`, `Complexity.length_cfgProg`, `Complexity.cfgIdx_cases`, `Complexity.cfgPos_cellIdx`, `Complexity.cellSrcs_valid`, `Complexity.cfgPos_inpIdx`, `Complexity.inpSrcs_valid`, `Complexity.cfgPos_snapIdx`, `Complexity.snapSrcs_valid`, `Complexity.length_padSrcs`.
