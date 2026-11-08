<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.cell_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Template Bit Output

**Claim.** Under the stated bounds, register values, and phase-flag conditions, executing the cell template on the register state produces the bit string assigned to its instruction by the table construction.

**Proof.** The proof reduces execution of the cell template to the general instruction-output theorem (`Complexity.UTab.prog_instr_bits`). For that application, it first derives the preceding-cell register index: from $q+\mathrm{stride}=i$ when $t\ne0$ and the given layout index for $i$, the stride arithmetic fact `Complexity.UTab.prev_eq` yields the index of cell $(t-1,\tau,r)$. The register lookup facts (`ER.f_i`, `ER.f_q`, and `ER.f_lb`) express the relevant register values as $i,q,$ and $lb$.

The cell-index bound and time bound establish that the instruction lies within the table range (`Complexity.cellIdx_lt_succ`). The layout identification `Complexity.cfgPos_cellIdx` then shows that the table instruction at this index is the cell template kind with its padded cell sources; `Complexity.length_tabLayout` supplies the input-list length used in that identification. The phase-flag assumptions align the template's boundary flags with those used in the source list. The cell-source translation identity (`Complexity.UTab.cellS_toBitSrc`) identifies each translated template source with the corresponding prescribed bit source, and the padding identity (`Complexity.UTab.padS_toBitSrc`) accounts for the trailing false constants. Finally, `Complexity.UTab.ok_cellS` verifies the source-index validity conditions from the register bounds, and `Complexity.UTab.ok_padS` extends that validity to the padded list. These facts meet the hypotheses of `prog_instr_bits`, which gives the claimed equality of executed output and table-assigned bits.

**Key facts.** `Complexity.UTab.ER.f_q`, `Complexity.UTab.prev_eq`, `Complexity.cellIdx_lt_succ`, `Complexity.cfgPos_cellIdx`, `Complexity.length_tabLayout`, `Complexity.UTab.cellS_toBitSrc`, `Complexity.UTab.padS_toBitSrc`, `Complexity.UTab.ok_cellS`, `Complexity.UTab.ok_padS`, `Complexity.UTab.prog_instr_bits`.
