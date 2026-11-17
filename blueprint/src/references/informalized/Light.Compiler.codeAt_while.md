<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.codeAt_while -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction locations in while loops

**Claim.** If a compiled while loop occurs as a prefix beginning at $pos$, then its compiled condition, compiled body, and back-jump occur respectively at $pos$, $pos+\mathrm{size}(c)$, and $pos+\mathrm{size}(c)+\mathrm{size}_{G.F}(s)$.

**Proof.** Unfold the while-loop compilation: it is the compiled condition, followed by the compiled body, followed by the single jump back to $pos$. Split the assumed prefix successively at these concatenation boundaries. The first piece is therefore a prefix at $pos$, and the remaining pieces begin after the lengths of the preceding pieces (`WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`). The compiled condition and body have lengths $\mathrm{size}(c)$ and $\mathrm{size}_{G.F}(s)$, respectively (`Light.Compiler.length_compileCond`, `Light.Compiler.length_compileStmt`); substituting these lengths gives the stated locations.

**Key facts.** `WordRAM.CodeAt.left`, `WordRAM.CodeAt.right`, `WordRAM.CodeAt.cast_pos`, `Light.Compiler.length_compileCond`, `Light.Compiler.length_compileStmt`.
