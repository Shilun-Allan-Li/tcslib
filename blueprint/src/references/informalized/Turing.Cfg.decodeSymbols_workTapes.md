<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.decodeSymbols_workTapes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoded Work-Tape Contents

**Claim.** At every work tape and cell position, the decoded content is the original optional symbol decoded by the Boolean-symbol decoder.

**Proof.** The decoded configuration defines its work-tape content at tape $j$ and position $p$ to be $(D.workTapes\ j\ p).bind (decodeBool\ e)$. The claimed equality is therefore exactly the defining equation for that field.
