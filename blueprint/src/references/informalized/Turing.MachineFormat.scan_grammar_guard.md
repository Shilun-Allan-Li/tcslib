<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.scan_grammar_guard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan grammar length bound

**Claim.** If parsing $\alpha$ yields $(b,r)$ and scanning succeeds with suffix $u$, then $(4k+5)3^{k+1}(\operatorname{val}(b)+1)\le |r|$.

**Proof.** Unfold the scan using the given successful parse. Success forces both preliminary tests—the canonical-header check and format guard—to pass, and exposes successful reads of the unary state index and the transition table. The format’s table skipper is the fixed machine-format skipper. Its consumption bound says that skipping the table uses at least $(4k+5)3^{k+1}(\operatorname{val}(b)+1)$ bits in addition to the suffix left after the table. The erased-index identity relates the successful state-index skip to the corresponding state read; soundness of that read expresses $r$ as the unary encoding of the read index followed by the remainder after the index. In particular, that remainder is no longer than $r$. Combining these length inequalities yields the claimed lower bound on $|r|$.

**Key facts.** `Turing.MachineFormat.skipTable_consumes`, `Turing.codeEraseFin`, `Turing.codeReadFin_sound`.
