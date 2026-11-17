<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satMap_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine Execution Matches Transducer Semantics

**Claim.** For an input split $x=p\mathbin{++}r$, the transducer machine started at the boundary after $p$ in state $q$ with output $o$ halts after $|r|+1$ steps and appends precisely the transducer semantics on $r$ to $o$.

**Proof.** Induct on the remaining word $r$. If $r$ is empty, the input head is at the end of $x$. The machine's end-of-input transition emits the final output prescribed by $\phi(q)$ and halts. Thus the output is $o$ followed by the semantics on the empty word, and the state is absent.

For the inductive step, write $r=b::r'$. At the current input position the scanned symbol is $b$, since $x=p\mathbin{++}(b::r')$. The machine emits $\varepsilon(q,b)$, changes state to $\delta(q,b)$, and advances the input head one place, yielding the canonical configuration at the boundary after $p\mathbin{++}[b]$ with output extended by that emission. The input-position calculation follows from the right-move rule when the head is not at the right boundary (`Turing.moveInputPos_pos_of_ne_right`); the input-symbol identification follows from the input-at-position fact (`Turing.FinTM.inputSymbol_at`), and configuration equality reduces to state, position, and output because there are no work tapes (`Turing.Cfg.ext_zero_tapes`). The remaining input is $r'$, so the induction hypothesis applies from this new configuration. It halts after $|r'|+1$ further steps and appends the semantics for state $\delta(q,b)$ on $r'$. By the recursive definition of the transducer semantics, this output is exactly the emission for $(q,b)$ followed by the semantics on $r'$, hence the semantics on $b::r$. Counting the first step gives $|r|+1$ steps in total.

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_pos_of_ne_right`.
