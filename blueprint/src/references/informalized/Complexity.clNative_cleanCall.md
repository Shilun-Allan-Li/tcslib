<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clNative_cleanCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Call Machine for a Polynomial-Time Function

**Claim.** For a polynomial-time computable function $f$, there is a finite Boolean machine with entry and exit states and at least one work tape that, from any physical input and argument on tape zero, reaches a clean configuration containing $f(\mathrm{arg})$ within a polynomial bound, without visiting the exit state at any earlier positive time.

**Proof.** Choose a machine $E$ computing $f$ in time $b(|\mathrm{arg}|+1)^e$, as provided by polynomial-time computability. The installed-call construction (`Turing.FinTM.exists_installCallTM`) gives a machine $W$, entry and exit states, and a positive work-tape count. From the prescribed initial configuration it reaches the clean output configuration after some positive time $t$, with no earlier positive visit to the exit state. Its time bound is a constant multiple of $T(|\mathrm{arg}|)+|\mathrm{arg}|+|f(\mathrm{arg})|+1$, where $T(n)=b(n+1)^e$. The output-length bound (`Turing.MultiTapeTM.output_length_le`), together with the fact that $E$ outputs $f(\mathrm{arg})$, gives $|f(\mathrm{arg})|\le b(|\mathrm{arg}|+1)^e$. Thus the installed-call bound is at most $c(2b+1)(|\mathrm{arg}|+1)^{e+1}$: use $(n+1)^e\le(n+1)^{e+1}$ and $n+1\le(n+1)^{e+1}$ to absorb the output and argument lengths into the larger power. The clean configuration and first-visit properties are preserved from the construction.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`.
