<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_length_search -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Search Computation

**Claim.** Under the stated register bounds and oracle answers, the computation from the length-bound state reaches the double-test state with register $12$ set to $F$, while satisfying the required conditions throughout.

**Proof.** Induct on the difference $F-v(12)$, generalizing the register assignment so that the induction remains applicable after an increment. If the difference is zero, register $12$ already equals $F$. The machine takes its equality branch directly when it also equals register $7$; otherwise it makes one length-oracle query at index $F$. The oracle answer is false, as required by the hypothesis, and the machine reaches the double-test state without changing the registers. These transitions are packaged by the one-step and reflexive reachability facts (\texttt{AReach.single}, \texttt{AReach.refl}, \texttt{AReach.step}). If the difference is positive, then $v(12)<F$, and the hypothesis $F\le v(7)$ ensures this index is within the searched range. The oracle consequently answers true. The machine increments register $12$ once, preserving the global register bound by (\texttt{register\_update\_le}); the remaining difference is one smaller, so the induction hypothesis completes the run. The transition sequence is again assembled with (\texttt{AReach.step}), and the machine's instruction-side condition is supplied at each stage by (\texttt{comp\_preS}).

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.vword_whole₁`, `Complexity.comp_preS`.
