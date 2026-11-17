<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Transducer.lean :: Complexity.transducer_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transducer Run on a Suffix

**Claim.** Starting from a configuration whose input head is at position $i+1$ and whose state is $q$, the machine halts after $|l|+1$ steps when $l=x.drop\ i$, and its output is the configuration’s initial output followed by the transducer output on $l$ from $q$.

**Proof.** Induct on the suffix $l$. If $l$ is empty, the equality $l=x.drop\ i$ implies $i=|x|$. The input-symbol-at-position rule therefore says the head sees the blank symbol. The machine’s blank-input transition halts without emitting anything, so one step gives the claimed halting state and preserves the output. If $l=b::l'$, then $i<|x|$, and the head-position hypothesis together with the input-symbol rule shows that the machine reads $b$. The suffix equality also gives $l'=x.drop(i+1)$. Thus the first step moves right, enters state $\delta(q,b)$, and appends the emission $o(q,b)$ to the existing output. The right-movement rule establishes that the new head position is $(i+1)+1$. Apply the induction hypothesis to this new configuration and suffix $l'$. It gives halting after the remaining $|l'|+1$ steps and appends the emissions from $l'$ starting at $\delta(q,b)$. By the recursive definition of the transducer output, these emissions, preceded by $o(q,b)$, are exactly the output on $b::l'$.

**Key facts.** `Turing.FinTM.inputSymbol_at`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_pos_of_ne_right`.
