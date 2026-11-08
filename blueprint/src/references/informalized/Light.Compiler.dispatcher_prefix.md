<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.dispatcher_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher Prefix Property

**Claim.** For natural numbers $j\le n$, the dispatcher with $j$ cases is a prefix of the dispatcher with $n$ cases.

**Proof.** Induct on $n$ while keeping the hypothesis $j\le n$. When $n=j$, the dispatcher is a prefix of itself. In the successor step, the induction hypothesis gives that the dispatcher with $j$ cases is a prefix of the dispatcher with $n$ cases. The dispatcher extension formula (`dispatcher_succ`) identifies the dispatcher with $n+1$ cases as the one with $n$ cases followed by the two instructions for case $n$. Appending a list to a list preserves the prefix relation, so the dispatcher with $j$ cases is also a prefix of the dispatcher with $n+1$ cases.

**Key facts.** `Light.Compiler.dispatcher_succ`.
