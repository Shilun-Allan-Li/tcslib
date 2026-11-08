<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.dispatcher_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dispatcher Extension by One Case

**Claim.** For every natural number $n$, the dispatcher with $n+1$ cases is the dispatcher with $n$ cases followed by the decrement and branch instructions for case $n$.

**Proof.** The dispatcher is formed by mapping each index in the range from $0$ to $n$ to its pair of instructions and concatenating those pairs. The range of length $n+1$ is the range of length $n$ with the final index $n$ appended. Distributing the mapping and concatenation over this decomposition gives the dispatcher with $n$ cases followed by the pair for index $n$.
