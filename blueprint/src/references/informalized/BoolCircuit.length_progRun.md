<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyProgram.lean :: BoolCircuit.length_progRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the program run

**Claim.** For every input list $x$, program $prog$, and initial list of Boolean blocks $init$, running the program yields a list of length $|init|+|prog|$.

**Proof.** Induct on the program, allowing the initial block list to vary. The empty program leaves the initial list unchanged, so the formula holds. For a program with first instruction $g$ and remaining instructions $gs$, the first step appends exactly one block, namely the output of applying the function selected by $g$ to its evaluated sources. Apply the induction hypothesis to $gs$ starting from this extended initial list. Its length is $|init|+1+|gs|$, which equals $|init|+|prog|$.
