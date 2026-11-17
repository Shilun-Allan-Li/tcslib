<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.goes_inputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Processing the Input Region

**Claim.** Under the stated register conditions, the counter program processes the entire input region, emits the encoded instruction bits in order, clears its position counters, and reaches the snapshot phase with the specified updated registers and unchanged input position within the stated step bound.

**Proof.** Define a register record $\mathrm{st}(p,a,b,c)$ by starting from $e$, advancing the instruction position by $p$, setting the preceding-cell register to zero when $t=0$ and otherwise to the advanced position minus one stride, and setting the hard-wired-input, free-input, and inner-loop counters to $a,b,c$. The single-position result (`goes_inp_one`) applies at each position in this region: its index and stride hypotheses follow from the index formula, while the required source-list and layout-source conditions are checked for the phase in question.

1. At position zero, the program processes phase $p0$ and emits the first instruction encoding. It then copies $|z|$ into the inner-loop counter. The first loop, justified by the repeated-loop execution result (`goes_loop`), processes the $|z|$ hard-wired positions in sequence. At each position the phase is $zA$ exactly when the loop index is zero and $zB$ otherwise; processing that phase advances the hard-wired position counter. The loop emits the corresponding instruction bits and leaves the inner-loop counter at zero.
2. The program next copies $n$ into the inner-loop counter and processes the $n$ free-input positions with a second application of `goes_loop`. At each position it uses phase $uA$ precisely at the first free position when the hard-wired portion is empty; otherwise it uses $uB$. The zero tests in the program implement this boundary choice. Each position advances the free-input counter, emits its instruction bits, and decrements the loop counter, which again ends at zero.
3. At the right end, the two end phases are selected by zero tests on the hard-wired and free-input counters: phase $e1$ is used only when both portions are empty, and phase $e2$ otherwise. The single-position result handles this final position. The program then clears the hard-wired and free-input counters using the counter-clearing result (`goes_clearR`), reaching the snapshot phase with both counters zero.

Concatenate these executions using sequential composition (`Goes.trans`). The output is the concatenation of the instruction encodings at the consecutive indices from $e.i$ through $e.i+|z|+n+1$, which is the stated range. The individual execution bounds, including the two loops and counter clearing, sum to at most $(|z|+n+2)(L_{\max}(M)+20)$; the initial register equalities identify the composed start and end records with those in the claim.

**Key facts.** `Complexity.UTab.goes_inp_one`, `Complexity.UTab.goes_copyR`, `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.goes_jz_zero`, `Complexity.CounterProg.goes_jz_pos`, `Complexity.UTab.goes_incR`, `Complexity.UTab.goes_clearR`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`, `Complexity.CounterProg.Goes.mono`.
