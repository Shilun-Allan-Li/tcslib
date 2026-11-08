<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: BoolCircuit.adderFamily_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language of the Adder Family

**Claim.** The adder family recognizes exactly the Boolean words encoding three equally sized blocks $a,b,c$ for which the value of $c$ is the sum of the values of $a$ and $b$.

**Proof.** Fix a word $w$. By the membership characterization for a circuit family (`BoolCircuit.DAGCircuitFamily.mem_language_iff`), membership means that the circuit indexed by the length of $w$ accepts $w$. Split according to whether that length is divisible by three. If it is, cut $w$ into consecutive blocks $a,b,c$ of width $|w|/3$; the first two blocks and the last have equal lengths, and their concatenation is $w$. The adder circuit’s evaluation on such a concatenation accepts exactly when the third block’s binary value is the sum of the first two (`BoolCircuit.adderCircuit_eval_append`). This proves both directions: acceptance yields the required blocks and value equation, and any such blocks and equation imply acceptance. If the length is not divisible by three, the family uses a constant-false circuit, which cannot accept. In this case no decomposition into three blocks of equal length can exist, since such a decomposition would make $|w|$ divisible by three. Thus both languages reject $w$.

**Key facts.** `BoolCircuit.DAGCircuitFamily.mem_language_iff`, `BoolCircuit.adderCircuit_eval_append`, `BoolCircuit.constCircuit_eval`.
