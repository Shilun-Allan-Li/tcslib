<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/ProgramCode.lean :: Light.Compiler.length_through_dispatcher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Through the Dispatcher

**Claim.** For every program $P$, main procedure index $p_0$, and Boolean flag $d$, the concatenation of the head code, main code, all procedure body code, and dispatcher code has length three times the dispatcher position determined by $P$ and $d$.

**Proof.** The code through all procedure bodies has length equal to the dispatcher position (`length_through_bodiesCode`). The dispatcher itself has length twice its parameter (`length_dispatcher`). Since the full code is the concatenation of these two parts, its length is the dispatcher position plus twice that position, hence three times the dispatcher position.

**Key facts.** `Light.Compiler.length_through_bodiesCode`, `Light.Compiler.length_dispatcher`.
