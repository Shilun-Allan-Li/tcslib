<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Group_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Serialization of a Wired Group

**Claim.** If the unary words encoding the four parameter functions $m(x),s(x),t(x),p(x)$ are polynomial-time computable, then the serialized fragment of the corresponding wired clause group is polynomial-time computable.

**Proof.** Use the polynomial-time template-serialization result (`Complexity.clA5Template_native`), which reduces the task to computing each wire address in unary. For a template coordinate $j$ among the first $B$ positions, the wire address is $m+sB+j$, and its unary representation is polynomial-time computable from those of $m$ and $s$ (`Complexity.clA5Address_native`). For a coordinate among the next $B$ positions, the address is $m+tB+(j-B)$, computed in the same way from $m$ and $t$. Every remaining coordinate is the input-bit address $p$, whose unary word is already available. The two bounds on $j$ partition all template coordinates, so every wire has the required polynomial-time computation and the serialized group fragment follows.

**Key facts.** `Complexity.clA5Template_native`, `Complexity.clA5Address_native`.
