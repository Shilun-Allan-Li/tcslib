<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.lit_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through a Serialized Literal

**Claim.** If the input suffix at the pointer is the serialization of literal $(v,b)$ followed by a remainder, and the register bounds and scratch-register hypotheses hold, the machine evaluates that literal and returns to the clause state with the pointer advanced by $v+3$.

**Proof.** The literal serialization begins with a $1$, followed by $v$ copies of $1$, then a false terminator and the polarity bit $b$. The machine advances past the first bit and processes the remaining unary run. The literal-counter run (`lc_run`) counts the $v$ ones into register $V$, passes the terminator, and leaves the pointer advanced by $v+2$ from its starting position; including the initial step, the pointer is now $P+v+3$ and $V=v$. The required suffix after the initial bit follows from the drop-successor property (`drop_succ_of_drop`), while the serialization length bound (`le_of_drop`) and the input and register bounds justify the guarded run. If the clause was already satisfied ($s=\mathrm{true}$), the machine skips evaluation and returns true, as required by $s\lor(\mathrm{asg}(K,S,v)=b)$. Otherwise it invokes literal evaluation (`lv_run`), which compares the assigned variable value with $b$ and clears $V$. This yields the stated clause value and final register state; concatenating the runs and identifying their endpoints gives the result.

**Key facts.** `Complexity.le_of_drop`, `Complexity.drop_succ_of_drop`, `Complexity.LogProg.TQBFARM.lc_run`, `Complexity.LogProg.TQBFARM.lv_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
