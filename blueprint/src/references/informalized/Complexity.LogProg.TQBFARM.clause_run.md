<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Leaf.lean :: Complexity.LogProg.TQBFARM.clause_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluating a Clause During the Run

**Claim.** Given the stated serialized suffix, register bounds, input-length bound, and zero scratch registers, the machine evaluates the clause into the accumulated truth bit and advances the pointer past its serialized literals, while maintaining the run conditions.

**Proof.** Proceed by induction on the clause. For the empty clause, its serialization contributes no literal bits, so the assumed suffix begins with the terminating false bit. The machine takes the false-reading branch from the clause state; the read lemma for that branch (`read_f`) supplies the run to the corresponding clause-end state. The empty-clause evaluation is false, so the final accumulated value is $s\lor\mathrm{false}=s$, and the registers are unchanged, as asserted by `fin_of`.

For a nonempty clause, write its first literal as $(v,b)$ followed by a tail clause. Its serialization begins with a true bit, then $v$ further true bits, a false terminator, and the polarity bit $b$. The true-reading lemma (`read_t`) starts the literal-processing run. The literal correctness theorem (`lit_run`) processes this encoding, evaluates whether the assignment gives variable $v$ the value $b$, and advances the pointer by $v+3$ positions, reaching the clause state with accumulated value $s\lor(\operatorname{asg}(st.K,st.S)(v)=b)$. Removing this literal's serialized block from the assumed suffix leaves exactly the serialized tail followed by the clause terminator and remaining suffix (`drop_add_of_drop`). The tail's serialized prefix fits within the input (`le_of_drop`), so the pointer increase preserves the register bound. The induction hypothesis now evaluates the tail from this new state. By the recursive definition of clause evaluation, its result combines with the first literal's truth value as $s\lor\operatorname{eval}(Cl,\operatorname{asg}(st.K,st.S))$. Concatenating the literal and tail runs with `AReach.trans`, and identifying the resulting endpoint with the claimed updated state via `reach_of_eq`, proves the result.

**Key facts.** `Complexity.LogProg.TQBFARM.read_f`, `Complexity.LogProg.TQBFARM.fin_of`, `Complexity.LogProg.TQBFARM.read_t`, `Complexity.LogProg.TQBFARM.lit_run`, `Complexity.drop_add_of_drop`, `Complexity.le_of_drop`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
