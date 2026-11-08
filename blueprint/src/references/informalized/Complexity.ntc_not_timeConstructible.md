<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_not_timeConstructible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# A Nonconstructible Time Bound

**Claim.** The time bound defined from the halting predicate cannot be time-constructible in the stated linear-in-bound sense.

**Proof.** Suppose the bound were time-constructible, and let $M$ be a machine that outputs the binary expansion of $T(|x|)$ within the stated bound. Write $H$ for the halting predicate. The proof builds machines for several elementary primitive-recursive operations: emitting a unary string of prescribed length, computing parity, and reading the first bit or its negation. It composes these machines with $M$ to obtain two machines that, on input $s$, can produce the unary output associated with $T(\operatorname{rank}(s))$ and then inspect its first bit (or its negation). The composition theorem `exists_comp_partial` ensures that the composed machine halts exactly when the successive computations halt; `codePrim_machine` supplies machines for the primitive-recursive operations, and `ntc_primrec_emit` supplies the unary-emission operation.

The rank identities `ntc_str_rank` and `ntc_bodd_T` identify the input used by $H$ at $\operatorname{rank}(s)$ with $s$, and show that the parity of $T(\operatorname{rank}(s))$ is the parity of $\operatorname{rank}(s)$ exclusive-or $H(s)$. Consequently its binary expansion begins with that parity. A conditional machine, chosen according to the parity of $\operatorname{rank}(s)$, tests this first bit when the rank parity is false and its negation when the rank parity is true. In either case, the conditional output answers exactly whether $H(s)$ holds. The primitive-recursive parity computation and `exists_cond` provide this conditional machine; `ntc_primrec_head` and `ntc_primrec_nhead` provide the two bit tests. Thus $H$ would be computable, contradicting `HALT_not_computable`.

**Key facts.** `Complexity.ntc_primrec_emit`, `Complexity.ntc_primrec_parity`, `Complexity.ntc_primrec_head`, `Complexity.ntc_primrec_nhead`, `Turing.codePrim_machine`, `Turing.FinTM.exists_comp_partial`, `Turing.FinTM.exists_cond`, `Complexity.ntc_bodd_T`, `Complexity.ntc_str_rank`, `Complexity.HALT_not_computable`.

**Caveat.** The proof uses primitive-recursive machine constructions and their composition/conditional semantics to turn the bit test into a decider for the halting predicate. The supplied statements support this route, but the omitted intermediate machine and output conventions require relying on those constructions' intended semantics.
