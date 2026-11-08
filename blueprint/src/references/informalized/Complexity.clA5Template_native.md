<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Template_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Serialization of a Wired Formula

**Claim.** If each unary word of length $wire(x,j)$ is polynomial-time computable, then relabeling a fixed CNF formula by $wire(x,\cdot)$ and serializing its clauses with leading markers is polynomial-time computable.

**Proof.** First consider one literal with variable index $j$ and sign bit $b$. Its serialization is the unary word of length $wire(x,j)+1$, followed by the fixed delimiter and sign bits. The assumed computation for the unary word, together with polynomial-time concatenation with fixed words (`clNative_append` and `clA5_pt_const`), gives a polynomial-time computation of this literal serialization. For a fixed clause, induct on its list of literals: the empty clause serializes to a fixed delimiter, and a nonempty clause is the concatenation of the first literal's serialization and the serialization of the remaining literals. Concatenation preserves polynomial-time computability. Finally, induct on the fixed CNF formula. The empty formula serializes to the empty word; each additional clause contributes its fixed leading marker followed by the clause serialization, concatenated with the serialization of the remaining formula. The same closure under concatenation proves the result.

**Key facts.** `Complexity.clA5_pt_const`, `Complexity.clNative_append`.
