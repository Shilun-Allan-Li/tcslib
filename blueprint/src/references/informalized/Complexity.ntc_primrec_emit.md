<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_primrec_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursive Unary Output

**Claim.** The function sending each finite bit string $s$ to the list of $$rank$(s)$ copies of $1$ is primitive recursive.

**Proof.** The rank function is primitive recursive by `ntc_primrec_rank`. The list-range operation preserves primitive recursiveness when applied to a primitive-recursive natural-valued function, so $s\mapsto\operatorname{List.range}(\operatorname{rank}(s))$ is primitive recursive. Mapping the constant value $1$ over a list is also primitive recursive. Composing these operations gives the list containing exactly $\operatorname{rank}(s)$ copies of $1$.

**Key facts.** `Complexity.ntc_primrec_rank`.
