<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.sum_mul_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factoring constants from a sum

**Claim.** Let $\alpha$ be a finite type, let $a,b\in\mathbb R$, and let $f,g:\alpha\to\mathbb R$. Then $\sum_{x:\alpha}(a f(x))(b g(x))=ab\sum_{x:\alpha}f(x)g(x)$.

**Proof.** For each index $x$, commutativity and associativity of real multiplication give $(a f(x))(b g(x))=(ab)(f(x)g(x))$. Summing these terms factors the constant $ab$ out of the finite sum, yielding the stated identity.
