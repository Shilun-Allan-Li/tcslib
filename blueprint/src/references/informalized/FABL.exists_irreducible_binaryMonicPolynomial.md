<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.exists_irreducible_binaryMonicPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Irreducible binary polynomial of prescribed degree

**Claim.** For every positive integer $\ell$, there is a monic irreducible polynomial of degree $\ell$ over $\mathbb{F}_2$, hence one of the stated form.

**Proof.** Let $K$ be the binary extension field of degree $\ell$. Choose a primitive element $\alpha$ of $K$ over $\mathbb{F}_2$. Since $K$ is finite, $\alpha$ is integral over $\mathbb{F}_2$, so its minimal polynomial $p$ is monic and irreducible. The primitive-element criterion says that the degree of $p$ equals the field extension degree; the latter is $\ell$ by the dimension formula for the binary extension field (`binaryExtensionField_finrank`). Now take the coefficient vector $m$ whose $i$th entry is the coefficient of $X^i$ in $p$, for $0\le i<\ell$. A monic polynomial of degree $\ell$ is $X^\ell$ plus its lower-degree terms, so the polynomial encoded by $m$ is exactly $p$ and is irreducible.

**Key facts.** `FABL.binaryExtensionField_finrank`.
