<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryMonicIrreducibleTest_eq_true_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Monic Irreducibility Test

**Claim.** For every positive integer $\ell$ and coefficient vector $m\in\mathbb{F}_2^\ell$, the binary monic irreducibility test returns true exactly when the associated monic polynomial is irreducible over $\mathbb{F}_2$.

**Proof.** Write $p$ for the polynomial associated with $m$. Its monicity and natural degree are $\ell$ (`binaryMonicPolynomial_monic`, `binaryMonicPolynomial_natDegree`), so positivity of $\ell$ implies that $p$ is not a unit. The test detects whether there are two low polynomials, each different from $1$, whose product is $p`; the equivalence between this witness and the Boolean factor search is `binaryHasProperFactor_eq_true_iff`.

Suppose first that the test returns true. Then no such pair of low polynomials exists. To prove irreducibility, consider any factorization $p=ab$. If both factors are nonunits, they are nonzero and have positive natural degree, since each divides the monic polynomial $p$. Their degrees add to $\ell$, so each degree is less than $\ell$. Encode each factor by its coefficients in degrees below $\ell$; `binaryLowPolynomial_coefficients` says these vectors recover the factors exactly. Neither factor can equal $1$, because over $\mathbb{F}_2$ a polynomial is a unit exactly when it equals $1$ (`isUnit_f₂Polynomial_iff_eq_one`). This would give the forbidden pair, a contradiction. Thus every factorization has a unit factor, and, together with the fact that $p$ is not a unit, this proves irreducibility.

Conversely, suppose $p$ is irreducible. A pair of low polynomials different from $1$ cannot multiply to $p$: irreducibility forces one factor to be a unit, and over $\mathbb{F}_2$ that factor must equal $1$. Hence no proper-factor witness exists. The Boolean search therefore returns false, so its negation—the irreducibility test—returns true.

**Key facts.** `FABL.binaryMonicPolynomial_monic`, `FABL.binaryMonicPolynomial_natDegree`, `FABL.binaryHasProperFactor_eq_true_iff`, `FABL.isUnit_f₂Polynomial_iff_eq_one`, `FABL.binaryLowPolynomial_coefficients`.
