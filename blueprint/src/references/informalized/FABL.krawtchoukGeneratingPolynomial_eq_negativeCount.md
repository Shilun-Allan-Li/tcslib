<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukGeneratingPolynomial_eq_negativeCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generating polynomial by negative coordinates

**Claim.** For a sign vector $x$, its generating polynomial factors as $(1-X)^z(1+X)^{n-z}$, where $z$ is the number of its negative coordinates.

**Proof.** Partition the coordinates into those where $x_i=-1$ and those where $x_i\ne-1$. The product defining the generating polynomial factors into the products over these two sets. On the first set, each factor $1+x_iX$ is $1-X$, so their product is $(1-X)^z$, with $z$ the number of negative coordinates. On the second set, each coordinate is a unit sign, hence is either $1$ or $-1$; since it is not $-1$, it must be $1$. Each factor there is $1+X$. The two sets partition the $n$ coordinates, so the second has size $n-z$, giving $(1+X)^{n-z}$. Multiplying the two products proves the identity.
