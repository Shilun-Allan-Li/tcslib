<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_split_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting the Inner Product at a Coordinate

**Claim.** The Gowers inner product of a family indexed by the $(k+1)$-dimensional Boolean cube equals the average over $y$ of the product of the two half expectations formed by fixing coordinate $i$ to $0$ and to $1$.

**Proof.** Reindex the average over the $(k+1)$ direction vectors by separating the vector in coordinate $i$ from the other $k$ vectors. This is a bijective change of variables, and averaging over the resulting pair can be written as iterated averages (FABL.expect_prod_type). For fixed values of these vectors and of $x$, the product over all cube points factors according to whether coordinate $i$ is $0$ or $1$. The insertion product identity (FABL.gowersProduct_insertNth) expresses it as the zero-slice product at $x$ times the one-slice product at $x+h$, where $h$ is the separated direction vector. Exchange the order of the finite averages so that $y$ is averaged first. For each fixed $y$, averaging the product over $h$ and $x$ gives the product of the separate averages over $x$: translation by $h$ makes $x+h$ uniform independently of $x$. This is the averaging identity (FABL.expect_mul_add_eq_mul_expect), and those two separate averages are exactly the half expectations for the two fixed coordinate values.

**Key facts.** `FABL.expect_prod_type`, `FABL.gowersProduct_insertNth`, `FABL.expect_mul_add_eq_mul_expect`.
