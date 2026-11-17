<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialExtremizer_centralLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extremizer Sign on a Central Layer

**Claim.** When $k\le n$ and $j\le k$, the extremizer on the canonical input with $gotsmanLinialStart(n,k)+j$ positive coordinates equals $1$ if $k-j$ is even and $-1$ otherwise.

**Proof.** First, $gotsmanLinialStart(n,k)+k\le n$, so the canonical input at the specified count has exactly $gotsmanLinialStart(n,k)+j$ positive coordinates: the general counting formula gives the minimum of this count and $n$, and the count is at most $n$. The product formula for the cube polynomial and the identity expressing the sum of signs as twice the positive-coordinate count minus $n$ then reduce its factors to $2j-2t-1$ for $0\le t<k$. Reindexing this product using $k=j+(k-j)$ shows that its threshold sign is the sign of the central product with parameters $j$ and $k-j$. The central-product sign formula ($\texttt{thresholdSign_centralProduct}$) says this sign is $1$ when $k-j$ is even and $-1$ when it is odd.

**Key facts.** `FABL.positiveCoordinateCount_canonicalCountInput`, `FABL.gotsmanLinialCubePolynomial_eq_product`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.thresholdSign_centralProduct`.
