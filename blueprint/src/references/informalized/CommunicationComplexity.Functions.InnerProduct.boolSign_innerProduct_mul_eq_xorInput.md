<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncInnerProduct.lean :: CommunicationComplexity.Functions.InnerProduct.boolSign_innerProduct_mul_eq_xorInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Multiplicativity under XOR

**Claim.** For all $n$-bit Boolean inputs $x,y,z$, the product of the signs of the mod-$2$ inner products of $x$ with $y$ and with $z$ equals the sign of the inner product of $x$ with the coordinatewise XOR of $y$ and $z$.

**Proof.** Expand each inner product as the Boolean sum of its coordinate contributions. The fact `boolSign_sum` expresses the sign of such a sum as the product of the signs of its summands. Thus the left side becomes a product over coordinates, with each coordinate contributing the product of the signs of $x_i\wedge y_i$ and $x_i\wedge z_i$. For each coordinate, checking the two possibilities for $x_i$ and the two possibilities for each of $y_i,z_i$ shows that this product is the sign of $x_i\wedge(y_i\oplus z_i)$. Multiplying these coordinate identities and applying `boolSign_sum` to the inner product with $y\oplus z$ gives the result.

**Key facts.** `CommunicationComplexity.boolSign_sum`.
