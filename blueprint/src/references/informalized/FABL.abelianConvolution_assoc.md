<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianConvolution_assoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Associativity of Normalized Convolution

**Claim.** For functions $f,g,h:G\to\mathbb C$ on a finite abelian group, normalized convolution is associative: $(f*g)*h=f*(g*h)$.

**Proof.** Fix $x\in G$ and express each convolution as a uniform expectation using `FABL.abelianConvolution_apply`. Expanding the nested expectations and pulling factors independent of the averaging variable outside their expectations gives the left side as the average over $z$ of $f(z)$ times the average over $y$ of $g(y-z)h(x-y)$. Interchanging the two finite averages, it remains to identify the inner average with the corresponding one on the right. For fixed $z$, reindex by the bijection $w=y-z$; then $y=z+w$ and $x-y=x-z-w$. The summand becomes $f(z)g(w)h(x-z-w)$, exactly the iterated-average expression for $f*(g*h)$ at $x$. Since this holds at every $x$, the two functions agree.

**Key facts.** `FABL.abelianConvolution_apply`.
