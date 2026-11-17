<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.pairEncode_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinates of a Pair Encoding

**Claim.** The defaulted bit at position $j$ of the pair encoding of $u$ and $v$ is the doubled bit of $u$ when $j<2|u|$, is the separator bit at either of the next two positions, and is the corresponding shifted bit of $v$ thereafter.

**Proof.** First suppose $j<2|u|$. The pair encoding can be written as the doubled string $u$ followed by the separator and then $v$ (`Turing.pairEncode_eq_dbl`), and the index lies within the doubled portion. Write $j$ as either $2\lfloor j/2\rfloor$ or $2\lfloor j/2\rfloor+1$. Since $j<2|u|$, the index $\lfloor j/2\rfloor$ lies within $u$. The doubled-string coordinate identity (`Turing.getElem?_dbl`) shows that either position contains $u_{\lfloor j/2\rfloor}$, giving the first case.

Now suppose $j\ge 2|u|$. The index is in the separator-and-suffix portion. At $j=2|u|$ the bit is the first separator bit, $0$; at $j=2|u|+1$ it is the second separator bit, $1$. For larger $j$, moving past the two separator bits leaves position $j-2|u|-2$ in $v$. The doubled-string length formula (`Turing.length_dbl`) locates the boundary, and the list indexing cases give the stated defaulted value, including when the shifted position is beyond the end of $v$.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Turing.getElem?_dbl`, `Turing.length_dbl`.
