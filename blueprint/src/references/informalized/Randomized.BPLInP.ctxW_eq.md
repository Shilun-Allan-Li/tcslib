<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.ctxW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Configuration Contexts

**Claim.** The context encoding of $x$ with parameters $c,B,e$ equals the context encoding using radius $c(|\operatorname{bits}(|x|)|+1)$ and code-iteration bound $B(|x|+1)^e$.

**Proof.** Expand the context encoding and replace its code-iteration word by the concatenation of the binary codes from $0$ to $B(|x|+1)^e-1$, as given by `Randomized.BPLInP.codesW_eq`. Expanding the radius encoding gives the binary expansion of $c(|\operatorname{bits}(|x|)|+1)$. These are exactly the radius and code-list components of the stated context encoding, while the input component $x$ is unchanged.

**Key facts.** `Randomized.BPLInP.codesW_eq`.
