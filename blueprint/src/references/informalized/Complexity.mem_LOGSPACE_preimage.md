<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.mem_LOGSPACE_preimage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace Preimages

**Claim.** If a function has polynomially bounded output length and its output bits and length can be queried in logspace, then the preimage of every logspace language under that function is in logspace.

**Proof.** Let a logspace machine decide $C$, and let two logspace machines decide, respectively, whether a queried output position contains $1$ and whether it lies within the output length. The compiler theorem for logspace simulations (`Complexity.LogProg.OIS.compile_decides`) combines these machines: it simulates the decider for $C$ on $f(x)$, answering its input-symbol and end-of-input queries through the two index languages. The pairing lemma (`Complexity.pairEncode_mem_indexLang`) ensures that the encoded queries supply exactly the requested answers. Thus the compiled machine decides whether $f(x)\in C$.

It remains to bound the compiled machine's space. Write $n=|x|$, and choose a polynomial-logarithm bound $K$ so that both $\logSpace(|f(x)|)$ and the bit length $W$ of $|f(x)|+1$ are at most $K\logSpace(n)$. These bounds follow from the polynomial output-length hypothesis, the bit-length estimate (`Complexity.LogProg.length_bits_le_log`), and the polynomial logarithm bound (`Complexity.LogProg.log_poly_bound`). Each encoded query for an index at most $|f(x)|$ has length at most $2n+2+W$. Since `logSpace` is monotone (`Complexity.logSpace_mono`), a further polynomial-logarithm bound $J$ controls the space of both query machines on these inputs by $((c_l+c_b)J+1)\logSpace(n)$, where $c_l,c_b$ are their space constants. The simulation theorem accounts for these query workspaces and the simulated decider's workspace; combining the bounds gives a constant multiple of $\logSpace(n)$. This is precisely membership in $\mathsf{LOGSPACE}$.

**Key facts.** `Complexity.LogProg.OIS.compile_decides`, `Complexity.pairEncode_mem_indexLang`, `Complexity.LogProg.length_bits_le_log`, `Complexity.LogProg.log_poly_bound`, `Complexity.logSpace_mono`.
