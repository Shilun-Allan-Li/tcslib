<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.validPair_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of valid paired words

**Claim.** A Boolean word is a valid paired encoding exactly when its initial run of ones has even length and is followed by $01$, and the suffix after those bits scans successfully as aligned pairs with a canonical remainder.

**Proof.** Suppose first that $y$ is valid, so it encodes a doubled unary word followed by a paired encoding of words $u,w$, with $u$ and $w$ canonical. The initial run has length $2n$ (`tRun_pairEncode`), and its next two bits are the separator $01$. Dropping that prefix leaves $\operatorname{dbl}(u)\,01\,w$, by the pair-encoding identity (`pairEncode_eq_dbl`) and the doubled-replicate identity (`dbl_replicate`). The scan characterization (`scanPairs_iff`) says this suffix scans to $w$ because the preceding-bit condition holds for canonical $u$ (`canon_iff`); hence the required scan and canonical remainder follow.

Conversely, suppose the bit-pattern and scan conditions hold. By `scanPairs_iff`, the suffix has the form $\operatorname{dbl}(u)\,01\,w$ for some $u$, and the scanner's preceding-bit condition implies that $u$ is canonical (`canon_iff`, with `none_orElse'` handling the initially absent previous bit). The prefix-decomposition lemma (`prefix_decomp`) reconstructs $y$ as the doubled unary prefix of length $tRun(y)$, followed by $01$ and the suffix. Since the prefix length is even, it equals twice $tRun(y)/2$. The encoding identities then express $y$ in the required paired form, with both inner components canonical.

**Key facts.** `Complexity.LogProg.tRun_pairEncode`, `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.scanPairs_iff`, `Complexity.LogProg.canon_iff`, `Complexity.LogProg.none_orElse'`, `Complexity.LogProg.prefix_decomp`.
