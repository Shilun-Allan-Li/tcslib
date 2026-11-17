<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.splice_vertices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splicing a Computation Segment

**Claim.** If the configurations at prefix times $a$ and $b$ have the same core data and output summary, deleting the choices between those times preserves the final core data and output summary. Every prefix of the shortened word also has the same core data and output summary as some prefix of the original word, of length at most $|w|$.

**Proof.** Write $c_j$ for the configuration reached after the first $j$ choices of $w$. The splice replaces $w$ by the word consisting of its first $a$ choices followed by the choices after its first $b$ choices. Since $c_a$ and $c_b$ have the same core data and output summary, running any common continuation from them preserves that equality (`coreSum_runWith`). In particular, continuing with the suffix after time $b$ shows that the spliced run ends with the same core data and output summary as the original run. The identification of a run on concatenated words with successive runs (`runWith_append`) expresses these continuations as the corresponding concatenated runs.

Now take a prefix of the shortened word, of length $j$. If $j\le a$, it is just the prefix of $w$ of length $j$, so choose that original prefix. If $j>a$, the prefix contains the first $a$ choices and then the first $j-a$ choices of the suffix after time $b$. It therefore corresponds to the original prefix of length $b+(j-a)$. The bounds $a\le b\le |w|$ and the fact that $j$ is at most the shortened word's length ensure this length is at most $|w|$. The equality of core data and output summaries for these two prefixes follows by first advancing from time $a$ along the retained suffix segment, using that $c_a$ and $c_b$ agree and that a common continuation preserves `coreSum`, and then using the run concatenation law to identify the resulting runs. Thus every shortened prefix has the required representative among the original prefixes.

**Key facts.** `Turing.NDTM.coreSum_runWith`, `Turing.NDTM.runWith_append`.
