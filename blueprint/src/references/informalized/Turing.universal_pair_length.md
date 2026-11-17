<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_pair_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Pair Encoding

**Claim.** The paired encoding of $\alpha$ and $x$ has length $2|\alpha|+2+|x|$.

**Proof.** Induct on $\alpha$. For the empty string, the doubled prefix contributes no entries, the separator contributes two, and the suffix contributes $|x|$. For $\alpha=b::\alpha'$, doubling its first bit contributes two entries, while the remaining doubled prefix has length $2|\alpha'|$ by induction. Adding the separator and suffix gives $2+2|\alpha'|+2+|x|$, which is the stated formula since $|\alpha|=|\alpha'|+1$.
