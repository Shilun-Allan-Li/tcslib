<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: Light.AbsLe.getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on an In-Range List Entry

**Claim.** If every entry of an integer list $l$ has absolute value at most $U$, then the entry at any index $i<\operatorname{length}(l)$ also has absolute value at most $U$.

**Proof.** For $i<\operatorname{length}(l)$, the entry at position $i$ is an element of $l$. The assumed bound applies to every element of the list, and therefore applies to this entry.
