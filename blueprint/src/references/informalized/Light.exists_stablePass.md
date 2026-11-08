<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/RadixPass.lean :: Light.exists_stablePass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable pass from a memory segment

**Claim.** Under the stated position hypothesis, there is a list of the same length as $\pi$ whose entries at the sorting positions are the corresponding entries of $\pi$, and whose integer entries describe the memory segment beginning at $dst$.

**Proof.** Take $\pi'$ to be the natural-number entries obtained by reading the length-$|\pi|$ memory segment beginning at $dst$ and converting each value to a natural number. Its length is therefore $|\pi|$. For any $j<|\pi|$, the sorting position is within that range by the bound on sorting positions (`Light.sortPos_lt`). The hypothesis identifies memory at that position with $\pi[j]$, so the corresponding entry of $\pi'$ is exactly $\pi[j]$. Finally, for any index $q<|\pi'|$, every position in the range occurs as a sorting position for some $j<|\pi|$ (`Light.exists_sortPos_eq`). Applying the hypothesis at that $j$ shows that memory at $dst+q$ is the corresponding entry of $\pi'$, which is precisely the required segment property.

**Key facts.** `Light.sortPos_lt`, `Light.exists_sortPos_eq`.
