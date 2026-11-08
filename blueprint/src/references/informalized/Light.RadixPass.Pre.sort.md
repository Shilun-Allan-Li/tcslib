<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/RadixPass.lean :: Light.RadixPass.Pre.sort -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radix precondition yields counting-sort precondition

**Claim.** The radix-pass precondition implies that the associated counting-sort arguments satisfy all counting-sort preconditions, with the list entries as items and their radix keys as keys.

**Proof.** Unpack the radix-pass assumptions. Because $\pi$ has length $w$ and every entry is less than $w$, each item $\pi_j$ for $j<w$ is in range and is less than $w$. The segment assumption then says that source cell $\mathrm{perm}+j$ contains this item (`Light.SegN.read`). The key cell for that item is before $\mathrm{perm}$ by the key-before assumption applied to $\pi_j$; hence it lies within memory and outside both the destination interval, which begins at $\mathrm{perm}+w$, and the counter interval, which begins at $\mathrm{cnt}$. The key value stored there is $kd(\pi_j)$, and this is below $\mathrm{nb}$. The remaining bounds follow from $\mathrm{perm}+2w\le\mathrm{cnt}$, $\mathrm{cnt}+\mathrm{nb}+1\le\mathrm{perm}+R$, and $\mathrm{perm}+R\le\mathrm{space}$: they bound the source, destination, and counter regions and place those regions apart. Thus every counting-sort precondition holds for the associated arguments.

**Key facts.** `Light.SegN.read`.
