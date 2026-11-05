<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.triplesToAux_markLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Round-trip of a marked block through the aux list

**Claim.** Let $w \in \mathbb{N}$ and let $b$ be a nonempty list of pairs in $\mathrm{Fin}\,w \times \mathrm{Bool}$. Mark the last entry of $b$ — set the marker flag to $\mathrm{true}$ on the final pair and $\mathrm{false}$ on every earlier pair — and then convert the resulting list of triples back into an aux list. The result equals the list obtained from $b$ by casting each pair $(i,d)$ to the entry $(i,d) \in \mathbb{N} \times \mathrm{Bool}$, with a single termination marker $(w,\mathrm{false})$ appended at the end.

**Proof.** The two operations are defined by recursion on the list, so we read off their effect and confirm that the single termination marker ends up at the tail.

Recall what marking does: on a one-element list $[(i,d)]$ it returns $[(i,d,\mathrm{true})]$, and on a longer list $(i,d)::\mathit{rest}$ it returns $(i,d,\mathrm{false}) :: \bigl(\text{mark of }\mathit{rest}\bigr)$. So every pair acquires a flag, $\mathrm{true}$ on exactly the last pair and $\mathrm{false}$ on all the others. The aux conversion then casts each triple $(i,d,\cdot)$ to the entry $(i,d) \in \mathbb{N} \times \mathrm{Bool}$, and *additionally* splices in a termination marker $(w,\mathrm{false})$ immediately after any triple whose flag is $\mathrm{true}$. Since marking produces exactly one $\mathrm{true}$ flag — on the final entry — the conversion inserts exactly one marker, and it lands right after the last pair, i.e. at the end. That is the claim; the induction below makes it precise.

We induct on $b$.

1. **Empty list.** Excluded by hypothesis: $b$ is nonempty, contradicting $b = [\,]$.

2. **Singleton**, $b = [(p,d)]$. Marking gives $[(p,d,\mathrm{true})]$. Feeding this to the conversion hits the $\mathrm{true}$-branch once and then the empty list, producing $(p,d) :: (w,\mathrm{false}) :: [\,] = [(p,d),(w,\mathrm{false})]$. The right-hand side casts $[(p,d)]$ and appends $(w,\mathrm{false})$, giving the same list. So the base case holds.

3. **Two or more entries**, $b = (p,d) :: \mathit{rest}$ with $\mathit{rest} = h_2 :: \mathit{rest}_2$ nonempty. Here the first marking clause applies: marking $b$ equals $(p,d,\mathrm{false}) :: \bigl(\text{mark of }\mathit{rest}\bigr)$, because the head is not the last entry and so receives flag $\mathrm{false}$. Running the conversion on this list takes the $\mathrm{false}$-branch on the head, emitting $(p,d)$ with no marker and recursing on the tail:
\[
\mathrm{triplesToAux}\,w\,(\text{mark of }b) = (p,d) :: \mathrm{triplesToAux}\,w\,(\text{mark of }\mathit{rest}).
\]
Now $\mathit{rest}$ is nonempty, so the induction hypothesis applies to it, rewriting the tail as $\mathit{rest}.\mathrm{map}(q \mapsto (q.1.\mathrm{val}, q.2)) \mathbin{+\!\!+} [(w,\mathrm{false})]$. Substituting,
\[
\mathrm{triplesToAux}\,w\,(\text{mark of }b) = (p,d) :: \Bigl(\mathit{rest}.\mathrm{map}(\cdots) \mathbin{+\!\!+} [(w,\mathrm{false})]\Bigr).
\]
The right-hand side of the goal is $b.\mathrm{map}(\cdots) \mathbin{+\!\!+} [(w,\mathrm{false})]$, and since $b = (p,d) :: \mathit{rest}$ the map distributes over the cons to give $(p,d) :: \bigl(\mathit{rest}.\mathrm{map}(\cdots)\bigr)$. Because consing commutes with appending at the tail, the two expressions coincide. This closes the inductive step.

The only ancillary fact is that $\mathit{rest} = h_2 :: \mathit{rest}_2$ is nonempty, which is what licenses the appeal to the induction hypothesis.
