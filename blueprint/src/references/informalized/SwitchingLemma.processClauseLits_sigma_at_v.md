<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_sigma_at_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The Updated Restriction at a Variable Depends Only on Its Starting Value

**Claim.** Consider the routine that processes one clause's free literals — a list of literals, each tagged with its position index — against a canonical decision-tree path, starting from a restriction $\rho_0$ and a restriction $\sigma$, and returning (among other data) an updated restriction $\sigma'$. Fix the literal list, the path, the restriction $\rho_0$, and a variable $v$. If two starting restrictions $\sigma_1$ and $\sigma_2$ satisfy $\sigma_1(v)=\sigma_2(v)$, then the updated restrictions they produce also agree at $v$. In other words, the value of $\sigma'$ at $v$ is a function of the single value $\sigma(v)$, with the literals, the path, and $\rho_0$ held fixed.

**Proof.** The whole argument rests on noticing *how* the routine ever touches the $\sigma$-component. Writing out the recursion, the routine consumes the literal list and the path in lockstep, and the updated restriction $\sigma'$ is built by the following rule:

- If the literal list is empty, it returns $\sigma' = \sigma$ unchanged.
- If the path is empty (but the literal list is not), it again returns $\sigma' = \sigma$ unchanged.
- Otherwise it peels off the leading literal $l$ (with its index) and the leading path step (with its recorded direction), and recurses on the tails, having first overwritten the single coordinate $l.\mathrm{var}$ of $\sigma$ with the value $\mathrm{some}(\lnot\, l.\mathrm{neg})$. The $\sigma'$ it returns is exactly the $\sigma'$ produced by that recursive call.

The point to extract is that the *only* modification ever made to $\sigma$ is an overwrite of one coordinate to the value $\mathrm{some}(\lnot\, l.\mathrm{neg})$ — a value determined entirely by the literal $l$, with no reference whatsoever to the incoming restriction. So two runs that start from $\sigma_1$ and $\sigma_2$ apply *identical* overwrites at *identical* moments; the only place their fate can differ at a coordinate is a coordinate that is never overwritten, where the output simply inherits the input. This is what makes agreement at $v$ propagate. We now make it precise by induction on the literal list, with the path, $\rho_0$, and both starting restrictions $\sigma_1,\sigma_2$ left general so that the inductive hypothesis can be re-applied to the modified restrictions.

1. **Base case — empty literal list.** Here $\sigma' = \sigma$ for both runs, so the claim is just the hypothesis $\sigma_1(v) = \sigma_2(v)$.

2. **Inductive step — the list is $l :: \text{rest}$.** Suppose the claim holds for the tail $\text{rest}$ (for every path, every $\rho_0$, and every pair of starting restrictions agreeing at $v$). Split on the path.

   a. **Empty path.** The routine returns $\sigma' = \sigma$ unchanged, so once more the conclusion is exactly the hypothesis $\sigma_1(v) = \sigma_2(v)$.

   b. **Nonempty path.** Both runs recurse on $\text{rest}$ and the path tail, from the same $\rho_0$-update, but starting now from the overwritten restrictions
   \[
   \sigma_1' = \sigma_1\big[\,l.\mathrm{var} \mapsto \mathrm{some}(\lnot\, l.\mathrm{neg})\,\big], \qquad
   \sigma_2' = \sigma_2\big[\,l.\mathrm{var} \mapsto \mathrm{some}(\lnot\, l.\mathrm{neg})\,\big].
   \]
   The returned $\sigma'$ of each run is the $\sigma'$ of its recursive call, so by the inductive hypothesis it suffices to check that $\sigma_1'$ and $\sigma_2'$ still agree at $v$. Evaluating a pointwise update at $v$ splits into two cases. If $v = l.\mathrm{var}$, then both $\sigma_1'(v)$ and $\sigma_2'(v)$ equal the overwritten value $\mathrm{some}(\lnot\, l.\mathrm{neg})$, so they are equal outright. If $v \neq l.\mathrm{var}$, the update leaves coordinate $v$ alone, so $\sigma_1'(v) = \sigma_1(v)$ and $\sigma_2'(v) = \sigma_2(v)$, which are equal by the hypothesis $\sigma_1(v) = \sigma_2(v)$. Either way the premise of the inductive hypothesis is met, and the conclusion follows.

This exhausts the cases, completing the induction. The mechanism throughout is the single observation of the opening paragraph: coordinate $v$ either gets overwritten with a value independent of the starting restriction — in which case the two runs match there trivially — or it is left untouched and carries forward the assumed equality $\sigma_1(v)=\sigma_2(v)$.
