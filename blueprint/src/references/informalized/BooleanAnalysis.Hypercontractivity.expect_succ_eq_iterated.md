<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: BooleanAnalysis.Hypercontractivity.expect_succ_eq_iterated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Iterated expectation over the last bit of the cube

**Claim.** Let $n \in \mathbb{N}$ and let $h : \{0,1\}^{n+1} \to \mathbb{R}$ be a Boolean function on $n+1$ bits. Writing $(x', b)$ for the point of $\{0,1\}^{n+1}$ obtained by appending the bit $b \in \{0,1\}$ to $x' \in \{0,1\}^n$ as its last coordinate, the uniform expectation of $h$ factors as an average over the last bit followed by an average over the remaining $n$ bits: $\mathbb{E}[h] = \mathbb{E}_{x' \in \{0,1\}^n}\!\left[\tfrac12\bigl(h(x',0) + h(x',1)\bigr)\right]$.

**Proof.** Both sides are, by definition, a normalising weight times a finite sum, so the proof is the bookkeeping that reconciles the two. Recall that the uniform expectation on the $m$-cube is $\mathbb{E}[f] = w_m \sum_{x \in \{0,1\}^m} f(x)$, where $w_m = (1/2)^m$ is the uniform weight.

1. **Expand the left-hand side.** Unfolding the definition of expectation on the $(n+1)$-cube gives
\[
  \mathbb{E}[h] \;=\; w_{n+1} \sum_{x \in \{0,1\}^{n+1}} h(x).
\]

2. **Split the sum by the last coordinate.** Every point of $\{0,1\}^{n+1}$ is uniquely $(x', b)$ for some $x' \in \{0,1\}^n$ and some bit $b$, so the sum over the $(n+1)$-cube splits into the two sums obtained by fixing the final bit. This is the fact that summing a function $\varphi$ over $\{0,1\}^{n+1}$ equals $\sum_{x'} \varphi(x',0) + \sum_{x'} \varphi(x',1)$ (`sum_boolCube_succ`), where $(x', b)$ denotes appending $b$ to $x'$ as its last coordinate. Applying it to $\varphi = h$ yields
\[
  \mathbb{E}[h] \;=\; w_{n+1}\!\left(\sum_{x' \in \{0,1\}^n} h(x',0) \;+\; \sum_{x' \in \{0,1\}^n} h(x',1)\right).
\]

3. **Peel off one factor of $\tfrac12$ from the weight.** The uniform weights of consecutive cubes satisfy $w_{n+1} = w_n/2$ (`uniformWeight_succ`), since $(1/2)^{n+1} = (1/2)^n \cdot \tfrac12$. Substituting and using that scalar multiplication distributes over the sum, each summand picks up the factor $\tfrac12$:
\[
  \mathbb{E}[h] \;=\; w_n \sum_{x' \in \{0,1\}^n} \tfrac12\bigl(h(x',0) + h(x',1)\bigr).
\]

4. **Recognise the right-hand side.** The displayed expression is precisely $w_n$ times the sum over the $n$-cube of the function $x' \mapsto \tfrac12\bigl(h(x',0)+h(x',1)\bigr)$, which is by definition the uniform expectation of that function over $\{0,1\}^n$. Hence
\[
  \mathbb{E}[h] \;=\; \mathbb{E}_{x' \in \{0,1\}^n}\!\left[\tfrac12\bigl(h(x',0) + h(x',1)\bigr)\right],
\]
as claimed. The remaining reassociation of the arithmetic (collecting the $\tfrac12$ and the weight, rearranging products and sums) is routine algebra carried out mechanically.

**Key facts.** `BooleanAnalysis.Hypercontractivity.sum_boolCube_succ`, `BooleanAnalysis.Hypercontractivity.uniformWeight_succ`.
