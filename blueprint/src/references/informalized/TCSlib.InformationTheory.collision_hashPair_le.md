<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/LeftoverHash.lean :: TCSlib.InformationTheory.collision_hashPair_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision Bound for Hashed Pairs

**Claim.** For a universal function $f\colon S\to\alpha\to\beta$, with $S$ and $\beta$ finite and nonempty, hashing an independent uniform seed and input distributed as $X$ produces a pair distribution whose collision probability is at most $\frac1{|S|}\bigl(\operatorname{Coll}(X)+\frac1{|\beta|}\bigr)$.

**Proof.** Write $N=|S|$ and $M=|\beta|$, both positive, and let $c(x,x')$ count the seeds $s$ for which $f(s,x)=f(s,x')$. The probability of the output pair $(s,y)$ is $N^{-1}$ times the total $X$-mass of the fiber $\{x:f(s,x)=y\}$. Expanding the collision probability over $(s,y)$ therefore gives $N^{-2}$ times the sum, over seeds and outputs, of the squared fiber masses; this uses the formula for the probability of a hashed pair ( `TCSlib.InformationTheory.hashPair_apply` ). For each fixed seed, the sum of squared fiber masses can be rewritten as a sum over ordered input pairs: a pair $(x,x')$ contributes $X(x)X(x')$ exactly when their outputs agree. This is the fiber square identity ( `TCSlib.InformationTheory.sum_sq_fiber` ). Reordering the sums over seeds and input pairs then replaces the number of agreeing seeds by $c(x,x')$. On the diagonal, $c(x,x)=N$. Off the diagonal, universality gives $c(x,x')\le N/M$. Since all input probabilities are nonnegative, bounding each off-diagonal contribution this way and including the diagonal yields
\[
\sum_{x,x'}c(x,x')X(x)X(x')\le N\sum_x X(x)^2+\frac NM\Bigl(\sum_x X(x)\Bigr)^2.
\]
The total mass of $X$ is one, so the right side is $N\operatorname{Coll}(X)+N/M$. Multiplying by $N^{-2}$, which is nonnegative, gives $N^{-1}(\operatorname{Coll}(X)+M^{-1})$, as required.

**Key facts.** `TCSlib.InformationTheory.hashPair_apply`, `TCSlib.InformationTheory.sum_sq_fiber`.
