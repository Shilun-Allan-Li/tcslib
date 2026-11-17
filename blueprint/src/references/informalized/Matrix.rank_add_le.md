<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean :: Matrix.rank_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subadditivity of matrix rank

**Claim.** For real matrices $A,B$ with rows indexed by $X$ and columns indexed by a finite set $Y$, the rank of their sum is at most the sum of their ranks.

**Proof.** View each matrix as the linear map from column vectors indexed by $Y$ to vectors indexed by $X$ given by matrix multiplication. The image of the map associated to $A+B$ is the sum of the images of the maps associated to $A$ and $B$: each output $(A+B)v=Av+Bv$ lies in that sum, and each vector $Av+Bw$ in the sum is the image of $(v,w)$ under the map $(v,w)\mapsto Av+Bw$, whose image is precisely the sum of the two images. In particular, the image of $A+B$ is contained in the sum of the individual images. The dimension of a contained subspace is at most that of the containing space, and the dimension of a sum of two finite-dimensional subspaces is at most the sum of their dimensions. Since rank is the dimension of the image, these facts give $\operatorname{rank}(A+B)\leq\operatorname{rank}(A)+\operatorname{rank}(B)$.
