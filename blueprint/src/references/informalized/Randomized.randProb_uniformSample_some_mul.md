<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.randProb_uniformSample_some_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepted Output Probability Relation

**Claim.** For $i<N$, the probability that the repeated sampling procedure returns $i$, multiplied by $N$, equals one minus the probability that it returns no value.

**Proof.** Set $m$ equal to the total number of random bits, and assign each input string the value $g$ equal to the procedure’s output when present, or $N$ when no output is present. Every value of $g$ lies in $0,\ldots,N$: a present output is less than $N$ (`lt_of_uniformSample_eq_some`), and the no-output case is assigned $N$. Partitioning according to these possible values gives the total-probability identity (`randProb_mem_eq_sum`). Since $g$ always lies in that range, the probability of belonging to it is $1$ (`randProb_true`). For each $j<N$, the event $g=j$ is exactly the event that the procedure returns $j$; moreover, the probabilities of returning any two values below $N$ are equal (`randProb_uniformSample_eq`). Thus the sum over the $N$ values below $N$ is $N$ times the probability of returning $i$. The remaining term, for $g=N$, is precisely the probability of no output. The partition identity now reads $1=N\,\Pr[\text{return }i]+\Pr[\text{no output}]$, which rearranges to the claimed relation.

**Key facts.** `Randomized.lt_of_uniformSample_eq_some`, `Randomized.randProb_mem_eq_sum`, `Randomized.randProb_true`, `Randomized.randProb_uniformSample_eq`, `Randomized.randProb_congr`.
