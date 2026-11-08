<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: Light.sumLists_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise sum of mapped lists

**Claim.** Starting from a zero list of length $|l|$ and successively adding the lists obtained by mapping $f(t,\cdot)$ over $l$ for each $t$ in $ts$ yields the list whose entry at $c$ is $\sum_{t\in ts}f(t,c)$.

**Proof.** Prove the corresponding fold identity by induction on $ts$, with an arbitrary initial list of the form $l$ mapped by a function $g$. For the empty list of parameters, the fold leaves that initial list unchanged, matching the entrywise expression with an empty sum. For a parameter list with head $t$, the fold first adds the list of values $f(t,c)$ coordinatewise, then performs the fold for the tail. Since both lists are mapped over the same $l$, their coordinatewise sum is the map of the pointwise sum. The induction hypothesis evaluates the tail fold, and associativity of addition identifies each resulting entry with $g(c)+\sum_{t\in ts}f(t,c)$. Finally take $g$ to be the constant-zero function. The initial zero list is exactly the map of that function over $l$, and adding zero leaves the claimed coordinate sums.
