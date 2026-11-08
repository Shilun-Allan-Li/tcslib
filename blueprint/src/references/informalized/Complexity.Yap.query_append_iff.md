<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.query_append_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query on an Appended Input

**Claim.** The query for $D_N$ on $z$ followed by $w$ holds exactly when $w$ is the ordered bit string of some assignment $y$ to the additional $m(|z|)$ inputs and $D_{|z|}$ accepts the combined assignment.

**Proof.** Replace $N$ by $|z|$ using the hypothesis on $z$. By the query characterization (`Complexity.Yap.query_encode_iff`), the query holds precisely when there is an assignment $x$ to all $|z|+m(|z|)$ inputs whose ordered bit string is $z\mathbin{++}w$ and on which $D_{|z|}$ accepts. Split the coordinates of $x$ into its first $|z|$ entries and its remaining $m(|z|)$ entries. The corresponding list of values is the concatenation of the two coordinate lists. Since that concatenation equals $z\mathbin{++}w$, equality of list concatenations identifies the first list with $z$ and the second with $w$. The first assignment is therefore the one given by $z$, while the second gives an assignment $y$ with $w=\operatorname{ofFn}(y)$; acceptance becomes acceptance on the appended assignment. Conversely, given such a $y$, concatenate the assignment read from $z$ with $y$. Its ordered bit string is $z\mathbin{++}w$, and the assumed acceptance supplies the query characterization, proving the query.

**Key facts.** `Complexity.Yap.query_encode_iff`.
