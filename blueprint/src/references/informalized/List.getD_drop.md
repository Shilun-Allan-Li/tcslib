<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Default Lookup After Dropping a Prefix

**Claim.** For a list $l$, natural numbers $a,j$, and default $d$, lookup at position $j$ in the list obtained by dropping the first $a$ entries equals lookup at position $a+j$ in $l$, with default $d$.

**Proof.** Express default lookup as optional indexed lookup followed by replacement of a missing value by $d$. The indexed lookup of the list after dropping $a$ entries at position $j$ is the original list's optional lookup at position $a+j$. Applying the same default replacement to these equal optional values yields the result.
