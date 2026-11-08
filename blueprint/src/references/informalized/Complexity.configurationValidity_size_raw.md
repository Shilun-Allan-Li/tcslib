<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationValidity_size_raw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw Configuration Encoding Length

**Claim.** Under the stated lower bound on $C$, the serialized configuration-validity CNF has length at most $\bigl(B(s+n+2)^2+2C(s+n+1)\bigr)\bigl(C(s+n+1)+3\bigr)+1$.

**Proof.** The serialization bound for a CNF says its length is at most its clause-and-literal cost times the largest wire index bound plus three, with one final delimiter (`codecCnf_serialize`). The variable-index result supplies the required wire bound, and relabeling by the identity does not change the formula. To bound the cost, split the formula into its relabeled validity constraints and padding clauses. Cost is additive across concatenation and invariant under relabeling (`codecCnfCost_append`, `codecCnfCost_relabel`). The core validity cost is at most $B(s+n+2)^2$ (`codecValidity_cost`), while the padding cost is at most twice the total padded length, hence at most $2C(s+n+1)$ (`codecPadding_cost`). Combining these estimates bounds the total cost by their sum. Substitution into the serialization bound yields the claimed expression.

**Key facts.** `Complexity.configurationValidity_literals`, `Complexity.codecCnf_serialize`, `Complexity.codecCnfCost_append`, `Complexity.codecCnfCost_relabel`, `Complexity.codecValidity_cost`, `Complexity.codecPadding_cost`.
