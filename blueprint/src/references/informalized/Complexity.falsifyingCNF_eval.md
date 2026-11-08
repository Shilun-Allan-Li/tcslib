<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.falsifyingCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Evaluation

**Claim.** The truth-table CNF of a Boolean function evaluates under an assignment to the value of that function on the assignment's first $\ell$ bits.

**Proof.** First characterize when the whole CNF evaluates to false. Since a CNF is a conjunction of its clauses, it is false exactly when some clause is false. Such a clause comes from a vector $v$ with $f(v)=\mathrm{false}$. By the characterization of when the clause excluding $v$ is false (`Complexity.falsifyingClause_eval_false`), that clause is false exactly when the assignment's first $\ell$ bits equal $v$. Thus, if the CNF is false, those bits equal a vector on which $f$ is false, so $f$ of those bits is false. Conversely, if $f$ of those bits is false, the vector of those bits is among the vectors used to form the CNF, and its excluding clause is false under the assignment; hence the CNF is false. We have proved that the CNF and $f$ of those bits have the same falsity condition. As both are Boolean values, they are equal.

**Key facts.** `Complexity.falsifyingClause_eval_false`.
