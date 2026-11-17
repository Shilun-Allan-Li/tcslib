<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.joinFields_recordTemplate_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Joined Record Template

**Claim.** Joining the two fields of the record template gives a list of length $w(n)+2s+2$.

**Proof.** The template has two fields: the binary-digit field has length $w(n)$ by the definition of its width, and the work-cell field has length $2s+1$ because it is indexed by the range from $0$ to $2s$. The joined-fields length formula (`joinFields_length`) adds the two field lengths and one separator, giving $w(n)+(2s+1)+1=w(n)+2s+2$.

**Key facts.** `Turing.joinFields_length`.
