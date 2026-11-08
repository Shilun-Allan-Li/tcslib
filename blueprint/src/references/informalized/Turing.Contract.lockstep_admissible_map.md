<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.lockstep_admissible_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Admissibility Under State Mapping

**Claim.** If the encoded configuration’s optional state is obtained by applying $\rho$ to the source state, then a source entry configuration satisfying $C$’s precondition maps to state $\rho(e)$ and satisfies the corresponding lockstep contract’s precondition.

**Proof.** Apply the lockstep admissibility theorem (`Turing.Contract.lockstep_admissible`) with entry state $\rho(e)$. Its required entry-state correspondence follows from the assumed state-mapping identity: the source state is $\operatorname{some}(e)$, so its image under the optional-state map is $\operatorname{some}(\rho(e))$. The theorem then gives both that the encoded configuration has this entry state and that it satisfies the lockstep contract’s precondition.

**Key facts.** `Turing.Contract.lockstep_admissible`.
