<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.FiniteUniqueGame.fullySatisfied_propagatedLabel_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of Propagated Labels

**Claim.** The labeling obtained by transporting chosen component root labels along the chosen paths satisfies every constraint if and only if each chosen root label satisfies the compatibility condition for every constraint whose source lies in that component.

**Proof.** Assume first that the propagated labeling satisfies every constraint. Fix a component and an edge whose source lies in it. The source and target of the edge lie in the same component (`FABL.FiniteUniqueGame.component_source_eq_target`), so both propagated labels use that component’s chosen root label. Substituting the definition of the propagated labeling into the edge’s satisfaction equation gives exactly the component’s root-label compatibility condition. Conversely, assume that condition holds in every component. For any edge, apply it in the component of the source. The source and target components agree by `FABL.FiniteUniqueGame.component_source_eq_target`; consequently, the resulting compatibility equation is precisely the satisfaction equation for the propagated labeling on that edge. Thus every constraint is satisfied.

**Key facts.** `FABL.FiniteUniqueGame.component_source_eq_target`.
