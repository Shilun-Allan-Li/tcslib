<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: NAndCircuit.ofVar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The single-variable AND-circuit

**Definition.** For `i : Fin n`, `NAndCircuit.ofVar i : NAndCircuit n` is the
one-literal clause `.clause [⟨i, true⟩] (List.nodup_singleton _)`: the positive
literal `xᵢ` (`sign = true`), packaged as a normal-form circuit. Its `Nodup`
obligation on `[i]` is discharged by `List.nodup_singleton`.

**Remark.** Unfolding `NAndCircuit.eval` gives `xᵢ && true`, so it computes the
projection `x ↦ x i`; `NOrCircuit.ofVar` is the literally identical
construction in the OR-rooted type.

**Note.** Convenience API only — neither `NAndCircuit.ofVar` nor
`NOrCircuit.ofVar` is used anywhere in the library, and no evaluation lemma is
proved for them.
