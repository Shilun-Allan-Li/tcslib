<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: E_c_E_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Complementing a coordinate set twice returns it

**Claim.** For every `M : Finset (Fin n)`, `E_c (E_c M) = M`, where
`E_c E := Eᶜ` is the complement of a coordinate set inside `Fin n`.

**Proof.** Immediate from `simp [E_c]`: after unfolding `E_c` the goal is
`Mᶜᶜ = M`, which is the `Finset` involutivity of complement
(`compl_compl`, a `simp` lemma).

**Used in.** `cleaning_dimension_identity`, to rewrite `E_c (E_c M)` back to
`M` when `g_add_dims` is instantiated at the complement `E_c M`; this is what
makes the cleaning identity symmetric in `M` and `M^c`.
