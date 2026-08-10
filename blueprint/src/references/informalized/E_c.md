<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: E_c -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `E_c E`: the complement of an erasure set

**Definition.** For `E : Finset (Fin n)`, `E_c E := Eᶜ` — the `Finset`
complement of `E` inside `Fin n`, i.e. the coordinates *not* in `E`. A plain
one-line abbreviation with no mathematical content of its own; it exists so
that the complement of an erasure set has a stable name in the cleaning
arguments.

Its interface is supplied by three companion lemmas:

- `E_c_eq` : `E_c E = Finset.univ \ E` (`ext` + `simp [E_c]`), which is the form
  `ker_r_E` states the kernel of the restriction map in.
- `E_c_E_c` : `E_c (E_c E) = E` — complementation is an involution
  (`simp [E_c]`).
- `card_add_compl` : `M.card + (E_c M).card = n` (`Finset.card_compl`).

**Used in.** `dim_map_r_E`, `g_expansion`, `g_formula`,
`dim_S_M_add_dim_S_M_c_le_dim_S`, `cleaning_dimension_identity` and
`g_complement_correctable` — everywhere the code is split into a set and its
complement.
