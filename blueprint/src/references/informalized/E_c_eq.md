<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: E_c_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Complement as a set difference from `univ`

**Claim.** For every `E : Finset (Fin n)`, `E_c E = Finset.univ \ E`. That is,
the complement notation `E_c E := Eᶜ` used throughout the file agrees with the
set difference of `E` from the full coordinate set.

**Proof.** Immediate: `ext` reduces to membership of an arbitrary `i`, and
`simp [E_c]` closes it, since `i ∈ Eᶜ ↔ i ∉ E ↔ i ∈ univ \ E` on a `Fintype`.

**Remark.** A bookkeeping bridge, needed because the kernel computation
`ker_r_E` is stated with `Finset.univ \ E` while the cleaning-lemma layer is
stated with `E_c`. As written it is **unused** — the one place that needs the
bridge (`dim_map_r_E`) discharges it by `convert ker_r_E E` rather than by
rewriting with this lemma.
