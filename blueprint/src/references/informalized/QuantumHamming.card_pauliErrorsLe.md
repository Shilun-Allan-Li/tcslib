<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: card_pauliErrorsLe -->
<!-- origin: quant-ph.9608006 run 4fa1f624d1c5 verdict not_in_text (0.62) -->

# Counting Pauli errors of weight at most t

**Claim.** The number of $n$-qubit Pauli strings of weight at most $t$ is

```
|E(n,t)| = ∑_{j=0}^{t} C(n,j) · 3^j.
```

**Proof.** Partition and count.

1. *Partition by weight, then by exact support.* `PauliErrorsLe n t` is the
   disjoint union over `j ∈ range (t+1)` and over supports
   `S ∈ powersetCard j univ` of the sets `pauliStringsExactSupport S`
   (`h_union`; membership is `Nat.lt_succ_iff` on the weight bound).
2. *Count one cell.* A string with support exactly `S` assigns one of the
   three non-identity Paulis to each coordinate of `S`: the assignment map
   `mkWithSupport` is a bijection onto the cell, so the cell has `3^{|S|}`
   elements (`card_pauliStringsExactSupport`, via `support_mkWithSupport`
   and injectivity of `mkWithSupport`).
3. *Count the cells.* For each `j` there are `C(n,j)` supports of size `j`
   (`Finset.card_powersetCard` on `univ`), each contributing `3^j`.
4. *Disjointness.* Cells with different supports are disjoint (a string
   determines its support), and weight classes are disjoint
   (`Finset.card_biUnion` twice). Summing gives the identity. ∎

**Used in.** `error_sphere_dimension` and thence `quantum_hamming_bound` /
`quantum_hamming_bound_raw`
(blueprint: `ErrorCorrectingCodes/QuantumHamming.tex`): this is the
volume-of-ball count in the sphere-packing argument. The source paper
(Calderbank–Rains–Shor–Sloane, quant-ph/9608006) uses
$\sum_j \binom{n}{j} 3^j$ only as the left-hand side of the sphere-packing
bound attributed to Gottesman, citing it as a black box; the counting
identity itself is stated nowhere in the text. Ekert–Macchiavello
(PRL 77, 2585) and Knill–Laflamme (PRA 55, 900) likewise use the count
implicitly.
