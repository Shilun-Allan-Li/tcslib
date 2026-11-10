# Peikert–Waters passages used by the trapdoor proofs

The author-hosted PDF is dated June 4, 2010 and has 44 pages. The full file is
557,098 bytes with SHA-256
`74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c`.
The page labels and physical page numbers agree on the extracted pages 33–39.
The per-page text fingerprints in `pw10-primary-source.json` use Poppler
`pdftotext -layout` 26.10.0. [Author PDF](https://web.eecs.umich.edu/~cpeikert/pubs/lossy_tdf.pdf)

| Consumed passage | Lean scope | Adaptation |
|---|---|---|
| §6.2, pages 33–34, concealer and Lemma 6.2 | `Lossy.Matrix` and `Lossy.Experiments` | Keep one public matrix, one independent secret and noise vector per column, and a single common-secret challenge in each adjacent hybrid. The Lean statement bounds the finite advantage by the sum of the column advantages and handles each fixed key shift explicitly. |
| §6.3.2, pages 35–36, gadget, encoding, evaluation, and inversion | `Lossy.Gadget` and `Lossy.Matrix` | Transpose row-vector evaluation into matrix-vector notation. Set the large modulus to an exact dyadic multiple of the message modulus, so the encoding is additive and nearest-scale decoding has a direct signed integer proof. The secret is the retained ordinary matrix. |
| §6.3.2, pages 36–37, Theorem 6.4 and its proof | `Lossy.Matrix` | Use a deterministic entrywise error bound. The lossy image factors through the first modular product and the bounded signed error vector. The conditional cardinality bound counts that integer interval directly. |
| §6.4, pages 37–39, anti-cyclic matrix and Theorem 6.5 | `AllButOne.AntiCyclic` and `AllButOne.Basic` | Use the same signed wrap on the branch coefficients. Exact divisibility removes the encoding-rounding discrepancy. The designated shifts cancel and the larger message modulus preserves bounded signed branch products. The anti-cyclic rank and other-branch inversion obligations remain open. |

The table identifies the passages to validate and match. Ingestion and approved
matching remain pending. The cited constructions use conditional bounds and
finite laws. Parameter instantiation and the asymptotic primitive bridges
remain separate.
