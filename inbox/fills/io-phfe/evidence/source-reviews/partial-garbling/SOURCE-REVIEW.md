# Partial-garbling source review

All five supplied source PDFs were SHA-256 checked before this review; every hash
matches the dispatch. Exact printed hash lines are in `sources-sha256.txt`.
The PDFs were read in place under
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/sources/`.
No PDF was copied. Scratch text and rendered relevant pages are here.
No Lean, lake, build command, public-source edit, or Git mutation was performed.

## Verified sources and locations

- [AGW20] Michel Abdalla, Junqing Gong, Hoeteck Wee, *Functional Encryption
  for Attribute-Weighted Sums from k-Lin* (supplied 39-page PDF).
- [IW14] Yuval Ishai, Hoeteck Wee, *Partial Garbling Schemes and Their
  Applications* (supplied 20-page PDF).
- Both PDFs' printed page numbers equal physical PDF page numbers at every
  location reviewed here.

| Location | Verified content | Formalization consequence |
|---|---|---|
| AGW20 §4.1, p.11 | Setup takes security/function parameters; encryption reveals public attributes; key includes public function; the scalar answer is a weighted sum. | Context for the one-slot specialization, not a replacement for GJLS21 syntax. |
| AGW20 §4.1, pp.11–12 | Universal randomized simulator; the stateful efficient adversary sees mpk, chooses challenge attribute/value pairs, receives ct, then queries KeyGen adaptively. KeyGen* receives the queried function and evaluated weighted sum. | Supports the semi-adaptive game and N=1 specialization. |
| AGW20 Remark 1, p.11 | Scalar-output decryption is relaxed to bounded values and brute-force discrete log. | Do not claim its scalar-output functionality verbatim; this job works in the exponent. |
| AGW20 §4.2, Lemma 2, p.12 | Four efficient algorithms; reconstruction for every coin; statistical privacy; pgb=(z−last(t),tᵀ(L1(x⊗I)+L0)); pgb* substitutes −last(t) and adds μe1 in the second block. | Interface syntax and law clauses. |
| AGW20 §4.2, p.12 | L0/L1 dimensions are printed swapped in both surrounding text and the lemma. | Record W1 as an explicit inherited misprint reading. |
| AGW20 §4.2, p.12, Extension | Adding δ at the distinguished coordinate changes the reconstructed value by δ and changes only that allowed leak. | A useful stronger reader, if later needed, follows because rec(m0)=1. Not required to import the extended FE. |
| AGW20 Appendix A, p.37, Lemma 12 and (28)–(30) | Garbling and its simulator are the last-column randomization of the same matrix; reconstruction is linear in the garbling. | Identifies the concrete instance being specialized; determinant proof route is not used here. |
| AGW20 Appendix A, p.38, (31) | Reorders garbling into n′ output coordinates first and m non-output coordinates second, with an explicit transpose. | Use output type Fin n′ ⊕ MIdx. |
| AGW20 Appendix A, p.38, (32) | L1 is n blocks each of shape (m+n′−1)×m; L0 is the constant part of the same (m+n′−1)×m matrix. | Correct dimensions: L1 : t×(ℓm), L0 : t×m. |
| AGW20 Appendix A, p.38, Algorithm rec | The reconstruction vector's distinguished second-block coordinate is 1. | Choose m0=root and forward value(root)=empty product=1. |
| AGW20 Appendix B, pp.38–39 | Concrete extended/unbounded-slot FE; its KeyGen prints L1/L0 with the corrected dimensions. Its final Dec explicitly computes scalar output by brute-force discrete log. | Corroborates dimensions; no Appendix-B scheme or discrete-log step should be implemented for this job. |
| IW14 Definition 1, p.6 | Reconstruction succeeds with probability 1; simulator and garbling have identical distributions. | Exact privacy is justified, rather than merely statistical closeness. |
| IW14 Definition 1 continuation, p.7 | Infinite families require an efficient algorithm producing descriptions of the garbling, reconstruction and simulator. | Efficiency belongs in the interface/targets; it must not be omitted. |
| IW14 Theorem 3, p.8 | When private inputs appear only on edges into the last t vertices: output length t(|V|−1), input degree one, randomness degree one for t=1 (degree two generally), reconstruction degree t. | Our instance uses t=1; no locality transformation is needed. |
| IW14 §4.2, pp.9–11 | Randomizes the last t matrix columns; the privacy argument gives identical distributions through group translations/canonical form. | The path-sum/translation proof supplies the same specialized law with no determinant or ABP datatype. |

## Terminology and disclosed readings

1. AGW20 p.12's swapped L0/L1 dimensions must not be copied. Both its own (32)
   and its Appendix-B KeyGen confirm the corrected shapes. This is precisely
   the inherited W1 reading required by the dispatch.
2. IW14 uses “affine” in Definition 1 for a stronger LOCAL syntax: each output
   uses one input coordinate. Our matrix formula is degree-one/general affine
   in x,z at fixed coins. Cite IW14 Theorem 3, not Corollary 1, for this syntax;
   do not claim the additional single-coordinate property without its locality
   transformation.
3. The randomness dimension t_rng=m+n′−1 is DIFFERENT from IW14 Theorem 3's
   parameter t_tail, which is 1 here. Keep these names distinct in prose.
4. The layered tensor specialization, forward/backward path-sum proof, exact
   translation, finite Sum-index reordering, and zero-dimension extensions are
   derived formalization choices. The papers do not explicitly state the
   d=0/n′=0 edge cases below; do not attribute those edge-case statements as
   quotations or separately numbered paper results.
5. References [29], [30], [43] in AGW20 and [25], [26] in IW14 were read only
   as references within these supplied papers. No external source is claimed
   to have been read.

## Complete relevant-page visual inspection

Rendered at 130 dpi, read as complete PNG pages (not crops):
AGW20 pp.11,12,37,38,39 and IW14 pp.6,7,8,9,10,11.
This includes all headings, diagrams, equation labels, the p.12 extension,
the p.38 Appendix-B transition, and the p.39 discrete-log output line.
All relevant mathematical text and page numbers are legible.

See `LAYERED-FORMULAS.md` for exact derived formulas, edge cases and proposed
Lean module boundaries. Public source remains unchanged.
