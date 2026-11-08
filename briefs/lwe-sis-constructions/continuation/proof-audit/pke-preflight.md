# Quantitative Regev PKE preflight

This planning document records the next support obligations. It adds no Lean
statement/proof, changes no owner API and does not start a new implementation
phase while the construction-core proof audit is pending. Source: visually
checked Wu24 Lecture 21, PDF page 86 / printed page 83; the exact source hashes
and review scope are in `source-page-review.json`.

## Reuse the row-oriented LWE public key

Keep `A` as an `m`-by-`n` matrix, `b = A s + e`, and public key `(A,b)`.
For a fresh uniform binary vector `r` of length `m`, the one-bit ciphertext is

\[
\left(A^{\mathsf T}r,\ \langle b,r\rangle+mu\lfloor q/2\rfloor\right).
\]

The residual after subtracting the secret product is

\[
\langle b,r\rangle-\langle s,A^{\mathsf T}r\rangle
=\langle e,r\rangle,
\qquad
|\langle e,r\rangle|\le mB.
\]

Thus the existing proved decoder supplies every-coin correctness from
`2*(m*B) < floor(q/2)`. The non-strict quarter bound in the notes is not copied;
the boundary examples in the source-comparison record explain why. Use the
actual bounded finite-seed noise and one full uniform secret, as in the current
LWE experiment. No lattice trapdoor is involved.

## Binary linear universality over composite moduli

In the uniform-public-key hybrid, augment the transpose of `A` by row `b` to
obtain an `(n+1)`-by-`m` matrix `C`. The ciphertext before message translation
is `C r`. Reuse the existing binary matrix hash construction rather than
define an equivalent competing hash. Its universality theorem can live in a
new owned child beside `Hashing/SIS/Basic`; the theorem uses no SIS hardness
or norm premise, and the PKE consumer must introduce no `SISAssumption`.

For distinct binary inputs `r,r'`, select a differing coordinate `j`. The
corresponding difference is `+1` or `-1`, which is invertible modulo every
`q >= 2`. Fixing every column other than `j`, each target vector has exactly
one choice of column `j` solving

\[
C_j(r_j-r'_j)=u-\sum_{i\ne j}C_i(r_i-r'_i).
\]

Therefore `C(r-r')` is uniform and the collision probability is exactly
`1/q^(n+1)`. This gives the collision universality consumed by the existing
leftover hash lemma. No primality premise is needed. Do not substitute the
field-only `isUniversal_affine`, or assert pairwise independence: the linear
hash of the zero vector is always zero. The empty input dimension makes
distinct inputs impossible; the proof should handle that case explicitly.

The future Lean obligations are the column-splitting equivalence/count,
uniform translation/sign equations, and the `IsUniversal` conclusion. They
are not claimed proved in Lean here. The small shared reading-lemma proposal
must be coordinated before this consumer reads `IsUniversal` by its body.

## Use an explicit leftover-hash error budget

`InformationTheory.leftover_hash` already gives the strong, seed-published
bound. Uniform binary `r` has min-entropy `m`, and the output has `n+1`
residue coordinates. The desired specialization is

\[
\operatorname{SD}((C,Cr),(C,U))
\le \frac12\sqrt{q^{n+1}/2^m}.
\]

If `q <= 2^W` and

\[
m\ge(n+1)W+2\kappa,
\]

then

\[
q^{n+1}/2^m
\le 2^{(n+1)W-m}
\le 2^{-2\kappa},
\qquad
\frac12\sqrt{q^{n+1}/2^m}\le\frac12\,2^{-\kappa}.
\]

Here exponent subtraction and division in the error calculation are real
arithmetic, with natural parameters cast to the reals; the integer sample
budget is an explicit sufficient condition. The future formal statement must
include its natural/real cast lemmas rather than treat this calculation as a
Lean proof. This keeps the extra output coordinate and security slack visible.
The notes' `3*n*log q` shorthand is not the final parameter contract.

Apply `Foundations.Experiments.distAdv_le_statDist` to the joint public-key/hash
experiment, with message translation and the distinguisher as postprocessing.
This route does not require a new shared statistical-distance data-processing
API. The ordinary triangle argument yields two real-to-uniform DLWE advantages
plus twice the displayed statistical error for two fixed plaintext bits.
Efficient preprocessing and the machine-valued CPA bridge remain separate.

The next statement gate should cover universality, uniform-source entropy,
the strong extraction specialization, the exact two-hybrid security bound and
the subset-sum algorithms/correctness. Machine/sampler implementation and the
existing primitive owner's message/game quantifiers must be accounted for at
their consumer gate. No LWE/search/SIS/lattice reduction is needed.

Notation: `n` is secret dimension; `m` is the LWE row count; `q` is the modulus;
`A,s,e,b` are the existing matrix, secret, integer errors and noisy values;
`r,r'` are binary subset vectors, cast to residues for multiplication; `μ` is
the plaintext bit; `B` bounds each error; `C` is the augmented matrix; `j` is
a differing coordinate; `u,U` are a fixed target and an independent uniform
output; `W` bounds residue width; `κ` is the security parameter; `SD` is the
repository's statistical distance.
