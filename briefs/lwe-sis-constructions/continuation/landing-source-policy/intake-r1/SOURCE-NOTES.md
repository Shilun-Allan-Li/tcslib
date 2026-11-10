# Source ambiguities preserved as printed

These are source-level issues or source/formalization differences, not silently corrected transcription. They remain unresolved for source-policy review. The repaired text is a transcription proposal, not an endorsement of the source proofs.

## pdf-c0f87bf2e871-p065-b001

- SOURCE AS PRINTED: commitment uses g^S, while the following exponents use s; capitalization is not silently repaired.

- SOURCE AS PRINTED: the input tuple is (x,x_2,x_3), although the next sentence uses x_1. The table and circuit labels are preserved.

## pdf-c0f87bf2e871-p075-b001

- SOURCE AS PRINTED: Definitions 18.1 and 18.3 write x in Z_q^m, while the lattice paragraph uses integer x in Z^m. No canonical integer lift is supplied. Do not use this as an identical match for the integer SIS relation.

## pdf-c0f87bf2e871-p082-b001

- SOURCE AS PRINTED: Definition 20.1 uses SamplePre(td,x) on the right where y has just been sampled; this apparent argument slip is preserved.

- SOURCE AS PRINTED: Corollary 20.3 samples y in Z_q^m, whereas the preceding theorem has y in Z_q^n; no dimension repair is made.

## pdf-c0f87bf2e871-p083-b001

- SOURCE AS PRINTED: the opening prose says LWE reduces to GapSVP, then says LWE is as hard as GapSVP. The reduction-direction wording is not repaired or used for matching this stack.

- SOURCE AS PRINTED: chi=D_{Z,s} is combined with Pr[|x|<beta]=1. A nondegenerate exact discrete Gaussian is not bounded on its entire support. No such law or worst-case reduction is imported.

- SOURCE AS PRINTED: the informal SIS-to-LWE adversary argument leaves shortness and the distribution of u^T z unquantified; it is not a hardness bridge for the formal independent assumptions.

- SOURCE/FORMAL DIFFERENCE: nearest-codepoint decoding with ties false is not a silent replacement for the printed rounding notation. The bound |e|<q/4 alone does not establish correctness of the formal decoder at every odd modulus; see rounding-boundaries.json.

## pdf-c0f87bf2e871-p085-b001

- SOURCE AS PRINTED: the correctness paragraph writes ct=(c_1,c_0), despite the preceding decryption tuple (c_0,c_1); the coordinate slip is preserved.

- SOURCE LIMITATION: Definition 21.2 displays a single-sample problem. Its CPA-security prose does not specify the common-secret polynomial batch, uniform message bounds, machine reductions or the quantitative two-hybrid inequality.

- SOURCE AS PRINTED: {q-1,q}={-1,0} in the final paragraph is read modulo q; no extra error-budget theorem is inferred.

## pdf-c0f87bf2e871-p091-b001

- SOURCE AS PRINTED: the final hash signature is sigma_{H(m),g}, with m not introduced on this page. It is not rewritten to another variable.

- SOURCE AS PRINTED: succinctness is written poly(lambda . |y|). The printed punctuation is retained, without choosing a different arity convention.
