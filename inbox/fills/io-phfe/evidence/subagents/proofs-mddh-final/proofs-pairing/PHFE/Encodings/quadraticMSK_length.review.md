# PHFE master-secret word length candidate

Exact live frozen header/opening prose and sketch preserved. One tactic block, no new
helper/import/runtime definition, admission, or efficiency premise. No Lean/lake/Git
command or live source edit was run. Root native validation remains pending.

Wire.quadraticMSK_eq exposes the retained PUBLIC group-matrix metadata and linear
secret word. Wire.linearMSK_eq exposes the three existing modular matrix encodings.
The now-proved Wire.groupMatrix_length and EXISTING Modular.encodeMatrix_length
supply each whole-block length. The public modulus already has its existing NeZero
instance; no extra width-fit or injectivity hypothesis is needed just for length.
There is no List.length_flatten, row count, point count, or modular count reproof.

length_pairEncode supplies framing lengths. Quadratic.piDim_eq and the published
PolyExpr eval_add/mul/const readers normalize the internal private dimension to 4*n
and the metadata output dimension to n*n. Ring normalization matches exactly
(8*n^3+24*n+12*l+6)*wG+6 from mskLen_eval, including pair framing. All zero dimensions
remain included. WireDraws scalarMatrix_eq is not needed: this wire reader already
uses the public Modular.encodeMatrix directly.

Rule 10: all supplied simp entries are published equations or shared length theorems,
never public definition bodies. No group exponent/scalar recovery or word alias
normalization occurs. The proof consumes existing encodings and their lengths whole.

Static exact APIs read: original quadraticMSK_length target; Wire quadraticMSK_eq/
linearMSK_eq; live WireLemmas.groupMatrix_length; Modular.lean:89 encodeMatrix_length;
PHFE/Widths.lean:59 mskLen_eval; Quadratic.lean:59 piDim_eq; Turing length_pairEncode.
The existing owned WireLemmas proof module must be reachable at integration as for the
MPK proof; no new Mathlib root is needed. No new helper target/probe is proposed.
No mathematical obstruction found.
