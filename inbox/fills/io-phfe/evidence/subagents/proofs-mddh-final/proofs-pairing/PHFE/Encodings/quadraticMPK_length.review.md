# PHFE public-key word length candidate

Exact live frozen header and opening prose/sketch preserved. One tactic block, no new
helper/runtime definition, no efficiency hypothesis, no admission. No Lean/lake/Git
command or live source edit was run. This candidate remains for root native validation.

The proof reads the EXISTING Wire.quadraticMPK_eq and linearMPK_eq equations, applies
the EXISTING length_pairEncode framing formula, and consumes the now-native-PASS
Wire.groupMatrix_length for every whole matrix. There is no row/point enumeration,
flatten length sum, List.length_ofFn proof, or copy of matrix-encoding counting.
The frozen sketch mentions row lengths; the stronger shared adapter supplies that
mathematics whole. No sketch text is changed by this draft.

Quadratic.piDim_eq and the PolyExpr eval_add/mul/const readers give the internal
private dimension 2*n+n*2. Ring normalization then matches mpkLen_eval's exact
(16+24*n+8*l)*wG+10, including nested pair overhead. All dimensions may be zero.

Rule 10: every named simp entry is a published equation/length theorem. No public
definition body is supplied to simp/rw/unfold. No codec/description alias changes occur.
If not yet reachable, root must add the existing owned Wee20.WireLemmas import to
PHFE.Encodings when integrating; this adds no Mathlib root and creates no cycle.
This scratch task changes no live imports.

Static search/read evidence: original PHFE.Encodings target; PHFE/Widths.mpkLen_eval;
Wire quadraticMPK_eq/linearMPK_eq; live WireLemmas.groupMatrix_length;
Quadratic.lean:59 piDim_eq; TuringMachine/Encoding.lean:220 length_pairEncode
(2*left.length+2+right.length). No complete existing PHFE public-key length theorem
was found beyond this frozen admission. No new helper target/probe is needed.
No mathematical obstruction found.
