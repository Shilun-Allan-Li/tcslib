# PHFE function-key length bound candidate

Exact live frozen header/opening prose and sketch preserved. One outer tactic block;
no new public helper, definition, import, admission, counting theorem, or efficiency
hypothesis. No Lean/lake/Git command or live source edit was run. Native validation
remains pending.

The local hLen is the exact numeric word identity obtained from existing keyWord_eq,
Wire.quadraticKey_eq/linearKey_eq, whole-matrix groupMatrix_length, pair lengths and
the List.ofFn length of the ORIGINAL function word. phfeClass_fnLen aligns that exact
original bit width with tensorFnLen; it does not decode/re-encode or identify aliases.
Quadratic.piDim_eq and PolyExpr equation readers give the fixed metadata dimensions.
Ring normalization yields
  2*fnLen + (8*n^3+6*n^2+(6*l+8)*mCount(actual decoded function))*wG + 10.

Only the existing PG.mCount_le_mBound changes that actual-function quantity to the
uniform bound. Ordered multiplication/addition then give exactly skLen_eval. The
proof adds no positivity restriction and includes zero input dimensions. No row/point
flatten count is repeated: whole-block lengths come from the now-proved Wire API.

## auxCount_add_one is not needed by the CURRENT encoded key

Current Linear.Key.K1 is a THREE-by-OUTPUT matrix Fin 3 x Fin(nprime.eval kappa),
not the auxiliary T-row draw space. Wire.linearKey encodes K1/K2/K3/R, with only
K2/K3/R using PG.MIdx via mCoord. Hence its exact length contains mCount and NO
auxCount. PG.auxCount_add_one remains relevant to full KeyDraw serialization but
using it here would add an irrelevant premise/calculation. Root was notified of this
current-interface fact before drafting. The coefficient 6*n^2 in hLen comes from K1.

Rule 10: every simp entry is a published wire, length, class-width, or polynomial
equation reader; no public definition body is supplied. The only dimension bound
is the supplied raw garbling's field law, not an efficiency target. There is no group
exponent extraction. Local hLen is specialized arithmetic for this frozen target,
not a new generic encoding lemma.

Static source/reuse readings: current PHFE.Encodings.keyWord_length_le/keyWord_eq;
Wire.quadraticKey_eq/linearKey_eq; Linear.Key fields; PHFE/Widths.skLen_eval;
PartialGarbling.Raw.mCount_le_mBound/auxCount_add_one; phfeClass_fnLen;
WireLemmas.groupMatrix_length; Quadratic.piDim_eq; length_pairEncode.
No mathematical obstruction found. No standard-axiom-only claim is made before
root native checking and the remaining encoding proof obligations are complete.
