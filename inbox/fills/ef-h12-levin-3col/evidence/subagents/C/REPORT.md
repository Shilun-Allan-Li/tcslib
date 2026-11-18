# Sub-agent C report: EF-H12 step 4 (colouring witness)

File (owned, new, 431 lines): TCSlib/Cryptography/ZeroKnowledge/LevinHardness/ColoringWitness.lean
Imports: LevinHardness.Gadget, ZeroKnowledge.Encoding, SecureComputation.ComposeSecurity.Machines
(all in order-prefix2; EncodingMachines comes transitively).

## Public declarations
- `gadgetNodeColor a b c i : Fin 3`: colours of the 6 gadget nodes (re-derived course table
  `clauseGadgetColor`). Reader `gadgetNodeColor_eq`.
- `gadgetColor K val t : Fin 3`: palette t gets t; literal 3+l gets (litVal val l ? 1 : 2); gadget node
  3+2K+6c+i gets gadgetNodeColor of the clause's three litVals at i. Reader `gadgetColor_eq`;
  case lemmas `gadgetColor_val_of_lt_three`, `gadgetColor_of_lit`, `gadgetColor_of_gadget`.
- `properColoring_gadgetColor K mem val`: (forall c, mem c = true -> clauseSat K val c = true) ->
  ProperColoring (gadgetGraph K mem) (fun u => gadgetColor K val u).
- `threeColorable_gadgetGraph K mem val`: same hypothesis -> ThreeColorable (gadgetGraph K mem).
- `colorWord s a := encColoring (fun u : Fin (gadgetN s.length) =>
  gadgetColor s.length (fun v => a.getD v false) u)`. Reader `colorWord_eq`.
- `polyTimeComputable_colorWord : PolyTimeComputable fun z => colorWord (pairFstD z) (pairSndD z)`
  (via ComposeMachines.polyTimeComputable_flatMap_range over t < gadgetN |s|, 2-bit chunks).

Private glue: gadgetNodeColor_ne_internal, litColor_ne_gadgetNodeColor (both by `decide` over
Bool^3), gadgetColor_ne_of_edge (six edge families of gadgetEdge_eq), colorBits,
flatMap_colorBits (flatMap of 2-bit chunks = encColoring), unaryDivConst_poly, unaryModConst_poly,
litVal_poly, clauseLit_poly, gadgetNodeColorBits_poly, gadgetColorBits_poly.
Candidates for promotion if another file (e.g. the graph-word machine) needs them: litVal_poly,
clauseLit_poly, unaryDiv/ModConst_poly.

## Foreign readers used
- gadgetN_eq, clauseLit_eq, litVal_eq, clauseSat_eq, gadgetEdge_eq, gadgetAdj_eq, gadgetGraph_apply
  -- LevinHardness/Gadget.lean
- ProperColoring_iff (:90), threeColorable_iff (:107) -- ZeroKnowledge/ThreeColoring/Language.lean
- getD_encColoring_two_mul, getD_encColoring_two_mul_add_one, length_encColoring
  -- ZeroKnowledge/Encoding.lean (~:280-312)
- divNum_eq (:631), modNum_eq (:650), divNum_poly (:657), modNum_poly (:678), unaryAdd_poly (:85),
  unaryMul_poly (:94), unarySub_poly (:106), unaryConst_poly (:115), unaryLength_poly (:121),
  ltTest_poly (:146), eqTest_poly (:154), getBit_poly (:178) -- ZeroKnowledge/EncodingMachines.lean
- ComposeMachines.polyTimeComputable_flatMap_range -- SecureComputation/ComposeSecurity/Machines.lean:81
- polyTimeComputable_ite/and (ClassNP/PolyTimePairing.lean:290,320), polyTimeComputable_not
  (ClassNP/PolyTimeBlockLoop.lean:175), polyTimeComputable_const, pairFstD/pairSndD rows,
  PolyTimeComputable.congr (Randomized/Closure.lean:101).

## MISSING readers
None needed.

## Overlaps / near-relatives
- (b) disclosed: gadgetColor/gadgetNodeColor re-derive private sat3Coloring/clauseGadgetColor of
  Complexity/NPReductions/ThreeSATToColoring.lean:163-182; properColoring_gadgetColor re-derives
  SATtoColor.SATtoColorCompleteness (:193). Said in module and declaration docstrings. That file is
  not imported.
- FormulaKit/Emit.lean:216-271 polyTimeComputable_unary_sub/mul/le/div/mod are still `sorry`; NOT
  used. I used the proved EncodingMachines rows instead (unarySub_poly, unaryMul_poly,
  divNum_poly, modNum_poly). unaryDivConst_poly/unaryModConst_poly specialize divNum_poly/modNum_poly
  (EncodingMachines.lean:657,678) to a constant divisor, composed with the readers.
- ThreeColoring/Machines.lean:159 ColMachines.polyTimeComputable_flatMap_range duplicates the host;
  I used ComposeMachines' as the brief says.
- EncodingMachines.polyTimeComputable_of_getD (:403) would be an alternative host; not used.
- No existing "encColoring as flatMap" lemma found (grep), so flatMap_colorBits is new (private).

## Checks
- Last compile (lean_slot.sh, ol-C): exit 0, no error/warning lines.
- Rule-10 seal test: a scratch copy with `attribute [local irreducible]` on gadgetN clauseLit litVal
  clauseSat gadgetEdge gadgetAdj gadgetGraph ProperColoring ThreeColorable encColoring divNum modNum
  pairFstD pairSndD PolyTimeComputable compiled cleanly (`Graph` is an abbrev and cannot be sealed).
  Scratch deleted.
- grep: no sorry/admit/native_decide/axiom/@[simp]; all lines <= 100 chars.

## Unfinished
Nothing.
