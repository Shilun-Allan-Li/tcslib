# Fixed-width BoolCircuit list glue — plan and candidates, NOT RUN

Read-only preparation. No source edit, Lean/lake/build/cache, git mutation,
new import or agent spawn. Exact source binding is in source-binding.json.
The two candidate lemmas are specialized to CONSTANT block width and use only
the existing BoolCircuit.encodeList_nil/cons readers plus public Core list
lemmas. The term application supplies the remaining uniform-row injection
step in the earlier LPNAdvice candidate, once these helpers are actually proved.

Proposed host: LPN.lean, area-local Internal namespace, before its existing
encoding proofs. It already directly imports CircuitComplexity.Uniform.
Encoding imports Params, which imports LPN; Reductions.LPN also sees it
through Hybrids. Therefore these theorem-only helpers add no import or new
source file. They define no new algorithm, prefix-free predicate, encoding,
sampler, equivalence, attribute or notation.

## Proposed specialized interfaces

1. Internal.encodeList_injective_of_fixedWidth:
   for f:alpha->List Bool, Function.Injective f and
   (forall a, length(f a)=width) imply
   Function.Injective (BoolCircuit.encodeList f).
2. Internal.encodeList_length_of_fixedWidth:
   (forall a, length(f a)=width) implies
   length(encodeList f xs)=length(xs)*(width+1)+1.

No Fintype, DecidableEq, nonempty-domain or positive-width assumption is
needed. In particular width=0 is valid: injection of f then forces its domain
to be subsingleton, while the list's true markers still determine its length.
The final false marker contributes1 even for an empty list.

The candidate fragments each contain one tactic block and are at most96
columns. Neither has been elaborated. Root must run exact?/apply? on each new
helper's statement before landing it, then compile and run canonical seals.
Do not claim these candidate strings as checked proofs. References/docstrings
may be expanded to fit the final source attribution policy before insertion.

## Proofs using exact public readers

Injection proceeds by induction on the FIRST input list, generalizing the
second. Nil/cons cannot match because their first markers are false/true.
For cons/cons, the public encodeList_cons reader gives equality

  true :: (f a ++ code xs) = true :: (f b ++ code ys).

Use List.cons.inj to cancel the marker. Equal widths give
length(f a)=length(f b), and the EXISTING List.append_inj splits equality
into f a=f b and code xs=code ys. Apply the supplied block injection and
induction. No generic prefix-free theorem or decoder is recreated.

Length proceeds by induction on xs. The nil reader gives[false], of length1.
The cons reader and List.length_cons/length_append contribute1+width plus
the tail formula. Normalize the successor product with Nat.succ_mul; omega
only rearranges natural arithmetic. This is an EXACT fixed-width formula,
not a new variable-block-size upper-bound theorem.

## Public alternatives searched and disposition

Whole TCSlib theorem/name searches covered encodeList/injective/length/
prefixFree/flatMap/decode combinations. Core, Batteries and Mathlib List
searches covered append_inj, flatten/flatMap injection, length_flatten and
length_flatMap. No public BoolCircuit tagged-list fixed-width injection or
exact fixed-width closed length formula was found. No tactic search ran.

| Existing public result | Status/reason |
|---|---|
| BoolCircuit.encodeList_nil/cons, Uniform.lean:96/100 | Adopted. Exact owner readers, already imported. |
| List.append_inj, Lean Init/Data/List/Lemmas.lean:1612 | Adopted. Supplies ALL head/remainder cancellation; no reproof. |
| List.length_cons/length_append and Nat.succ_mul | Adopted for exact specialized length arithmetic. |
| BoolCircuit.encodeList_eq_flatMap, UniformTableauEmitter.lean:256 | Correct generic identity, but emitter is NOT in the current reduction closure. Import would add19 TCSlib+1 Mathlib modules, including tableau/program/circuit machinery; rejected just for this identity. The new lemmas do NOT recreate that list equality. |
| List.length_flatMap:2046 and length_flatten:1869 (Core List/Lemmas) | Correct generic lengths, but need an explicit flatten/flatMap representation first. No advantage over two existing nil/cons readers; not needed. |
| BoolCircuit.AdjWalk.length_encodeList_le', LogspaceUniformAdj.lean:181 | Public generic bound, unavailable in current closure. Not imported, not re-proved as a generic theorem. Our exact CONSTANT-width equality is a genuinely different specialized result. |
| BoolCircuit.AdjScan.length_encodeList_cons, LogspaceUniformScan.lean:309 | Public one-step length identity in a heavier module. The proposed proof uses the owner's encodeList_cons reader and Core length lemmas directly; no new one-step helper is stated. |
| BoolCircuit.decodeList_encodeList, DAGCircuitSatLang.lean:120 | Correct decoding theorem but needs a supplied element decoder with suffix preservation and fuel. Not in current closure, would introduce unnecessary decoder machinery for the fixed-width use cases. |
| LamportReduction.encodeList_injective/ofFn_eq_iff | DIFFERENT encoding: nested pairs with empty-list code[], not this true/false tagged concatenation. Cannot be applied. |
| PrivateKeyScheme encodeList_eq_flatMap and other cryptographic tuple-code lemmas | Also a different nested-pair code. Not adopted. |
| Encoding.Modular.encodeMatrix_injective | Bare flattened fixed-width rows, with NO true markers/final false bit. It does not directly prove injection of the actual tagged advice code. Use encodeVector_injective for each recovered row instead. |

Emitter's existing exact identity was inspected in place. It says
encodeList f xs = xs.flatMap(fun a=>true::f a) ++[false]. The emitter's direct
imports are Mathlib.Tactic.FinCases, UniformTableauSpec and Uniform. Its
transitive expansion relative to the inspected LPN closure is saved in
emitter-added-modules.txt, with both closure snapshots. No heavy module is
recommended or imported by this preparation.

## Private overlap — explicitly disclosed

CircuitComplexity/Uniform.lean contains:

- private PrefixFree, line87;
- private encodeList_prefixFree, line158, proving prefix-free element codes
  give a prefix-free list code;
- private length_encodeList_le, line234, proving an upper bound when each
  element code has length<=B.

Our injection is a fixed-width SPECIAL CASE of the consequences of that
private prefix-free infrastructure. Our exact length equality implies its
private upper bound in the constant-width case. These overlaps are disclosed;
private declarations cannot be reused as public Rule10 APIs, and no private
name is accessed through its generated _private name. The candidates do not
copy either generic proof, predicate or statement. They use the existing
public encodeList readers and List.append_inj with a stronger fixed-width
hypothesis, giving the narrow result required by these particular layouts.

## Concrete use map and exact widths

| Owner/use | Element encoder and constant width | Block injection source |
|---|---|---|
| Encoding.encBuckets | b -> natToList(B) b.val, width B | numeral round trip plus b.val<B<=2^B, Fin.ext |
| Encoding.encOneDraw noise list | selector/residue pair code, width2*ell+kappa+5 | pairEncode_injective; selector and residue numeral round trips, existing W width and prime width |
| Encoding.encDraw repetition list | encOneDraw, width OneLen=2*ell*(kappa+1)+n*(2*ell+kappa+6)+3 | existing encOneDraw_injective plus its exact length equality |
| LPNAdvice.uniform row list | encodeVector(kappa+1), width n*(kappa+1) | existing encodeVector_injective with pp.le_two_pow |
| Raw LPN.encDraw noise list | VARIABLE width due Nat.bits(selector); NOT covered | separate self-delimiting/prefix-free path required; see below |

For finite function vectors, apply list-code injection to the encoded
List.ofFn values, then List.ofFn_injective. No additional ofFn wrapper theorem
is required. Candidate03 is the exact term for LPNAdvice.uniform, using the
actual PrimeParam field name le_two_pow. This remains valid at n=0 or kappa=0.

The exact length helper gives:

- bucket code m*(B+1)+1;
- noise list n*(2*ell+kappa+6)+1;
- full Draw 2*n+3+kappa*(OneLen+1), after the outer pair reader;
- uniform-row list kappa*(n*(kappa+1)+1)+1.

These are the exact layout equalities needed by the earlier LPNAdvice bound
plan; the tagged-list markers must not be dropped.

## Raw LPN limitation that must not be hidden

LPNFamily.Raw.encDraw encodes a noise seed c with

  pairEncode (pairEncode (Nat.bits c.1.val) (natToList width c.2.val)) [].

Nat.bits(selector) varies in length. Therefore no fixed width can be supplied
for this element encoder as currently defined. Do NOT apply helper01 there
with a false width assertion, and do NOT change this final encoding merely
to make a proof easy. The outer closed pair makes it self-delimiting, so the
existing injectivity statement is sound but needs a separate argument.

A public closed-pair concatenation identity exists as
Complexity.BinArith.pairEncode_nil_append in ClassP/BinaryArith/Words.lean:57
(and another copy in Asymptotic.BlockEncryptor). Words happens to be in the
current transitive closure, but BinaryArith.* is a Phase B exclusion in the
dispatch. This preparation does NOT adopt that API or add its import. Root
must resolve applicability under the binding Phase A rules before using it;
otherwise retain the variable-width recovery as an explicit separate gap.
A generic prefix-free-list theorem should not be smuggled in under a new name.

The fixed-width helper task is therefore complete for the listed constant
layouts, but it does NOT close Raw LPN's variable-width list obligation.
That limitation is a proof-route issue, not evidence that its injection
statement is false. No source/statement repair is proposed.

## Pending verification

Both helper statements and all specialized uses need root exact?/apply?
searches and elaboration. In particular, verify the List.cons.inj spelling,
reader rewrite occurrence order and successor arithmetic under the pinned
Lean environment. These are untested syntax details, explicitly NOT_RUN.
No kernel proof, seal pass, or automatic tactic output is claimed.
