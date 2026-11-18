# Raw LPN variable-width draw injection — untested candidate

01-encDraw_injective.proof is a complete replacement BODY for the existing
LPNFamily.Raw.encDraw_injective, LPN.lean:365. It retains every encoding definition,
selector Nat.bits word, fixed-width residue, list marker, and outer pair. It adds no
assumption, import, theorem, helper, sampler, algorithm, or statement change.
No Lean/Lake/build/cache, exact?/apply?, implementation edit, git mutation, or agent
spawn occurred. Only /private/tmp proof notes were written. The candidate has NOT
been elaborated; all mechanical checks and final axiom verification belong to root.

Source snapshot HEAD `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`; LPN.lean SHA256 `162f7692bdc35a09ccb23ef330e2f8d70ca0c2250c5630a99ea6120463ee15f0`.
The expected context is the existing LPNFamily.Raw namespace with F : Raw and ell : Nat,
and the owner's existing open Complexity Turing Games declarations.

## Closure correction and superseded first draft

The initial draft used Complexity.BinArith.pairEncode_nil_append from
ClassP/BinaryArith/Words.lean:57. That was based on a historical closure assertion.
The CURRENT comment-aware source closure shows Words is NOT imported by LPN; it is
loaded only later elsewhere. The exact analogous BlockEncryptor identity is also
unavailable at LPN. That draft is superseded. The current candidate contains no
BinArith reference, and must not be represented as checked with the missing lemma.
No forbidden direct import was added or proposed.

The current minimal route applies the ALREADY IMPORTED pairEncode_injective at the
concrete pairs (payload x, code xs) and (payload y, code ys). Its input equality is
normalized using ONLY the published pairEncode_eq_dbl reader and the Core list
append_nil/append_assoc equations. There is no statement or separate proof of
pairEncode a [] ++ tail = pairEncode a tail, no local generic identity/prefix-free
predicate, and no new parser. Both the hypothesis and the target of this concrete
injection application reduce to the same public-reader append normal form.
This transparent equation normalization replaces the unavailable identity call.
Its conceptual relationship to that identity is disclosed here; it is not hidden
under a private helper name or imported indirectly through unrelated machinery.

## Exact retained layout and proof route

Let payload(c)=pairEncode (Nat.bits c.selector.val) (natToList width c.residue.val).
Let block(c)=pairEncode payload(c) []. These are LOCAL abbreviations for the
encoder's existing expressions, not new public algorithms or changed codes.

1. payload is injective. Existing pairEncode_injective recovers the selector bits
   and residue numeral. Existing LogProg.bits_injective recovers the selector
   natural; Fin.ext recovers its Fin value. For the residue, val<p<=2^width gives
   the two bounds for Candidates.natToList_injOn; ZMod.val_injective recovers it.
2. Prove injection of BoolCircuit.encodeList block by induction on the FIRST list.
   In nil/cons or cons/nil, encodeList_nil/cons readers give contradictory false/true
   markers. In cons/cons, cancel the true marker with List.cons.inj.
3. The remaining equality has two closed blocks followed by the two remaining
   list codes. Apply pairEncode_injective to (payload x, code xs)/(payload y, code ys).
   Its hypothesis follows by simpa only [pairEncode_eq_dbl, List.append_nil,
   List.append_assoc] using the closed-block equality. This recovers BOTH the head
   payload and the untouched rest without any block-width assertion. Apply payload
   injection and the induction hypothesis, then congrArg₂ List.cons.
4. Read F.encDraw through encDraw_eq. Two existing pair injections split matrix,
   secret and noise-list codes. Existing Modular.encodeMatrix_injective and
   encodeVector_injective use F.modulus_le_pow directly. Apply the preceding
   list injection, then existing List.ofFn_injective for the noise-seed function.

The local list argument is specialized to this actual F-dependent block encoder.
It does not duplicate the generic private PrefixFree definition or generic
BoolCircuit.encodeList_prefixFree theorem in Uniform.lean. The private theorem has
conceptual overlap as a more general result, which is explicitly disclosed. No
private generated name is accessed, and no generic theorem is recreated locally.
The fixed-width helper proposed for construction Encoding is not used at all: the
Nat.bits selector widths genuinely vary, so supplying a constant width here would
be false. The direct closed-block application avoids that mistake.

## Public APIs inspected and selected

| API | Exact source | Use |
| --- | --- | --- |
| pairEncode_injective | TCSlib/Complexity/TuringMachine/Encoding.lean:173 | Recovers outer matrix/secret pairs, payload fields and one closed-block payload/tail. |
| pairEncode_eq_dbl | same :216 | Existing owner reader normalizes one concrete application; dbl remains opaque. |
| List.append_nil / append_assoc | pinned Lean Init/Data/List/Basic.lean:610,625 | Normalize the publicly specified pair expression; no List definition unfolded. |
| BoolCircuit.encodeList_nil / encodeList_cons | TCSlib/Complexity/CircuitComplexity/Uniform.lean:96,100 | Observe actual false/true list markers. |
| Complexity.LogProg.bits_injective | TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean:82 | Public pure selector recovery, already imported transitively. |
| Candidates.natToList_injOn | TCSlib/Cryptography/Candidates/Arithmetic.lean:161 | Public fixed-width residue injection; p<=2^width supplies fit. |
| ZMod.val_injective | Mathlib public residue API, already used in Modular.encodeVector_injective | Recover residues from equal canonical values. |
| Modular.encodeVector_injective / encodeMatrix_injective | TCSlib/Cryptography/Encoding/Modular.lean:101,126 | Secret and matrix injection at the stored residue width. |
| List.ofFn_injective | Mathlib/Data/List/OfFn.lean:192 | Recover the actual finite noise-seed function. |

Pinned Mathlib Data/Nat/Bits, BinaryRec and Core Nat/Bitwise were searched for
ofBits_bits/bits injection/bit-fold reconstruction. No such public Core/Mathlib
round-trip theorem was found in those sources. Batteries' Nat.ofBits takes a
Fin-indexed function, not this list word, and its available theorems do not supply
the required Nat.bits inverse. Rather than reprove generic bit injection via a
fold or arithmetic induction, consume the existing public LogProg.bits_injective.
It is itself proved using the published bitsVal_bits inverse. No machine or
register-program construction/efficiency theorem is called from that module.

Public tagged-list decoder alternatives were also inspected. DAGCircuitSatLang's
decodeList_encodeList requires its own decoder/fuel infrastructure and is not in
the LPN closure; it would add unrelated machinery. The other Lamport encodeList
is a DIFFERENT nested-pair encoding. Neither is needed. Turing.Encoding has no
separate public suffix-preserving pair-prefix theorem, so the selected concrete
injection application consumes its existing shape/injection readers instead.

## Boundary and dependency audit

No lower bound on sample count or secret dimension is needed. If samples=0 the
noise list is empty, so the nil branch applies; empty matrix/vector injectivity is
explicitly included by the shared Modular API. A zero selector has Nat.bits 0=[];
its payload and closed outer pair still retain unambiguous separators. noiseDen=1
has only that selector. The proof places NO upper bound on noiseDen and makes no
constant-width claim for its selectors. The stored modulus prime gives NeZero;
F.modulus_le_pow gives the exact residue fit. No additional seed or stretch
hypothesis is introduced.

The candidate uses no existing sorried theorem, self implication or downstream
result as evidence. Every called theorem is an existing public library API.
Its local induction has no placeholders and one outer tactic block; bullets
handle subgoals without nested tactic blocks. Remaining risks are elaboration of
local payload/block lets under change, implicit pair arguments, and the concrete
reader-normalization step. Source-level reasoning is not kernel validation.

reuse-searches.json records successful and negative text searches, including the
missing Core inverse query. import-closure.json records the corrected current
owner closure, including the ABSENT Words source. Required sources are all present
for the current candidate. static-checks.json and SHA256SUMS report only text counts,
widths and digests; they are not Lean syntax or proof checks.
