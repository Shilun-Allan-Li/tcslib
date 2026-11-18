# BilinearGen.dlinEnc_injective candidate

Status: scratch full candidate checked by inspection only; native verification pending.
No Lean/lake/build/Git/live edit/additional agent was run. Frozen header/prose exactly
preserved; one tactic block, no remaining holes/sorry, no helper or statement change.
All challenge points remain arbitrary group elements. No scalar encoding, inverse encoding,
discrete logarithm, scalar witness, or generator-coin recovery is used.

## Dependent transport route

Destructure the two actual DLINChallenge records and their PublicParams/GroupDescription
records. Read dlinEnc_eq/dlinStr_eq. Turing.pairEncode_injective first recovers equality of
the raw public description strings. Substitute that equality BEFORE comparing group points;
both groups now literally have type (G.group κ d₁).G. This is ordinary dependent equality
elimination, not a new group equivalence or a hidden codec transport assumption.

The remaining five nested pairs split into the generator and five point words. Each word
pair is handled by List.ofFn_injective followed by the existing group's encG_injective.
Eliminate these six data equalities. Reflexivity then closes the constructor equality:
reachability and nonidentity witnesses are proofs of propositions and are removed by Lean's
proof irrelevance. Duplicate generator coins are not extracted, compared, or stored.

No PublicParams.encode_injective helper is necessary: this actual DLIN encoding stores
the description and generator as separate nested components, and existing pair injection
already provides the dependency-aligning description equality. No new generic target or
probe is requested. Every explicit rewrite/simp item is a published reader. Record/subtype
case elimination and proof irrelevance use primitive constructors rather than generated
foreign definition equations.

## Actual API searches and inspections

* Read current Pairing/Linear.lean:119-181 for DLINChallenge fields, dlinEnc_eq and exact
  frozen header. Read MatrixDH/Parameters.lean:46-200 for GroupDescription, PublicParams,
  group_eq/orderParam_val, encode_eq and publicParamsCore_eq. PublicParams has no existing
  encoding injectivity theorem in that module.
* Search `pairEncode_injective|pairEncode.*(inj|eq_iff)|eq.*pairEncode` in the shared
  TuringMachine/Encoding.lean located Turing.pairEncode_injective at 173. Read :165-179:
  it is injectivity of the function on word pairs, so Prod.mk.inj gives the component
  equality pair without a parser/cancellation reproof.
* Search `HEq.*(enc|encode)|injective.*(Sigma|sigma)|Sigma.*injective|Subtype.*(heq|inj)|sigma.*encode|dependent.*inject`
  over Encoding, Pairing and Mathlib Function/Equiv sources found no more direct compatible
  dependent public-challenge codec result.
* Search `encode.*injective|injective.*encode|Sigma.*(encode|codec)|dependent.*codec` over
  Pairing/Encoding/Complexity found scalar encoders and circuit-specific Sigma codecs;
  none applies to this existing reachable-description/group record. They are not imported,
  copied, or specialized into a private helper.
* Search for generic Sigma injection/extensionality in Mathlib Logic/Function/Equiv found
  Sigma.ext use; it is unnecessary once the actual record's description is substituted.
* Read Pairing/Group.lean:130-132 for encG/encG_injective and previously inspected
  Mathlib/Data/List/OfFn.lean:192 for List.ofFn_injective.

## Parallels and overlap disclosure

Pairing/Assumptions.lean has a private probability bound that also recovers a target-group
point with encT_injective(List.ofFn_injective h). Its statement/proof is not copied or used;
only the already-public generic List injectivity and public group field are consumed here.
The scalar Encoding.Modular injection proofs likewise use List.ofFn_injective but contain no
needed dependent-group transport. No private proof machinery is duplicated.

Native focus: nested dependent rcases of the actual records, group-type normalization after
subst d₂, and equality elimination for the generator's dependent nonidentity proof. All are
constructive constructor/equality steps; no additional mathematical API is missing by
inspection. This candidate has no dependency on pending correctness or length admissions.
