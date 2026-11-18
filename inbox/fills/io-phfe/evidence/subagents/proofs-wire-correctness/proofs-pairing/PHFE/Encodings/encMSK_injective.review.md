# PHFE master-secret fixed-width injectivity candidate

Exact live frozen header/opening prose and sketch preserved; one tactic block, no new
helper/runtime definition, decoder, efficiency premise, or admission. No Lean/lake/Git
command or live source edit was run. Native validation remains pending.

## Staged exact-width recovery (root's CT repair followed)

First apply congrArg List.ofFn to equal encMSK values. Then ONLY encMSK_eq is simplified
in that equality. Next rewrite the TWO specialized ofFn_padFin_of_length instances
using the now-native-PASS quadraticMSK_length. ONLY AFTER full word recovery are
Wire.quadraticMSK_eq/linearMSK_eq read. This avoids bottom-up expansion of Wire words
preventing the specialized padding lemma from matching. No generic bounded-word
zero-padding injectivity is claimed or needed: both unpadded lengths are exact.

## Existing data injectivity consumed whole

The EXISTING pairEncode_injective separates the fixed nested pairs.
Wire.groupMatrix_injective recovers public group matrix metadata.
Encoding.Modular.encodeMatrix_injective recovers W, flattened U, and V, using the
EXISTING order-width theorem. U's coordinate transport is inverted by evaluating
at finProdFinEquiv j and using Equiv.symm_apply_apply; no new flatten/coordinate
helper is built. Primitive structure cases and field equalities finish the records.
There is no row counting, encoded-block splitting proof, encoder decoder, or recovery
of a scalar exponent from a group value. Empty dimensions remain covered.

## Required existing width-theorem import

Static current import traversal found Encodings has NO path to
TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Draws.
Root must make that existing module available when integrating the named
IdentityBased.BB1Machine.order_le_two_pow application (previously authorized width
reuse route). No draw, sampleBelow decoder, or other BB1 operation is used.
No width/cardinality theorem is reproved. This is an existing sibling-module dependency
for a generic pairing width fact; promotion to a common pairing home remains the
previously disclosed cleanup request after scope opens. No live import changed here.

Rule 10: only encMSK_eq, exact padding readers, published Wire word equations and
PublicParams.group_eq are supplied to simp/rw. All injectivity/count bounds are existing
public theorems; no definition bodies are supplied to tactics.

Static exact API reads: current frozen encMSK target, encMSK_eq, quadraticMSK_length,
Wire.quadraticMSK_eq/linearMSK_eq, live Wire.groupMatrix_injective,
Modular.lean:126 encodeMatrix_injective, Adversary.lean:218
ofFn_padFin_of_length, Turing pairEncode_injective, and BB1Machine/Draws.lean:156
order_le_two_pow. No mathematical obstruction found.
