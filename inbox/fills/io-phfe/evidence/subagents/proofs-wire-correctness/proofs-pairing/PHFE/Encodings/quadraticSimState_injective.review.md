# Complete simulator-state word injectivity candidate

Exact live frozen header/opening prose and sketch preserved; one outer tactic block,
no admission, helper, generic foldr theorem, runtime definition, decoder, efficiency
premise, import edit, or new Mathlib root. No Lean/lake/Git command or source edit was
run. Native validation remains pending.

The existing Wire.quadraticSimState_eq/linearSimState_eq readers expose the fixed lists
of FOUR outer blocks and EIGHT inner linear-state blocks. Existing List.foldr_cons/nil
and the newly native-gated/proved Pairing.pairEncode_eq_iff split these fixed nested
pairs directly. Only reflexive empty-tail equalities/conjunctions are simplified.
There is no induction, custom parser, or new generic fold-encoding injectivity lemma.

Wire.groupMatrix_injective recovers the fixed public metadata matrix. The EXISTING
Modular.encodeMatrix/Vector_injective APIs recover ALL scalar fields: A,W,U,V,c,w,v,
basisInv,y1,y2. The explicit Uflat equality fixes Fin(l.eval kappa*2) before applying
modular injectivity, then existing finProdFinEquiv inverse identities recover the
original product-indexed U. This follows root's MSK interface repair. The total stored
basisInv is included, so arbitrary singular/before-challenge states are covered; no
valid-setup or invertibility assumption is silently added.

The existing BB1Machine.order_le_two_pow bounds the public modulus by its source-group
width, read through PublicParams.group_eq. Its module is now already a direct Encodings
import, so this candidate adds no dependency. No BB1 draw/decoder or new order-count
proof is used. Primitive record field equalities finish the arbitrary typed states.

Rule 10: all supplied simp entries are published Wire, List, pair, or scalar equation
readers/theorems. No public definition body is supplied to simp/rw/unfold. Shared
group/modular encoding injectivity is consumed whole; no matrix/point block splitting
is repeated. No group exponent is extracted. Empty public/private dimensions remain
in scope under the original header.

Static source reads: frozen quadraticSimState_injective; WireDraws fixed state word
readers; Quadratic.SimState and Linear.SimState field order/types; live pairEncode_eq_iff
in Parameters.lean:51; Wire.groupMatrix_injective; Modular encodeMatrix/Vector injectivity;
BB1Machine.order_le_two_pow. No new helper target/probe is needed.
No mathematical obstruction found. The conjunction destructuring and full candidate
remain for root's native check before completeness/axiom claims.
