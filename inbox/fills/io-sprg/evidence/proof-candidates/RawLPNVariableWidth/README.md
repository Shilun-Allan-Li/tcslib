# Raw LPN selector encoding: scope and recovery route — NOT RUN

No source edit, Lean/build/cache, git mutation, new import or agent spawn.
The current LPN transitive closure is saved in current-lpn-closure.txt.
Fresh static closure distinguishes the public pure facts below:
  Complexity.BinArith.pairEncode_nil_append
    Complexity/ClassP/BinaryArith/Words.lean:57;
  Complexity.LogProg.bits_injective
    Complexity/SpaceComplexity/Machines/Bin.lean:82.
LogProg.Bin IS in the current LPN owner closure, but BinaryArith.Words is NOT.
The Words identity is available downstream through OneWayLemmas; it is not
available to fill a proof located earlier in LPN.lean. No direct BinaryArith
module import is proposed. See the owner-specific route below.

## Binding scope conclusion

Dispatch item3 (pasted-text-1.txt:313-316) prohibits IMPORTING the Phase B
modules, including Complexity.ClassP.BinaryArith.*. Its item7:455-456 names
sweep-r2/r3 as the MUST-REUSE list and named do-not-use list. Sweep-r2 legend
labels B Phase B only, but its Appendix enumerates specific modular arithmetic,
addition/multiplication, forLoop and their polynomial-time facts; it does not
name pairEncode_nil_append or prohibit all constants in its namespace.
Design-r2 section2.3 similarly says minus Phase B imports and separately do
not import the named modules. Rulings adds no broader constant-usage ban.

Therefore reusing this pure list identity WHERE ALREADY LOADED is permitted, with
explicit overlap/scope disclosure. It introduces no machine, sampler, RAM
interface or PolyTimeComputable proof. The explicit X/B operation names remain
excluded. In contrast, adding import ...BinaryArith.Words would violate item3.
The alternative copy in Asymptotic.BlockEncryptor is unnecessary and should
not be imported.

The DOWNSTREAM forced path includes Asymptotic.OneWayLemmas ->
BinaryArith.Loops -> BinaryArith.Words. It does not run through the current
LPN owner, whose exact closure snapshot was refreshed during this audit.
Candidate01 is consequently only usable in an appropriate downstream host.
Do not add a forbidden import merely to use it in LPN.lean.

## Keep the existing final Nat.bits definition

Root selected retaining Raw.encDraw's Nat.bits selector. This code is injective
and its closed pair is self-delimiting for all selector widths, including zero.
There is no mathematical or generic-efficiency obstruction in this definition.
The log-width proposal natToList(log2(noiseDen)+1) is rejected pre-M0 engineering
exploration; it would fit by Nat.lt_pow_succ_log_self and keep polynomial bit
widths, but is not needed to repair any false obligation. In particular retain
the actual draw/core law, LWE challenge, pair/list layout and T6 target unchanged.
The fixed-width helper for Encoding/LPNAdvice still cannot be applied to this
Raw element encoder with a claimed constant width.

## Allowed specialized variable-width route

Let payload(c)=pairEncode (Nat.bits c.1.val)
  (Candidates.natToList width c.2.val), block(c)=pairEncode(payload(c),[]).
The existing pure identity converts
  block(c) ++ suffix = block(d) ++ rest
into
  pairEncode(payload(c),suffix)=pairEncode(payload(d),rest).
Turing.pairEncode_injective recovers BOTH payload equality and suffix equality.
Apply it again to payload equality. Complexity.LogProg.bits_injective then
recovers selector.val and Fin.ext recovers selector. For the residue use the
public Candidates.natToList_injOn (Arithmetic.lean:161), its val_lt bound,
and Raw.modulus_le_pow; recover the ZMod value with ZMod.val_injective.
Pair the recovered components for payload injection.

The staged candidate01 (downstream only) consumes exactly this closed-pair shape
and an injective
payload f, then uses the two public BoolCircuit.encodeList_nil/cons readers.
An induction cancels the true marker, invokes the existing closed-pair identity
and pair injectivity, and recurses on the recovered suffix. Nil/cons cases are
separated by false/true markers. It defines no new encoding, decoder, predicate,
choice or algorithm. Apply it to payload above, then List.ofFn_injective, and
combine with the public modular matrix/vector injection theorems to fill the
existing Raw.encDraw_injective body.

## Owner-available representation step, no new import

Candidate02 replaces the unavailable Words theorem by normalizing hbody with
  simp only [Turing.pairEncode_eq, List.append_nil] at hbody
and then uses Turing.pairEncode_injective at the explicit type
  (f a, code as) = (f b, code bs).
The expanded hbody definitionally matches pairEncode(f a,code as)=
pairEncode(f b,code bs). No append associativity, decoder or induction on
individual bits is needed. The owner's public MR equation is reused;
no foreign definition is unfolded by name.

This short INLINE representation step overlaps with the public Words identity.
Disclose this fact and the import restriction explicitly under dispatch item8:
the ban is on UNDISCLOSED inline re-derivation, and pairEncode_nil_append is
not a named MR theorem in the sweep. The broader list induction still has no
public equivalent in the current allowed closure. This is a permitted narrow
proof route; it is not permission to restate other Phase B theorems or add any
excluded import.

## Overlap disclosure and pending checks

Private BoolCircuit.PrefixFree and encodeList_prefixFree in Uniform.lean have
more general prefix-free-list functionality; they cannot be reused as public
APIs and are not accessed by generated private names. Candidate01 is specialized
to exactly pairEncode(payload,[]) and delegates parsing/recovery to the existing
public pair theorem. Search public alternatives before landing: name/shape search
found only the unrelated Lamport nested-pair-list injection, the heavier decoder
route, and the existing Words identity. The already-staged fixed-width helper is
a different specialization. Do not restate a general PrefixFree abstraction.

All candidate syntax, exact?/apply? probes, elaboration and seals remain pending
root. No Lean executed, kernel proof or successful probe claimed. The earlier
FixedWidthList README's caution that scope required resolution is superseded by
this exact binding assessment; its Raw fixed-width limitation remains valid.
