# One proof candidate: BilinearGroup.expVec_add

Target: existing frozen statement in Pairing/Exponents.lean around line196, as read at the
parent-reported live HEAD7d42a6ef6a20d379c524c11db87a1b0c0e4c25df. No Git command was run to
verify HEAD independently. No live edit, Lean/lake/build/proof-check or new agent was used.

The fragment retains the exact public docstring/header and replaces only the sorry body.
It is intended inside the EXISTING namespace/context:

TCSlib.Cryptography.Pairing.BilinearGroup,
{ι : Type*} {wG wT : ℕ} (B : BilinearGroup wG wT).

The proof is a pure term (ZERO tactic blocks) and introduces no helper or import. It uses:

1. Core funext to compare coordinates.
2. Exponents.expVec_apply at the sum and each summand.
3. Published Group.pow_val_add, the actual scalar modular-exponent theorem.
4. Core congrArg₂ and Eq.trans/symm to rebuild the right side.

Pointwise addition/multiplication of function values is only definitionally reduced as
notation. No TCSlib algorithm, ZMod definition, or other foreign definition is unfolded or
passed to simp/rw. The scalar exponent law itself is REUSED, not reproved. The proof never
mentions another admitted algebra lemma or the target expVec_add constant itself.

Read Operations.lean in full: its orderStr/mulG/powG/pairStr/mulT/memT specs concern efficient
encodings and supply no alternate algebra proof. Group.pow_val_add at254 is the closest
published mathematical result. Operations is therefore not imported by this pure lemma.
No efficiency premise is required and no new one is added.

Search evidence is in expVec_add-searches.txt. The only existing expVec_add full name found
is the target declaration itself; analogous target-group transport is a separate statement.
Mathlib Pi.evalMulHom shows the same pointwise function reduction principle but does not
state this ZMod exponent wrapper. Core funext is at Init/Core.lean:2254.

Exact?/apply? probes and actual elaboration remain PENDING PARENT. The fragment is NOT a
reported passing proof until parent checks it. Static review found no mathematical
obstruction: the source scalar identity immediately gives this result at every coordinate,
including an empty index type, arbitrary base g (even1), and all admitted group parameters.
