# Lamport verifier: one-existing-block proposal

**Unapplied, unchecked proposal at frozen source head**
`e9d64158461bfe24ddc88ab885bc4017899b4c16`.

Patch `Lamport-verFun-decision-transport.patch` follows the generator and signer proposals.
Those earlier patches were composed only in memory; the library file remains frozen.
This invocation changes only the existing local `h₃` proof block inside
`polyTimeComputable_lamportVerFun`. The `h₃` statement and all other source bytes relative
to the in-memory base are unchanged. No algorithm, header, premise, data field, import,
admission, helper declaration or additional tactic block is added.

## Diagnostic and the precise transport used

Completed seal 009 reports probe `1779:42` mapped to frozen source `362:42`, the `h₃`
statement. Its `convert`/`funext`/`simp` proof at lines 363–365 leaves an equality between
Boolean decisions whose displayed propositions look identical. The log does not print the
implicit decision procedures or transport terms, so it does not by itself establish why
the old conversion failed. This remains a real source diagnostic, not a false positive.

The replacement constructs the pointwise output equality explicitly:

1. Public `PolyTimeComputable.congr` transports the equality-test witness pointwise; no
   conversion of a function-valued computability statement is requested.
2. `Function.comp_apply`, `pairFstD_pairEncode` and `pairSndD_pairEncode` read the composed
   test's paired inputs. These are equation theorems, not definition unfolds.
3. Congruence of the singleton Boolean list reduces the output equality to Boolean equality.
4. Core `decide_eq_decide.mpr` reduces it to equivalence of the tested propositions. Its
   actual Lean-4.25.0 signature independently quantifies `{_ : Decidable p}` and
   `{_ : Decidable q}` and states `decide p = decide q ↔ (p ↔ q)`
   (`Init/PropLemmas.lean:464–466`). Thus the proof does not need the two decision procedures
   to normalize to the same expression.
5. Public `blockState_eq` rewrites the target's two state arguments to the paired words
   already present in the compositional witness; the propositions then coincide.

The two `blockEncFun` applications and their algorithms remain opaque. The only simplification
lists in the replacement are the three explicit composition/projection equations and then
`blockState_eq`. There is no broad simp, foreign ordinary-definition unfold, copied foreign
proof, new logical assumption or attempt to weaken the equality test.

## Native isolation limit and fallback

This direct proposition-equivalence proof follows from the inspected reader statements,
but it has not been elaborated or sealed here. The exact hidden cause of the old
identical-looking goal remains unisolated. Root should first native-check this existing
`h₃` block under the recorded seal. If an earlier step leaves a different goal, isolate only
this witness/equality in a scratch probe with the same local variables, exact `hX`/`hY`
terms and seal, and print explicit/fully detailed goals immediately before the decision
transport. Check that singleton congruence exposes `decide p = decide q`, then that
`decide_eq_decide.mpr` exposes `p ↔ q`, before testing the two `blockState_eq` rewrites.
Do not broaden simplification or remove the seal to hide that failure. No second probe proof
block was written or run in this invocation.

## Fingerprints and static checks

| Version | SHA-256 |
|---|---|
| Frozen library file | `91dcee4158e54b53372ea573067d8bb08576f73f2b4c08af2889c80d0eebd391` |
| In-memory generator + signer base | `8812be18ab448ff11d1c4f8a8ed0ba995831618780580d724a665f9a437ae09b` |
| In-memory generator + signer + verifier result | `d735ef6270bb03ef108adff3a9f6e2b2495b34a27d000bfb12c3a9ca20ef676d` |

All three proposal patches compose in memory with exact context; the stored verifier diff
has one hunk. The existing `:= by` count is unchanged, and every byte outside this one
existing local proof is preserved relative to the in-memory base. Actual library bytes
retain the frozen fingerprint. No Lean/cache, Git command, app, source edit or seal run.
The correctness proof's separate `coinLen` diagnostic is still untouched.

**Not yet clear to merge — proposal remains unapplied/unchecked; correctness transport and root verification remain.**
