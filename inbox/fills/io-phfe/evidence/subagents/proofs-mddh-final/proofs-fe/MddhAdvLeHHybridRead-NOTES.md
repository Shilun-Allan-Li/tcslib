# Inner hHybridRead candidate

Scratch only; no Lean, lake, build, Git or live edits. This fills ONLY the existing local
hHybridRead statement with κ,j,real already introduced. The proof-only fragment has a
single tactic block, six-space body indentation, and no admissions. Native check pending.
It does not change the parent hybrid ladder or any previously checked proof segment.

## Argument and boundary discipline

Expand only the proof-local hybrid, then read its acceptance and sequential draws through
accept_eq and the published bind/pure probability/expectation readers. Fix pp,M,S,U under
explicit expectation congruences. Expand only proof-local obs and use prob_eq_expect on
its D.Coins probability. The original coins then align exactly.

The remaining comparison is transported through the actual distinguisher/encoding/exponent
expression by congrArg on its SCALAR response matrix. No foreign function is unfolded or
inverted, and ProbComp.prob is not closed by definitional equality.

At each output coordinate, split the Bool and whether b.val=j.val. In the random branch
the threshold is j; selected U entries and every other entry coincide. In the real branch
the selected threshold test is true, and Matrix.mul_apply' reads (M*S)[a,j] as row a of M
dotted with S's column j, which is precisely the displayed Matrix.mulVec entry. Outside
the selected column, the tests b.val<j.val+1 and b.val<j.val agree; omega uses the explicit
non-equality hypothesis. All original pp,M,S,U and coin draws are retained. This contains
no resampling proof; the surrounding ladder's existing two coordinate-law calls remain.

## Actual static searches/reuse

Read the current live shared hybrid/obs definitions and the exact root scratch
MddhAdvLeHHybridResample.root.skeleton.proof.lean.inc, where the local name is hHybridRead
(the statement remains unchanged from the former hRead).

- `rg -n 'hHybridRead|let hybrid|let obs|hHybridResample'` in live SelfReduction.
- Read SelfReduction:605-665; source still had the prior whole hybrid hole while root's
  repaired surrounding candidate was under native check, so the precise insertion name
  was confirmed from the root scratch file rather than inferred from that live snapshot.
- Read Mathlib/Data/Matrix/Mul:288-307 and669-698. `Matrix.mul_apply'`:299 gives exactly
  `(M*N) i k = dotProduct (M i) (fun j => N j k)`. Only the permitted core/Mathlib
  Matrix.mulVec entry reduction remains in its exact application; neither mulVec nor
  dotProduct is named in any simp/rw/unfold list. dotProduct is GLOBAL, not Matrix-prefixed.
- `rg -n 'mulVec.*(apply|column)|mul_apply_eq|mulVec.*col|dotProduct.*col'` in matrix sources;
  mul_apply' is the closest exact published column reader, so no helper is introduced.
- Read Games/Probability:94-132 and202-230 for exact expect_pure, expect_bind,
  prob_pure, prob_bind, prob_eq_expect signatures. Reuse is explicit at each probability
  leaf; no foreign ProbComp.prob body is assumed.
- Queried the existing root scratch for the name hHybridRead and the diagnosed hF repairs;
  those prior repairs are outside this fragment and are not overwritten.

Two finite-index equality branches use `Fin.ext h` to substitute b=j. Core Bool and
Nat equation lemmas reduce the closed branch; the only fresh arithmetic subgoal is the
stated hCompare iff, discharged by omega within the same outer tactic block.

## Root check notes

Fragment is38 lines, maximum88 columns. It should replace only the term-sorry body of
hHybridRead inside the repaired ladder. The final true selected-coordinate exact call is
intentionally `Matrix.mul_apply'`, not a repeated sum proof. If its implicit row/column
arguments require extra annotation under the native context, use the same reader with
`M := M`, `N := S`, `i := a`, `k := j`; no new statement/helper is needed.
No successful native typecheck or standard-only result is claimed by this scratch draft.
