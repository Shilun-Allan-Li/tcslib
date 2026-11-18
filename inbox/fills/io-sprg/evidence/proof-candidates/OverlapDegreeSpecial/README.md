# Isolated specialized Degree overlap goals — NOT RUN

Eighteen goal-only templates cover exactly the existing public/private zero,
constant, left/right variable, addition, multiplication, finite sum, finite product,
and groupwise-renaming theorems. probe-index.json uses their exact current source
names and records the source lines at inspection. No Lean, Lake, cache, git command,
implementation-source edit, agent spawn, or materializer invocation occurred.

Every pubDegree/privDegree occurrence is replaced literally by weightedTotalDegree
with Sum.elim indicator weights. Both finite-sum HYPOTHESES and conclusions are
expanded. Public weights are1/0; private weights0/1. Renaming uses the actual
Sum.map e f, with target indicators on sigma'/tau' and source indicators on
sigma/tau. Nat annotations on literals preserve the original Nat codomain.
No local alias, duplicate wrapper definition, copied owned helper, arbitrary weight
parameter, or stronger/generalized goal is substituted for the actual statement.

All original hypotheses are retained: arbitrary variable/coefficient/index types
and only CommSemiring R; sums have exactly their pointwise bound h and d; products
have no extra premise; rename has the same two equivalences. No Nontrivial,
DecidableEq, Fintype, positivity, nonempty-type or nonzero-polynomial assumption
is added. The zero semiring, empty types/sets and zero bound remain allowed.

Templates import exactly the owner's two Mathlib roots plus toolchain
Lean.Elab.Tactic.LibrarySearch. The fresh import-closure audit contains ZERO
TCSlib modules. Consequently the M0 specialized theorem, the owned generic six,
and every other StructuredSeed theorem are absent, regardless of whether root has
already filled their bodies. Clearing locals or renaming a goal would not exclude
a globally imported self theorem; excluding its entire module closure does.

materialize.py is BYTE-FOR-BYTE the existing OverlapProbes materializer. Its JSON
schema/CLI and /private/tmp output guard are unchanged; it reads this packet's
local index/templates. Root may request one named template with --tactic exact?
or --tactic apply? and one --output path. One invocation introduces exactly ONE
outer search block in ONE output; do not batch two materializations in one tool
invocation under the standing one-block rule. No materialization was performed here.

The18 templates each have zero tactic blocks and one __PROBE_BODY__ marker.
Root will run both searches for each,36 probes total, with source/log bindings.
An exact? result must close the goal. An apply? suggestion with remaining goals
is a partial match and must be recorded with those subgoals; it is not a proof.
The two zero goals are expected positive controls for public weightedTotalDegree_zero,
but no search/compile success is claimed. No fallback proof or sorry is appended.

Source-binding records the Degree bytes read while root may be filling its six
generic bodies. Those body edits may move source lines; they do not change the
18 specialized mathematical statements. This packet changes no imports or
statements in implementation and supplies no proof body for them.
