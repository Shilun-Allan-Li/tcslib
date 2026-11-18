# weightedIncidence_mulVec proof candidate

Exactly one theorem proof is supplied, in `weightedIncidence_mulVec.proof.lean.inc`.
The existing header matches the proposed header byte for byte; the opening statement
prose is unchanged. A proof sketch was appended. The snippet contains 28 lines, maximum
width 85, no admission, no tactic block, and no new helper declaration.

No live source edit, Lean/lake invocation, Git command, or new agent was used. The candidate
has not been elaborated by this agent and needs the lead's normal validation.

## Reuse already checked by the lead

The lead ran the required exact?/apply? probes on this exact helper statement. The raw logs
read by the agent are:

- evidence/search/path-algebra/run/mods/.lake_io-phfe-probes_PathAlgebraReuse.log;
- evidence/search/path-algebra/run/mods/.lake_io-phfe-probes_PathAlgebraApply.log.

The exact? log says it could not close the two incidence-action goals. The apply? log
contains only partial unrelated function-equality suggestions. The padded-incidence goal
in the old probe had a separate type-inference error, which the lead is fixing with
`Fin.snoc (α := fun _ => R) x (1 : R)`. This candidate does not depend on that theorem.

## Proof route and nearest relatives

The source proof is a composition of published statements, not another singleton-sum
argument:

1. `Pi.single_apply`, generated from Algebra/Notation/Pi/Basic:89-92, identifies each
   conditional coefficient with its supported coordinate vector. Its equality condition
   is already evaluated-index = supported-index, matching the header exactly.
2. `Matrix.sub_dotProduct`, Data/Matrix/Mul:225, separates the two coordinate vectors.
3. `Matrix.single_dotProduct`, Data/Matrix/Mul:178, evaluates the weighted parent term.
4. `Matrix.single_one_dotProduct`, Data/Matrix/Mul:205, evaluates the child term directly.

The initial `show` reduces only the Mathlib Matrix.mulVec and Matrix.of wrappers, as
explicitly permitted by Rule 10. The proof never passes a definition to simp/rw/unfold,
and consumes no TCSlib definition, reader, admission or other new helper. The Pi
subtraction inside the row equation is only a core/Mathlib pointwise reduction.

Focused searches and exact paths are in `weightedIncidence_mulVec.searches.txt`; the
larger graph/incidence and coordinate-action search inventory remains in `searches.txt`.
There is no public-law reproof: the complete finite-sum cancellation is delegated to the
existing single-coordinate dot-product lemmas.

The proof needs no additional import beyond Mathlib.Data.Matrix.Mul and its existing
public dependencies. The ring may be noncommutative or trivial; no multiplication is
reordered. Endpoints may coincide, E may be empty, and no extra finite/inhabited instance
is introduced. No mathematical obstruction was found.
