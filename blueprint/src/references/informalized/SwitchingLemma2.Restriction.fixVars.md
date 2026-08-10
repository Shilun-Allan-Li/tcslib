<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Restriction.fixVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Fixing a list of variables in a restriction

**Definition.** `fixVars : Restriction n → List (Fin n × Bool) → Restriction n`
is defined by structural recursion on the list:

- `fixVars ρ [] = ρ`;
- `fixVars ρ ((v, b) :: rest) = fixVars (Function.update ρ v (some b)) rest`.

That is, it walks the list left to right and overwrites coordinate `v` with
`some b` at each step, so later pairs win over earlier ones for a repeated
variable. A plain definition; no proof.

**Remark.** Its companion `unfixVars` (same file) is the mirror image, updating
each listed coordinate to `none` instead. Neither is a lemma-bearing notion
here: both are convenience constructors for describing a restriction obtained
from `ρ` by fixing/freeing a designated block of variables.

**Used in.** Nothing, currently — `fixVars` and `unfixVars` have no call sites
in the repository. The switching-lemma files build modified restrictions with
`Function.update` directly (e.g. in `Switching/Encoding.lean`), so these two
definitions are presently dead code kept for the intended interface.
