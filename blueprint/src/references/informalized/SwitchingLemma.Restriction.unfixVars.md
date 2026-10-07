<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: Restriction.unfixVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Freeing a list of variables in a restriction

**Definition.** `unfixVars : Restriction n → List (Fin n × Bool) → Restriction n`
is defined by structural recursion on the list:

- `unfixVars ρ [] = ρ`;
- `unfixVars ρ ((v, _) :: rest) = unfixVars (Function.update ρ v none) rest`.

It walks the list and sets each listed coordinate `v` to `none`, restoring it to
free. A plain definition; no proof.

**Remark.** The `Bool` component of each pair is ignored (the pattern binds it as
`_`), so the argument type `List (Fin n × Bool)` is only there to match
`fixVars`, of which this is the mirror image; `unfixVars ρ l` depends solely on
`l.map Prod.fst`. Consequently `unfixVars (fixVars ρ l) l` frees the listed
variables rather than recovering the original `ρ`, unless `ρ` already had them
free.

**Note.** Dead code: `unfixVars` has no call sites anywhere in `TCSlib/` outside
its own defining equation (only stale copies under `.claude/worktrees/` mention
it). Like `fixVars`, it is a convenience constructor kept for the intended
interface; the switching-lemma files build modified restrictions with
`Function.update` directly.
