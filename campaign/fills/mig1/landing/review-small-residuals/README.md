# Small residual candidate disposition

No concrete missed repoint to an existing exact-contract API is established for these three screen
rows. Their shared calculations already consume the canonical initialization and rewind interfaces.
This bounded finding supports retaining them as disclosed constructor/interface-assembly templates;
it is not a duplication-debt acknowledgment or a claim that no further abstraction is possible.
The maintainer owns final semantic classifications and audit severity.

This was source-only review, with no Lean execution or proof implementation. The nine source files
read and their exact hashes are captured in `capture.json` and `inputs/`; the three report rows are
preserved in `candidate-rows.json`. The completed forwarding-rewind evidence was not modified.

## G02: N02 and N04

**Accounting correction:** both declarations are in **Simulation.lean**, not Composition.lean:
`branchTM_initCfg_false` (line 342) and `branchTM_initCfg_true` (line 360). Both are private.

| Field or premise | False branch | True branch |
| --- | --- | --- |
| Selected machine | `M₂` | `M₁` |
| State injection | `Sum.inr` | `Sum.inl` |
| Selected bank | Right, after the `M₁.k` idle tapes | Left, before the `M₂.k` idle tapes |
| Configuration embedding | `rightCfg` | `leftCfg` |
| Inactive contents/heads | Blank / zero | Blank / zero |
| Native input head and output | One / empty | One / empty |

The exact goals identify the branch machine's initial configuration with the selected machine's
initial blank configuration in its bank. They do not assert a step, run, time bound or simulation
invariant. The transition table is unused. The only branch-specific state calculation is the
corresponding value of `branchTM`'s Boolean start-state selector.

Both bodies already perform the same canonical field calculation:

1. Use `MultiTapeTM.initCfg_eq` on the branch and selected machine.
2. Apply `Cfg.ext` to the five configuration fields.
3. Use `Cfg.init_state` with `Option.map_some`; the selected constructor finishes the state field.
4. Use `Cfg.init_inputPos` and `Cfg.init_output` for the unchanged input head and output.
5. For tapes and heads, use `Cfg.init_workTapes` / `Cfg.init_workTapePos`, function extensionality,
   and the two published `Fin.addCases_left` / `Fin.addCases_right` equations.

`leftCfg` and `rightCfg` (Simulation lines 196 and 207) are the same-home record embeddings with
opposite active-bank placement. Their public generated field equations are registered at lines
217–220. Their action/step/run interfaces (`leftCfg_apply` through `rightCfg_run`, lines 223–317)
transport a nontrivial existing configuration; they do not give this blank initial-configuration
identity. `MultiTapeTM.initCfg_with_q₀` (Finite line 241) changes a start state at the same tape
count and does not embed into a larger tape sum. No exact whole-configuration initialization
replacement was identified in the reviewed Simulation/Configuration/Deterministic/Finite/CfgFacts/
StateRenaming homes. That is a bounded candidate search, not a compiled namespace census.

The repeated `Cfg.ext` / `Fin.addCases` syntax implements blank-field equality in two distinct
fixed embeddings. Factoring it further would create another constructor-calculation abstraction;
this review does not establish an omitted existing mathematical contract requiring a direct repoint.
The same-home embedding definition reads are legal under the ownership rule; other-file
initialization reads already use published field equations.

## G06: N09

The relevant source contracts in Simulation are:

| Declaration | Visibility / line | Conclusion and reused work |
| --- | --- | --- |
| `rewind_scan` | Public, 514 | Starting in scan state at input position `p ≤ |x|`, reach the destination at position one in exactly `p+1` steps; every other configuration field is retained. |
| `rewind_first_step` | **Private**, 567 | Mandatory first step is the record update to scan state and one clamped left input move, with the new position at most `|x|`. |
| `rewind_from_any` | Public, 581 | Some endpoint time exists after the mandatory first move and scan. |
| `timed_rewind` | Public, 598 | Such an endpoint exists within the original input position plus two. |
| `rewind_scan_heads` | Public, 616 | Every prefix up to the exact scan completion time preserves all work heads. |
| `rewind_heads` | Public, 655 | One bounded endpoint witness has the desired full configuration and preserves work heads at every prefix through that witness. |

**Accounting correction:** `rewind_first_step` is a same-home private helper, not a published
public API. Its canonical reuse is nevertheless already present in all three endpoint wrappers.

For original input position `p`, all three endpoint wrappers choose the same concrete time
`R = (moveInputPos p .neg).val + 1 + 1`. They first call `rewind_first_step`, then compose its
step with the exact `rewind_scan` endpoint via `runFrom_succ_eq_step`. `timed_rewind` and
`rewind_heads` additionally discharge the elementary bound using `moveInputPos_neg_val` and
`omega`. Thus the shared endpoint substring is an explicit witness and two existing reader calls;
it does not repeat the scan induction or derive the first transition again.

The stronger contract's additional mathematical work is already canonical too: its zero-prefix
case uses `runFrom_zero`; its successor-prefix case rewrites the same first-step equation and
calls `rewind_scan_heads` with the explicit residual time and exact head position. It does not
repeat that theorem's head-preservation induction.

A direct replacement of this stronger proof by `rewind_from_any` or `timed_rewind` is not justified
by their conclusions: they hide the witness time and omit the all-prefix frame. In particular,
`dest : Option S` is arbitrary; after dispatch its next transition may move work heads. A coarse
bound such as `r ≤ p.val+2` alone does not show the selected run is still in the rewind phases at
every required prefix. Keeping the explicit `R` connects the endpoint to the exact range covered
by `rewind_scan_heads`.

Conversely the later `rewind_heads` contract contains the weaker existential conclusions by
projection, but it occurs after both weaker wrappers, so that is not a direct existing in-place
repoint in the current declaration order. This review proposes neither a reorder nor a new exact
witness API. Extracting the few-line endpoint assembly into another private helper could reduce
text, but is a further interface-packaging choice; it is not a demonstrated missed reuse of an
existing exact contract. No impossibility of future refactoring or debt waiver is inferred.

## Limits and recommendation

Retain G02 and G06 as specifically disclosed constructor/interface-assembly matches at this stage,
with the home/visibility wording corrected. This finding does not dispose of the separate
substantive terminal, bank, forwarding-rewind, tagged-lockstep or Catalog frame families, which
have their own repair/review work. There was no global duplication clearance, new public API,
source exception, design ruling, admission fill, source/Git/snapshot/cache mutation, build, screen,
commit, push, dispatch or merge-clearance claim.
