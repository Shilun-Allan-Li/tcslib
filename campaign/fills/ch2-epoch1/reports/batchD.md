# Chapter 2, epoch 1, batch D

All seven assigned proofs are filled. Only the three owned Lean files changed.
The audited public signatures, definitions, declaration order, and existing
comments are preserved. One verification-policy exception is escalated below:
six targets use a proper subset of the brief's exact expected axiom triple.

## Revision and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Base: `7494522e8826be6b54675307668435afc59c005d`.
- Result: `aebe3d9b6f81b93767c168746e2f0aa53d8acb46`.
- Working and bundle branch: `complexity/arora-barak-ch1`, following the user's
  subsequent explicit instruction. This supersedes the brief's requested
  `fill/ch2-e1-D` working-branch name.
- Delivery: ZIP only; no PR or remote push. One format-patch commit and an
  incremental git bundle against the stated base are included.
- Toolchain: Lean 4.25.0; Mathlib commit
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Execution: one agent, no delegation. No `lake build` invocation.

The source diff consists of:

1. `TCSlib/Complexity/Formulas/CNF.lean`
2. `TCSlib/Complexity/Formulas/CNFEncoding.lean`
3. `TCSlib/Complexity/Formulas/DNF.lean`

## Targets versus the prescribed sketches

| Target | Completion and proof route |
|---|---|
| `Complexity.eval_congr_of_lt_numVars` | Filled. An occurring variable contributes its successor to the flattened list; membership bounds that successor by the maximum fold. Apply core's evaluation congruence. |
| `Complexity.exists_cnf_boolFun` | Filled. List one excluding clause for each falsifying assignment from the filtered finite universe. Prove the excluding-clause equivalence, then separately prove the variable, clause-count, width, and evaluation conjuncts. No positive-arity assumption is used. |
| `Std.Sat.CNF.parse_serialize` | Filled. Prove the specified unary-run identity, suffix-carrying literal round trip, clause round trip, and formula round trip; instantiate the last at the empty suffix. Both recursive round trips quantify over **every fuel at least the serialized fragment length**, exactly as required. |
| `Std.Sat.CNF.decode_serialize` | Filled. Apply the parser round trip and reduce `Option.getD` on `some`. |
| `Std.Sat.CNF.numVars_decode_le` | Filled. Prove exact literal consumption and suffix-aware bounds for successful clause/formula parsing; bound the maximum fold termwise. Failed parses and nonempty final remainders reduce to the empty fallback. |
| `Std.Sat.CNF.evalDNF_dual` | Filled. Induct on literals to prove the clause identity, checking the two Boolean values of each assignment and polarity; then induct on clauses and apply Boolean De Morgan. |
| `Std.Sat.CNF.dnfTautology_dual_iff` | Filled. Rewrite the pointwise identity, Boolean negation, and negated existential. |

There is **no deviation from the required fuel-strengthening form**. For the
variable-bound proof, the consumed-prefix inequality is written additively:
each variable contribution plus the final remainder length is at most the
input length. The accompanying remainder bound makes this equivalent to
bounding the contribution by input length minus remainder length. This avoids
truncated-subtraction bookkeeping without changing the sketch's content.

Original docstrings and attribution text were retained verbatim. New helper
docstrings describe their contracts; the longer inductions have proof sketches.
No existing sketch appendix was changed or added.

## Every new declaration

All 18 additions are private: 16 theorems and two definitions. There are no new
public declarations, renamed declarations, or removals.

### `CNF.lean`, namespace `Complexity`

| Line | Name | Contract |
|---|---|---|
| 112 | `le_foldr_max_of_mem` | A natural-number list member is at most the list's maximum fold with initial value zero. |
| 146 | `foldr_max_le_of_forall` | A common upper bound for all list members bounds that maximum fold. |
| 155 | `falsifyingClause` | Definition: the `List.ofFn` clause containing each finite variable with polarity opposite to the given assignment. |
| 160 | `falsifyingClause_eval_false` | That clause evaluates false exactly when the total assignment restricts to the given finite assignment. |
| 177 | `falsifyingCNF` | Noncomputable definition: map the excluding-clause construction over the list of all falsifying assignments. |
| 181 | `falsifyingCNF_numVars` | The constructed formula's variable measure is at most its arity. |
| 193 | `falsifyingCNF_length` | The constructed formula has at most two to the arity clauses. |
| 202 | `falsifyingCNF_width` | Every constructed clause has width at most the arity; the proof uses its exact length. |
| 213 | `falsifyingCNF_eval` | Evaluation of the constructed formula agrees with the given function on the restricted assignment. |

### `CNFEncoding.lean`, namespace `Std.Sat.CNF`

| Line | Name | Contract |
|---|---|---|
| 169 | `takeTrues_replicate` | Reading a run of `k + 1` true bits followed by false returns exactly that count and preserves the false-prefixed suffix. |
| 179 | `parseLit_serializeLit` | A serialized literal followed by any suffix parses to that literal and suffix. |
| 191 | `parseClause_serializeClause` | A serialized clause followed by any suffix parses correctly with any fuel at least its serialized length. |
| 223 | `parseClauses_serialize` | The corresponding suffix-carrying formula round trip, again with any fuel at least its serialized length. |
| 280 | `takeTrues_length` | The counted run length plus returned remainder length equals the input length. |
| 293 | `parseLit_length` | Successful literal parsing consumes exactly its variable index plus three bits. |
| 312 | `parseClause_bounds` | On success, remainder length is at most input length; every returned variable index plus one, plus remainder length, is at most input length. |
| 373 | `parseClauses_bounds` | The same remainder and variable bounds for every literal in every returned clause. |
| 431 | `numVars_le_of_literal_bounds` | A common upper bound for all variable-index successors bounds `numVars`. |

`DNF.lean` adds no declarations. Its clause induction is a local `have` inside
the existing target. Local `have` bindings elsewhere are likewise not new
environment declarations.

## Requested shared lemmas

For a future serial merge, consider promoting the generic maximum-fold upper
bound `foldr_max_le_of_forall` to a shared list utility. This batch keeps its
private copy in `CNF.lean` and a local copy inside
`CNFEncoding.numVars_le_of_literal_bounds`. No shared-file modification is
needed to compile or integrate this batch.

## Verification

The final fresh-tree sweep completed successfully at result commit
`aebe3d9b6f81b93767c168746e2f0aa53d8acb46`: **53/53 modules passed,
zero `error:` lines, and 52 expected out-of-scope admission warnings**.
The axiom prints below were run against that same fresh output tree.

The patch was replayed in a clean local checkout of the base. Its resulting
Git tree exactly matches the result commit, and all three packaged source
files match that replay byte-for-byte. Bundle verification passed. The
original working tree is clean. Full evidence is in `verification/`.

The admission inventory decreases from 59 to 52, exactly the seven assigned
targets. Every remaining admission is outside the owned files. The source
freeze script also checks the ordered public declaration list, its multiset,
unchanged definition bodies, preservation of original block comments, and the
absence of admissions or new unsafe/axiom mechanisms in the owned files.

Scoped style lint reports **0 FAIL, 0 WARN**. Its displayed private-declaration
count omits the `private noncomputable def` because of its matcher order; the
dedicated source inventory correctly records all 18 additions.

The initial cache setup was narrowed to the campaign's direct Mathlib imports
and their dependency closure. A shared-cache temporary-file conflict was
resolved by using a private cache directory; the final cache operation
completed successfully. Bootstrap and final verification use the repository's
`lean_check_tree.sh`, which removes each old output and checks exit status,
error diagnostics, and the existence of a fresh output. The final sweep uses
a separate initially absent output tree.

### Actual axiom footprints

```text
'Complexity.eval_congr_of_lt_numVars' depends on axioms: [propext, Quot.sound]
'Complexity.exists_cnf_boolFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Std.Sat.CNF.parse_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.decode_serialize' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.numVars_decode_le' depends on axioms: [propext, Quot.sound]
'Std.Sat.CNF.evalDNF_dual' does not depend on any axioms
'Std.Sat.CNF.dnfTautology_dual_iff' depends on axioms: [propext, Quot.sound]
```

### Final sweep tail

```text
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
PASS TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
PASS TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
PASS TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
MODULES_PASSED 53
END_UTC 2026-10-02T20:16:52Z
```

## Escalations

**E1 — exact axiom-list wording.** The brief says to expect exactly
`[propext, Classical.choice, Quot.sound]` for every target. Only
`exists_cnf_boolFun` needs all three. Five targets need only `propext` and
`Quot.sound`; `evalDNF_dual` is axiom-free. Thus all seven use **only** the
permitted standard axioms, and none uses `sorryAx`, but six do not meet the
literal exact-list expectation. The raw output is preserved. Maintainer
disposition requested: accept subsets of the standard triple for this gate.
No proof was padded with unused axiom dependencies to manufacture the list.

There are no mathematical or statement-freeze escalations. The working-branch
change above follows the user's direct instruction and requires no additional
permission.

## Contents and integration

- Full modified sources appear at their repository-relative paths.
- `patches/0001-Fill-Chapter-2-epoch-1-batch-D-formula-proofs.patch` is the
  complete one-commit series against the pinned base.
- `fill-ch2-e1-D.bundle` contains the result branch and requires the pinned base.
- `verification/` contains the final sweep, axiom output and print source,
  frozen module order, style/freeze checks, environment record, and delivery
  verification evidence.
- `SHA256SUMS` covers every other archive member.

From the extracted archive, run `sha256sum -c SHA256SUMS`. In a clean integration
checkout containing the pinned base, use `git bundle verify` on the bundle
and `git am -3` on the patch. The supplied sources must match the resulting
files. Run `verification/final_sweep.sh` from that repository root after cache
setup; it intentionally requires an absent final-output directory.
