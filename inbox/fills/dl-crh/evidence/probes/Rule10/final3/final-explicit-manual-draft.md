# Final3 explicit-list source review draft

Status: source review rebound and repaired blocks inspected; native final3
kind/home review remains pending. No final3 native clearance is issued here.
No Lean or Lake process was run for this review, and no Lean source was edited.
Final2 artifacts are unchanged.

The proof commit is `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`. The final3
scan-plan SHA-256 is
`5a2301b66d344357afdbc6173db92d5c0255baad1d034ea67058109217ebcffa`.
The source-bound 595-row draft is `final-explicit-manual-draft.json`, SHA-256
`e129c1d038ac0c2ad0c3c6f281d056b256a3e0be6b9e46b8775b9eaaab5edda8`.
It records exact owner-source hashes and the final3 snapshot hash.

## Rebinding method

Every final3 item is matched to one reviewed final2 occurrence by exact source
path, declaration name, item text, and head. Repeated identical items inside a
declaration use their within-declaration occurrence order. Line numbers and
tactic-line positions are not identities. The materializer rejects unmatched
or extra items and verifies that the only changed declaration bodies are the
three repaired proofs listed below.

All 595 occurrences are accounted for: 383 NEW, 4 CHANGED, and 208 SAME.
The reader multiset is unchanged. Fifteen occurrences move within the two
staged simplifier proofs; the JSON records `previous_review_row_id` for each
row rather than assuming the old numeric ID still identifies it. In particular,
the `hw.dlW_eq` occurrence formerly at row 573 is now row 568.

The previous native disposition and expected exact constant identity are
retained for comparison, but every global still requires the fresh native
final3 table. No old native or source hash is presented as a final3 check.

The exact materializer is
`evidence/tools/manual_explicit_review_final3_draft.py`, run as
`python3 -I evidence/tools/manual_explicit_review_final3_draft.py --write`.

## Explicitly inspected repaired blocks

### `Reduction.collisionPost_split`

The previous final2 `hword` proof used dependent simplification of the padding
width. The new proof first establishes only
`width.eval u.length = (n + 1) + (n + 1)` using local `width` and `u` lets plus
the public `List.length_replicate` and `PolyExpr.eval_add/var/const` equations.
These remain the six explicit-list items at rows 360–365; their context is now
a natural-number equality and their tactic changes from `simpa` to `simp`.

The new `congrArg` transports the entire value of the nondependent function
`fun k : ℕ => List.ofFn (padFin k raw)`, then composes with the exact public
`ofFn_padFin_eq_padStr` reader. It does not simplify the body of `padFin`, add
a foreign reader, or create a new explicit-list item. The remaining proof steps
are preserved. This directly implements the static repair described in
`evidence/Reduction-padding-seal-repair.md`.

The final3 Reduction source SHA-256 is
`27e4d37dc581ff2db70336b8b19ce3a92531de09c0e42ff260a9ffd4685b04c6`.

### `dlHash_compresses`

The same reader items are split into two explicit `simp only` calls. The first
reads `inDom`, `inRange`, `hash`, and evaluator fields, projects the key, and
uses `decide_eq_true_eq`. The second evaluates the domain/range length fields
through their published polynomial equations. There is no new symbol or body
read; the staged order avoids dependent dimension transport before the key/value
readers have applied. Rows 545–551 are remapped by their exact reader items.

### `dlHash_collision_accept_eq`

The first simplifier call reads the raw collision predicate, domain/hash/eval
fields, key projection, Boolean decision equation, and the published
well-formed-width theorem. The second evaluates the length fields and their
polynomial constructor equations. Again the reader multiset is unchanged.
Rows 566–573 are remapped by exact reader item, including the moved dot-notation
width theorem. No foreign definition is added to a simplifier list.

The final3 owned-module source SHA-256 is
`9d500a96e0e112a092ec0f2e548c5a648752dba89faa4bee40272ef55fcf78d0`.
The other six reviewed owner/provider source hashes are unchanged.

## Next required step

After final3's native scan is available, confirm each row's kind/home and
re-dispose every raw foreign-definition candidate and scanner-open item.
The prior four `reduceIte` simproc dispositions and pinned Lean implementation
evidence remain relevant comparison material; they must be bound to the fresh
final3 native log and plan rather than copied as an unsupported clearance.

The draft preserves the distinction between explicit-list review and implicit
dependency seals. Final2's complete explicit-list review remains valid only
for its own snapshot, which had later-discovered implicit dependent-transport
seal failures. Final3's repaired source and full validation results need their
own final report provenance.
