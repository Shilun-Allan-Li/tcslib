# New-section argument inspection

The approved source additions were read in the frozen five-file diff and checked again
against exact Git blobs before making the guarded copies. This inspection concerns only
the additions, not unchanged legacy tactics.

| Addition | New proof/command arguments |
| --- | --- |
| `CodeTM.toFinTM_eq` | `rfl`, reading its same-home definition; structure projections are reducible abbreviations. |
| Ten left/right field readers | Exact owner-local `simps` commands, explicit five projections, `isSimp := false`. |
| `branchTM_k`, `branchTM_State` | `rfl`, reading the same-home branch constructor. |
| `branchTM_runFrom_independent` | `rw` names only the published same-home shape equations and `MultiTapeTM.agreeOn_iff`; the run is transferred by the public `runFrom_eq_of_agreeOn`. Its inner `rfl` compares identical same-home tables. |
| Five capture field readers | Exact owner-local `simps` command with `isSimp := false`; the foreign `bufferTape` stays sealed in the successful owner probe. |
| Four zero-space facts | Exact application of the public `spaceUsed_zero_tapes_eq_zero`; the premise's `rfl` reads only the same-home canonical machine's tape count. |

No other-file TCSlib definition is supplied to a new `simp`, `rw`, `unfold`, `dsimp`,
`show`, or `change` argument. In particular, `runFrom`, `spaceUsed`, and `bufferTape` are
not unfolded by these additions. The only `simps` targets are the three owner-local
configuration definitions whose fields the user approved.

The successful published-consumer probe rewrites only actual API theorem names, or
uses the actual reader theorem directly. Its probe-local `branchView` may reduce; all
16 ordinary foreign definitions in its seal set remain irreducible. No production
consumer uses a foreign-definition `rfl` or passes such a definition to a tactic.

Definitions named in guard/attribute instrumentation and in the intentional negative
controls are part of the test mechanism, not production proof-unfolding arguments.
