# Gate 95's copy-text screen at round 3's head (`bbf69680`)

- **Script:** round 2's, unchanged: the bundled `copy-text-screen-v3-nf-pairs.py`
  (`../../screen/screen-nf-pairs.py.txt` less its two comment lines), the v3 screen restricted to
  pairs with an `NDNormalForm` declaration on one side.
- **Population:** round 2's 23 files (`population.txt`, with `BufferWords`).
- **Root:** `git archive bbf69680 -- TCSlib`, a frozen copy. The head is #191's round-3 head, on
  the campaign after #196 (so `Build/Contract/Basic` has #197's `Contract.zero`).
- **Run:** `nice -n 10 python3 -I copy-text-screen-v3-nf-pairs.py <root> $(cat population.txt)`,
  under the screen lock. Exit 0, 174 s (`status.txt`).

## Result

| Run | Commit | Declarations | Pairs | Characters |
|---|---|---|---|---|
| round 2, repaired head | `10c01517` | 1,444 | 13 | 5,191 |
| **round 3** | `bbf69680` | **1,446** | **13** | **5,191** |

- `pairdiff.py` against round 2's run (`pairdiff-r2.txt`): head pairs 13, new 0, gone 0. The 13
  pair lines are byte-identical to round 2's.
- **The two new screened declarations** (`decls-r2.tsv` at round 2's head `ac934f99` against
  `decls-r3.tsv`, by `decl-list.py`, v3's own extraction): `nf_update_last` (184 characters, the
  shared prefix-array completion) and `Turing.Contract.zero` (#197, 214). Neither is in a pair.
  `Segment.zero`'s label is now qualified, because `Contract.zero` shares its short name.
- **The sweep's declarations** are all shorter, by 30 to 120 characters each; `nf_sweep_record`
  (626 → 279) and `nf_prefix_last` (442 → 208) lost the shared proof to `nf_update_last`.
  `nf_display_prefix_length` stays under the 60-character cut-off. None of them is in a pair, at
  either head.
