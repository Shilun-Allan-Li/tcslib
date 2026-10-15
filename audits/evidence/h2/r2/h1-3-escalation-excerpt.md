# Excerpt: audits/b5a-fill-agent-reports/h1-3-REPORT.md, lines 100-158 (verbatim)
# source sha256 d1d0243904b5f09362b4dbdba77687ba041fe93d89152835f56bbc3d1f6d935d, at campaign commit 1781a230

## Statement freeze, ownership, and escalations

`evidence/ownership-audit.py` reconstructs the base byte for byte by removing only the new
private gap and the flagged appendix and restoring the permitted inherited proof bodies.
It verifies all inherited signatures, definitions, prior docstrings, imports, and all
out-of-scope text exactly. The only changed tracked file is
`TCSlib/Complexity/TuringMachine/CodeSimulator.lean`. No public declaration was added,
renamed, deleted, or re-signed; no import changed. The original headline body and pending tag
are unchanged. The appendix is explicitly flagged **Fill appendix (H1 continuation 2,
partial; complete hosted clock and verdict)**. No other appendix or status text changed.

**Rule-11 escalation:** the requested all-zero style counts conflict with the same rule’s
statement/definition freeze. Fourteen of the 83 inherited over-width lines are in frozen
signatures or definition bodies. The remaining unused-variable warning is the binder `hr`
in the **statement** of `h1Seek_stateStep`, inside its dependent `if`. Removing or renaming it
would change the frozen signature. These items were left unchanged; no linter was disabled
and no statement was altered to satisfy a style count. Continue on the permitted cleanup.
A maintainer must explicitly authorize those protected edits in a later scope if desired.
No false theorem or failing host contract was discovered; there is no request for a new host.

The module header’s status remains inherited and does not describe this new clock phase;
the brief reserves its update for integration. Earlier target appendices remain historical
and are not rewritten; the new flagged appendix records the current frontier.

### Scoped style cleanup

| Measurement in the inherited 98 declarations | Before | After |
|---|---:|---:|
| Lean linter warnings | 67 | 1 (frozen statement binder) |
| Lines longer than 100 characters | 83 | 14 (all frozen) |
| New-helper linter warnings | — | 0 |
| New-helper over-width lines | — | 0 |

Only proof-body lint simplifications and whitespace wrapping were performed. The touched
inherited declarations are:

`h1Unary_step`, `h1Succ_heads`, `h1Action_split`, `h1Skip_run`, `h1Skip_path`, `h1Seek_request`, `h1Seek_many`, `h1Seek_stateStep`, `h1Seek_rank`, `h1Seek_groups`, `h1Seek_observe`, `h1ReadActions_at`, `h1Table_cut`, `h1Seek_lookup`, `h1Unary_read`, `h1Data_stateCell`, `h1Round_prepare`, `h1Buffer_reads`, `h1Round_payload`, `h1Buffer_suffix`, `h1Round_restore`, `h1Round_lookup`, `h1Round_canonical`, `h1Round_effect`.

Protected over-width lines (some declarations have two):

| Declaration | Width |
|---|---:|
| `h1SeekRouter` | 114 |
| `h1SeekRed` | 101 |
| `h1Seek_request` | 101 |
| `h1Table_cut` | 110 |
| `h1RoundPh` | 102 |
| `h1RoundRed` | 103 |
| `h1RoundPh_decidable` | 101 |
| `h1Data_window` | 110 |
| `h1Round_phase` | 104 |
| `h1Round_payload` | 103 |
| `h1Round_payload` | 105 |
| `h1Round_canonical` | 104 |
| `h1RoundRep_entry` | 106 |
| `h1Round_effect` | 104 |

Final file: **5416 lines, 13 public and
199 private declarations**. Base private count: 188. File size is
