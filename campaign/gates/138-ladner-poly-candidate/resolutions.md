# Gate 138 resolutions for #320

Round 1 audited `fc72e67b25e79231fbb04a324d9978d9e9f00349` and returned **CLEAR (0 blockers,
0 majors, 1 minor, 11 notes)**, recorded verbatim as `findings.md` (SHA-256 `aa823bd0ca3a975f4e9a4388b24ce8f7f3ec31075888e8a48a0ef0dbb12a0086`).

| Finding | Resolution |
| --- | --- |
| G138-01 · four pairs mislabelled `helper-citation` (minor) | **Fixed in the records.** The classifier now gives `helper-citation` only when one endpoint's text names the helper (`evidence/fixes/dispositions.py.txt`). Rerun on the same screens, it changes exactly the four flagged directed pairs, in both populations, to `fp-idiom`: `ladner_pad_guard_FP` / `ladner_index_lt_loglog_FP` (both directions), `ladner_query_preparation` / `ladner_index_lt_loglog_FP` and `ladner_wordVerdict_FP` / `ladner_index_lt_loglog_FP`. Pair lists, counts and reproduced-character totals are unchanged. `evidence/PAIR-DISPOSITIONS.json` is replaced; the carrier keeps the audited version. |

Notes N1 to N11 need no action. **Gate 138 is clear to merge.** Seyoon merges #320. The replay output `oleans-cl138-cfe8a` (876 objects)
becomes the campaign snapshot if the merge commit's tree equals the prospective tree `f46a0aed394a55192e1f6555c90a135f1d537cf5` outside `campaign/`.
