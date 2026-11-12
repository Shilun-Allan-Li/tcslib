# Gate 129 round 3 dispositions

The verbatim round 3 return has SHA-256
d1ccbff62772e37edfd7cb89e14736846c76b35d86c84a59c0ae740eeac39527. It audited ead826bc6b1900c4209717aafc14244745106d7d.
The updated #251 source is 39dfa843b02ae7fdd0acaeacfadf5bba17a60feb.

| Finding | Current disposition |
|---|---|
| 1 | Primitives uses published one-step run, live-step, action and state-map equations. Its fixed-pair donor uses `pairEncode_eq`. The split startup and restore cite the approved word-seam equation. The expanded check covers the complete affected proofs. |
| 2 | The left, right and buffered embeddings compare reads by rewriting through `bufferTape_inputSymbol` and using equality of the input positions. The existing buffer definition and supporting lemmas retain their source text and move before the first two consumers in Simulation. |
| 3 | The whole-input copy specializes `scanCopy_suffix`. Five further zero-tape callers share the existing right-moving step. The replay, rewind and additional matching polynomial and capture cases cite the no-write proof for an outer `none`. Erase rows retain outer `some none`. |
| 4 | The round 3 forward eraser specialization is retained. Its later erase pass is covered separately. |
| 5 | The approved live-copy and aligned-rewind factoring remains. The round 4 re-points reuse the same contracts. |
| 6 | The three earlier readers are unchanged. The approved fourth non-simp reader `Cfg.ofWords_mapState` lives beside the word seam in Convention, with the approved StateRenaming import. The old private Seam proof and the CodeSimulator inline re-derivation are replaced. |
| 7 | Reductions retains its approved import and fixed-prefix donor. Its source is byte-identical to the audited round 3 head. |
| 8 | The round 3 replay is historical. A complete 395-module merged-tree pass was followed by a 141-module replay of the Seam closure from that verified snapshot. The final tree preserves all 65 inherited admissions in unchanged files. |
| 9 | The current freeze, comparison patches and recovery map cover the eight changed owners. The retained machine definitions and the reader statements have the exact source scope stated in the pack. |
| 10 | All 119 complete selected proofs and 70 paired controls passed on exact rebuilt imports. The same 53-file population is compared on both sides. All 220 selected text matches have exact spans and dispositions. |

The external Codex follow-up remains required before gate closure.
