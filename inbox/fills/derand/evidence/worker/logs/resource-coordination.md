# Resource coordination

The user explicitly authorized messages to other workers about shared Mac resources.
No mathematical work was delegated and no sub-agents were spawned.

- The narrowed NthRootLemmas cache fetch waited normally for all three slots, then ran for 7.89 seconds and released them.
- At sc-garbles request, only derands two validated Python dispatchers were paused at 10:56:58 UTC. Current native children finished normally; a 12-second acquisition gap ran from 10:57:19 to 10:57:31, and both parents resumed in a finally block.
- At seq-zks request, only the verification Python dispatcher paused from 11:07:34 to 11:08:14. Its current native child finished normally. The other workers cache acquired its slots and finished at 11:11:00; derand started no new main-tree check during that cache window.
- Exact pause/resume events are in courtesy-gap.jsonl and cache-window.jsonl. Every native check still acquired its own issued-wrapper slot; no native Lean or other workers process was signaled.

- Final coordination update: sc-garble reported all Lean/cache work complete. Derand then informed sc-garble and seq-zk that its final 387-module replay and post-check native probes were finished and that no further derand Lean/cache slot use was planned.
