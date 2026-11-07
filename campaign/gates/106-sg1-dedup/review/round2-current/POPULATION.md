# Gate 106 round-two source population

The source freeze, compiled-module census, and both fresh screens use exactly the same nine files, matching the immutable round-one `evidence/current/screen/population-head.txt`. `population.txt` is the machine-readable list. There was no existing gate-local `POPULATION.md`; this records that standing list without changing it.

| File under `TCSlib/Complexity/` | Reason |
| --- | --- |
| `ClassNP/SAT.lean` | Actual cut-guard repair, retained generic adapter/dispatcher families |
| `ClassNP/Tautology.lean` | Original Segment specialization/consumers |
| `CookLevin/Hardness.lean` | Actual cut-guard repair, retained generic adapter/dispatcher families |
| `SpaceComplexity/Machines/Frag.lean` | Original isolated cell-read repair, already merged through NatBits |
| `TuringMachine/Build/Catalog.lean` | Disclosed SafeSegment siblings and pre-existing copied material |
| `TuringMachine/Build/Contract/Basic.lean` | Published Segment definition, equation and composition API |
| `TuringMachine/Build/CounterLoop.lean` | Original Segment specialization/consumers |
| `TuringMachine/Build/Primitives.lean` | Disclosed SafeSegment siblings and pre-existing copied material |
| `TuringMachine/Robustness/SingleTape.lean` | Original Segment specialization/consumers |

Current base: maintainer-supplied `e3adffac67377a8b6e23bed74bfdbb44a123dd86`, records checkout source and complete `oleans-mac3`. Current head: maintainer-supplied `478cd3a8dfb46094b9d8b971662f2ddadb1eccdb`, frozen `wt-sg1` source and complete `oleans-msg4`. This task executes no Git command. `context.json` records these supplied identities plus independently computed body hashes, Git-blob hashes, compiled-module hashes, and original-audit/msg3 body identity.

Every population file is retained verbatim as `base-source/<path>.lean.txt` and `head-source/<path>.lean.txt`. Fresh screens use temporary trees populated from exactly those archived bytes, with their original `.lean` relative paths; screen requests name every input. No incomplete source subset is substituted within the cited population. Full `TCSlib/**/*.lean` path/hash maps independently establish that the five current changed source files all lie in this list.
