# Inspection table (cp1, commit 07b50af56b0a9a7046a667fd9b6cf33c110f0700)

Every `rw`/`rwa`/`erw`/`nth_rewrite`/`simp`/`simpa`/`simp_all`/`dsimp`/`unfold`/`show`/`change` argument on an added line of `git diff 72fcfbef 07b50af5 -- TCSlib/Complexity/SpaceComplexity/Padding.lean`. Kinds resolved by `Probe/EPadKinds.lean` in `namespace Complexity` with `open Turing`.

| line | tactic | argument | kind |
|---:|---|---|---|
| 93 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 93 | `rw` | `if_pos h` | theorem if_pos (Init.Core) |
| 99 | `rw` | `epadVirt` | own file: def `epadVirt` |
| 99 | `rw` | `if_neg h` | theorem if_neg (Init.Core) |
| 105 | `rw` | `epadVirt_of_valid h` | own file: theorem `epadVirt_of_valid` |
| 106 | `rw` | `epadVirt_of_not_valid h` | own file: theorem `epadVirt_of_not_valid` |
| 116 | `rw` | `pairDecode_pairEncode` | theorem Turing.pairDecode_pairEncode (TCSlib.Complexity.TuringMachine.Encoding) |
| 116 | `rw` | `Option.some.injEq` | theorem Option.some.injEq (Init.Core) |
| 116 | `rw` | `Prod.mk.injEq` | theorem Prod.mk.injEq (Init.Core) |
| 118 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |
| 124 | `rw` | `LogProg.bitsVal_bits` | theorem Complexity.LogProg.bitsVal_bits (TCSlib.Complexity.SpaceComplexity.Machines.Bin) |

Counts by kind (first word): own: 4, theorem: 7
