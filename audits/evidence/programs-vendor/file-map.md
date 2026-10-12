# Vendored files: upstream → tcslib

Upstream: anthropics/formal-math, folder `3sum-apsp`, commit e1a4e6508154ea59f030480661590a9fe3018011. "Changed lines" counts diff lines other than the module-system lines, imports, the standard options and the vendoring header; they are the renames, the `## References` sections, the proof repairs and the word-RAM trim, each listed in the file's header.

| Upstream file | Vendored file | Lines (upstream → vendored) | Changed lines outside the header and imports |
|---|---|---|---|
| `ThreeSumApsp/Lang/Syntax.lean` | `TCSlib/Programs/Light/Syntax.lean` | 165 → 182 | 3 |
| `EndStatement.lean` | `TCSlib/Programs/WordRAM/Basic.lean` | 140 → 74 | 89 |
| `ThreeSumApsp/Util/Basic.lean` | `TCSlib/Programs/Util/Basic.lean` | 25 → 41 | 2 |
| `ThreeSumApsp/Machine/Steps.lean` | `TCSlib/Programs/WordRAM/Steps.lean` | 420 → 438 | 9 |
| `ThreeSumApsp/Lang/Compiler/StatementCode.lean` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | 365 → 383 | 5 |
| `ThreeSumApsp/Lang/Compiler/Cells.lean` | `TCSlib/Programs/Light/Compiler/Cells.lean` | 336 → 358 | 10 |
| `ThreeSumApsp/Lang/Compiler/Expressions.lean` | `TCSlib/Programs/Light/Compiler/Expressions.lean` | 167 → 185 | 5 |
| `ThreeSumApsp/Util/List.lean` | `TCSlib/Programs/Util/List.lean` | 477 → 498 | 9 |
| `ThreeSumApsp/Lang/RunsStayInLimits.lean` | `TCSlib/Programs/Light/RunsStayInLimits.lean` | 98 → 116 | 5 |
| `ThreeSumApsp/Lang/Compiler/Conditions.lean` | `TCSlib/Programs/Light/Compiler/Conditions.lean` | 149 → 167 | 7 |
| `ThreeSumApsp/Lang/Compiler/CallFrames.lean` | `TCSlib/Programs/Light/Compiler/CallFrames.lean` | 152 → 171 | 7 |
| `ThreeSumApsp/Lang/Compiler/Dispatcher.lean` | `TCSlib/Programs/Light/Compiler/Dispatcher.lean` | 97 → 115 | 7 |
| `ThreeSumApsp/Lang/Compiler/Simulation.lean` | `TCSlib/Programs/Light/Compiler/Simulation.lean` | 480 → 498 | 7 |
| `ThreeSumApsp/Lang/Compiler/ProgramCode.lean` | `TCSlib/Programs/Light/Compiler/ProgramCode.lean` | 260 → 278 | 7 |
| `ThreeSumApsp/Lang/Compiler/StartUp.lean` | `TCSlib/Programs/Light/Compiler/StartUp.lean` | 256 → 274 | 5 |
| `ThreeSumApsp/Lang/Compiler/WholeProgram.lean` | `TCSlib/Programs/Light/Compiler/WholeProgram.lean` | 266 → 284 | 7 |
| `ThreeSumApsp/Lang/Logic.lean` | `TCSlib/Programs/Light/Logic.lean` | 286 → 303 | 3 |
| `ThreeSumApsp/Lang/Assigns.lean` | `TCSlib/Programs/Light/Assigns.lean` | 69 → 86 | 3 |
| `ThreeSumApsp/Lang/Rules.lean` | `TCSlib/Programs/Light/Rules.lean` | 366 → 383 | 3 |
| `ThreeSumApsp/Lang/Frames.lean` | `TCSlib/Programs/Light/Frames.lean` | 391 → 408 | 3 |
| `ThreeSumApsp/Lang/Calls.lean` | `TCSlib/Programs/Light/Calls.lean` | 130 → 147 | 3 |
| `ThreeSumApsp/Lang/Tactics.lean` | `TCSlib/Programs/Light/Tactics.lean` | 175 → 193 | 7 |
| `ThreeSumApsp/Lang/Regions.lean` | `TCSlib/Programs/Light/Regions.lean` | 211 → 228 | 3 |
| `ThreeSumApsp/Util/Index.lean` | `TCSlib/Programs/Util/Index.lean` | 117 → 134 | 3 |
| `ThreeSumApsp/Lang/Lib/Seg.lean` | `TCSlib/Programs/Light/Lib/Seg.lean` | 236 → 254 | 5 |
| `ThreeSumApsp/Lang/Lib/ArrayAt.lean` | `TCSlib/Programs/Light/Lib/ArrayAt.lean` | 143 → 161 | 5 |
| `ThreeSumApsp/Lang/Lib/Pass.lean` | `TCSlib/Programs/Light/Lib/Pass.lean` | 72 → 89 | 3 |
| `ThreeSumApsp/Lang/Lib/Copy.lean` | `TCSlib/Programs/Light/Lib/Copy.lean` | 88 → 105 | 3 |
| `ThreeSumApsp/Util/CountingSort.lean` | `TCSlib/Programs/Util/CountingSort.lean` | 131 → 149 | 7 |
| `ThreeSumApsp/Lang/Lib/CountSort.lean` | `TCSlib/Programs/Light/Lib/CountSort.lean` | 501 → 521 | 6 |
| `ThreeSumApsp/Lang/Lib/Emod.lean` | `TCSlib/Programs/Light/Lib/Emod.lean` | 269 → 290 | 5 |
| `ThreeSumApsp/Lang/Lib/Logs.lean` | `TCSlib/Programs/Light/Lib/Logs.lean` | 274 → 295 | 5 |
| `ThreeSumApsp/Lang/Lib/Merge.lean` | `TCSlib/Programs/Light/Lib/Merge.lean` | 199 → 216 | 3 |
| `ThreeSumApsp/Lang/Lib/MergeSort.lean` | `TCSlib/Programs/Light/Lib/MergeSort.lean` | 222 → 241 | 3 |
| `ThreeSumApsp/Lang/Lib/NextPair.lean` | `TCSlib/Programs/Light/Lib/NextPair.lean` | 74 → 91 | 3 |
| `ThreeSumApsp/Util/Odometer.lean` | `TCSlib/Programs/Util/Odometer.lean` | 67 → 85 | 7 |
| `ThreeSumApsp/Lang/Lib/Odometer.lean` | `TCSlib/Programs/Light/Lib/Odometer.lean` | 83 → 101 | 15 |
| `ThreeSumApsp/Lang/Lib/PowTable.lean` | `TCSlib/Programs/Light/Lib/PowTable.lean` | 116 → 133 | 3 |
| `ThreeSumApsp/Util/StablePass.lean` | `TCSlib/Programs/Util/StablePass.lean` | 102 → 120 | 7 |
| `ThreeSumApsp/Lang/Lib/RadixPass.lean` | `TCSlib/Programs/Light/Lib/RadixPass.lean` | 181 → 199 | 5 |
| `ThreeSumApsp/Lang/Lib/Sqrt.lean` | `TCSlib/Programs/Light/Lib/Sqrt.lean` | 80 → 99 | 4 |
