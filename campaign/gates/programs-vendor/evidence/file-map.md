# Vendored files: upstream → tcslib

Upstream: anthropics/formal-math, folder `3sum-apsp`, commit e1a4e6508154ea59f030480661590a9fe3018011. "Changed lines" counts diff lines other than the module-system lines, imports, the standard options and the vendoring header; they are the renames, the `## References` sections, the proof repairs and the word-RAM trim, each listed in the file's header.

| Upstream file | Vendored file | Lines (upstream → vendored) | Changed lines outside the header and imports |
|---|---|---|---|
| `ThreeSumApsp/Lang/Syntax.lean` | `TCSlib/Programs/Light/Syntax.lean` | 164 → 181 | 3 |
| `EndStatement.lean` | `TCSlib/Programs/WordRAM/Basic.lean` | 139 → 73 | 89 |
| `ThreeSumApsp/Util/Basic.lean` | `TCSlib/Programs/Util/Basic.lean` | 24 → 40 | 2 |
| `ThreeSumApsp/Machine/Steps.lean` | `TCSlib/Programs/WordRAM/Steps.lean` | 419 → 437 | 9 |
| `ThreeSumApsp/Lang/Compiler/StatementCode.lean` | `TCSlib/Programs/Light/Compiler/StatementCode.lean` | 364 → 382 | 5 |
| `ThreeSumApsp/Lang/Compiler/Cells.lean` | `TCSlib/Programs/Light/Compiler/Cells.lean` | 335 → 357 | 10 |
| `ThreeSumApsp/Lang/Compiler/Expressions.lean` | `TCSlib/Programs/Light/Compiler/Expressions.lean` | 166 → 184 | 5 |
| `ThreeSumApsp/Util/List.lean` | `TCSlib/Programs/Util/List.lean` | 476 → 497 | 9 |
| `ThreeSumApsp/Lang/RunsStayInLimits.lean` | `TCSlib/Programs/Light/RunsStayInLimits.lean` | 97 → 115 | 5 |
| `ThreeSumApsp/Lang/Compiler/Conditions.lean` | `TCSlib/Programs/Light/Compiler/Conditions.lean` | 148 → 166 | 7 |
| `ThreeSumApsp/Lang/Compiler/CallFrames.lean` | `TCSlib/Programs/Light/Compiler/CallFrames.lean` | 151 → 170 | 7 |
| `ThreeSumApsp/Lang/Compiler/Dispatcher.lean` | `TCSlib/Programs/Light/Compiler/Dispatcher.lean` | 96 → 114 | 7 |
| `ThreeSumApsp/Lang/Compiler/Simulation.lean` | `TCSlib/Programs/Light/Compiler/Simulation.lean` | 479 → 497 | 7 |
| `ThreeSumApsp/Lang/Compiler/ProgramCode.lean` | `TCSlib/Programs/Light/Compiler/ProgramCode.lean` | 259 → 277 | 7 |
| `ThreeSumApsp/Lang/Compiler/StartUp.lean` | `TCSlib/Programs/Light/Compiler/StartUp.lean` | 255 → 273 | 5 |
| `ThreeSumApsp/Lang/Compiler/WholeProgram.lean` | `TCSlib/Programs/Light/Compiler/WholeProgram.lean` | 265 → 283 | 7 |
| `ThreeSumApsp/Lang/Logic.lean` | `TCSlib/Programs/Light/Logic.lean` | 285 → 302 | 3 |
| `ThreeSumApsp/Lang/Assigns.lean` | `TCSlib/Programs/Light/Assigns.lean` | 68 → 85 | 3 |
| `ThreeSumApsp/Lang/Rules.lean` | `TCSlib/Programs/Light/Rules.lean` | 365 → 382 | 3 |
| `ThreeSumApsp/Lang/Frames.lean` | `TCSlib/Programs/Light/Frames.lean` | 390 → 407 | 3 |
| `ThreeSumApsp/Lang/Calls.lean` | `TCSlib/Programs/Light/Calls.lean` | 129 → 146 | 3 |
| `ThreeSumApsp/Lang/Tactics.lean` | `TCSlib/Programs/Light/Tactics.lean` | 174 → 197 | 12 |
| `ThreeSumApsp/Lang/Regions.lean` | `TCSlib/Programs/Light/Regions.lean` | 210 → 227 | 3 |
| `ThreeSumApsp/Util/Index.lean` | `TCSlib/Programs/Util/Index.lean` | 116 → 135 | 3 |
| `ThreeSumApsp/Lang/Lib/Seg.lean` | `TCSlib/Programs/Light/Lib/Seg.lean` | 235 → 253 | 5 |
| `ThreeSumApsp/Lang/Lib/ArrayAt.lean` | `TCSlib/Programs/Light/Lib/ArrayAt.lean` | 142 → 160 | 5 |
| `ThreeSumApsp/Lang/Lib/Pass.lean` | `TCSlib/Programs/Light/Lib/Pass.lean` | 71 → 88 | 3 |
| `ThreeSumApsp/Lang/Lib/Copy.lean` | `TCSlib/Programs/Light/Lib/Copy.lean` | 87 → 104 | 3 |
| `ThreeSumApsp/Util/CountingSort.lean` | `TCSlib/Programs/Util/CountingSort.lean` | 130 → 148 | 7 |
| `ThreeSumApsp/Lang/Lib/CountSort.lean` | `TCSlib/Programs/Light/Lib/CountSort.lean` | 500 → 520 | 6 |
| `ThreeSumApsp/Lang/Lib/Emod.lean` | `TCSlib/Programs/Light/Lib/Emod.lean` | 268 → 289 | 5 |
| `ThreeSumApsp/Lang/Lib/Logs.lean` | `TCSlib/Programs/Light/Lib/Logs.lean` | 273 → 294 | 5 |
| `ThreeSumApsp/Lang/Lib/Merge.lean` | `TCSlib/Programs/Light/Lib/Merge.lean` | 198 → 215 | 3 |
| `ThreeSumApsp/Lang/Lib/MergeSort.lean` | `TCSlib/Programs/Light/Lib/MergeSort.lean` | 221 → 240 | 3 |
| `ThreeSumApsp/Lang/Lib/NextPair.lean` | `TCSlib/Programs/Light/Lib/NextPair.lean` | 73 → 90 | 3 |
| `ThreeSumApsp/Util/Odometer.lean` | `TCSlib/Programs/Util/Odometer.lean` | 66 → 84 | 7 |
| `ThreeSumApsp/Lang/Lib/Odometer.lean` | `TCSlib/Programs/Light/Lib/Odometer.lean` | 82 → 100 | 15 |
| `ThreeSumApsp/Lang/Lib/PowTable.lean` | `TCSlib/Programs/Light/Lib/PowTable.lean` | 115 → 132 | 3 |
| `ThreeSumApsp/Util/StablePass.lean` | `TCSlib/Programs/Util/StablePass.lean` | 101 → 119 | 7 |
| `ThreeSumApsp/Lang/Lib/RadixPass.lean` | `TCSlib/Programs/Light/Lib/RadixPass.lean` | 180 → 198 | 5 |
| `ThreeSumApsp/Lang/Lib/Sqrt.lean` | `TCSlib/Programs/Light/Lib/Sqrt.lean` | 79 → 98 | 4 |
