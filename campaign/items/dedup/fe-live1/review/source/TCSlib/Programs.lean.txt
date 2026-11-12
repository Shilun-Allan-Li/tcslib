/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Compat
import TCSlib.Programs.Util
import TCSlib.Programs.WordRAM
import TCSlib.Programs.Light
import TCSlib.Programs.Util.Basic
import TCSlib.Programs.Util.CountingSort
import TCSlib.Programs.Util.Index
import TCSlib.Programs.Util.List
import TCSlib.Programs.Util.Odometer
import TCSlib.Programs.Util.StablePass
import TCSlib.Programs.WordRAM.Basic
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Programs.WordRAM.Steps
import TCSlib.Programs.Light.Assigns
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Compiler.CallFrames
import TCSlib.Programs.Light.Compiler.Cells
import TCSlib.Programs.Light.Compiler.Conditions
import TCSlib.Programs.Light.Compiler.Dispatcher
import TCSlib.Programs.Light.Compiler.Expressions
import TCSlib.Programs.Light.Compiler.ProgramCode
import TCSlib.Programs.Light.Compiler.Simulation
import TCSlib.Programs.Light.Compiler.StartUp
import TCSlib.Programs.Light.Compiler.StatementCode
import TCSlib.Programs.Light.Compiler.WholeProgram
import TCSlib.Programs.Light.Frames
import TCSlib.Programs.Light.Lib.ArrayAt
import TCSlib.Programs.Light.Lib.Copy
import TCSlib.Programs.Light.Lib.CountSort
import TCSlib.Programs.Light.Lib.Emod
import TCSlib.Programs.Light.Lib.Logs
import TCSlib.Programs.Light.Lib.Merge
import TCSlib.Programs.Light.Lib.MergeSort
import TCSlib.Programs.Light.Lib.NextPair
import TCSlib.Programs.Light.Lib.Odometer
import TCSlib.Programs.Light.Lib.Pass
import TCSlib.Programs.Light.Lib.PowTable
import TCSlib.Programs.Light.Lib.RadixPass
import TCSlib.Programs.Light.Lib.Seg
import TCSlib.Programs.Light.Lib.Sqrt
import TCSlib.Programs.Light.Logic
import TCSlib.Programs.Light.Regions
import TCSlib.Programs.Light.Rules
import TCSlib.Programs.Light.RunsStayInLimits
import TCSlib.Programs.Light.Syntax
import TCSlib.Programs.Light.Tactics

/-!
# Programs

The programming layer (design `machine-library-design.md` §15): the light language and its logic, the word RAM, and the compiler between them, vendored from [AFM26]; and the compatibility names for our Mathlib pin. Every module of the area is imported directly; the topic facades are `TCSlib.Programs.Util`, `TCSlib.Programs.WordRAM` and `TCSlib.Programs.Light`.

## Contents

* `TCSlib.Programs.Compat`: Compatibility names for the vendored programming layer
* `TCSlib.Programs.Util`: Programs: general facts
* `TCSlib.Programs.WordRAM`: Programs: the word RAM
* `TCSlib.Programs.Light`: Programs: the light language
* `TCSlib.Programs.Util.Basic`: What most files use of Mathlib
* `TCSlib.Programs.Util.CountingSort`: The pure side of counting sort
* `TCSlib.Programs.Util.Index`: Index arithmetic: a pair of numbers as one number
* `TCSlib.Programs.Util.List`: Lists: entries with a default, blocks, sums, counting, sorted lists
* `TCSlib.Programs.Util.Odometer`: Counting in base `b` without division: an odometer
* `TCSlib.Programs.Util.StablePass`: One stable pass of a radix sort, on lists
* `TCSlib.Programs.WordRAM.Basic`: The word RAM
* `TCSlib.Programs.WordRAM.Extended`: The extended word RAM: input, output, coins and halving; footprints and halting
* `TCSlib.Programs.WordRAM.Steps`: Running the word RAM: words, steps, pieces of code, straight-line code, branches
* `TCSlib.Programs.Light.Assigns`: A statement changes only the local variables that it assigns
* `TCSlib.Programs.Light.Calls`: Calls
* `TCSlib.Programs.Light.Compiler.CallFrames`: Pieces of a call: the arguments and the new frame
* `TCSlib.Programs.Light.Compiler.Cells`: The cells of the compiled code, and the memories that represent a state
* `TCSlib.Programs.Light.Compiler.Conditions`: The compiler is correct on tests
* `TCSlib.Programs.Light.Compiler.Dispatcher`: The dispatcher
* `TCSlib.Programs.Light.Compiler.Expressions`: The compiler is correct on expressions
* `TCSlib.Programs.Light.Compiler.ProgramCode`: The code of a whole program
* `TCSlib.Programs.Light.Compiler.Simulation`: The compiler is correct on statements: the simulation theorem
* `TCSlib.Programs.Light.Compiler.StartUp`: The start-up code
* `TCSlib.Programs.Light.Compiler.StatementCode`: The compiler from the light language to the word RAM: cells, and the code of statements
* `TCSlib.Programs.Light.Compiler.WholeProgram`: The compiler is correct on whole programs
* `TCSlib.Programs.Light.Frames`: Local variables as a list
* `TCSlib.Programs.Light.Lib.ArrayAt`: Arrays in the memory
* `TCSlib.Programs.Light.Lib.Copy`: Copying and filling a segment
* `TCSlib.Programs.Light.Lib.CountSort`: Counting sort of a list of items by a key that is read through the item
* `TCSlib.Programs.Light.Lib.Emod`: The remainder of a division
* `TCSlib.Programs.Light.Lib.Logs`: Logarithms, the cube root and halves, without division
* `TCSlib.Programs.Light.Lib.Merge`: Merging two segments
* `TCSlib.Programs.Light.Lib.MergeSort`: Merge sort
* `TCSlib.Programs.Light.Lib.NextPair`: From a pair to the next pair
* `TCSlib.Programs.Light.Lib.Odometer`: An odometer in the memory
* `TCSlib.Programs.Light.Lib.Pass`: A pass over an array
* `TCSlib.Programs.Light.Lib.PowTable`: Tables of powers
* `TCSlib.Programs.Light.Lib.RadixPass`: One pass of a radix sort on a list of indices
* `TCSlib.Programs.Light.Lib.Seg`: Segments of the memory
* `TCSlib.Programs.Light.Lib.Sqrt`: The integer square root by counting up
* `TCSlib.Programs.Light.Logic`: Proof rules for the light language
* `TCSlib.Programs.Light.Regions`: Regions of the memory, and the cells that a step leaves alone
* `TCSlib.Programs.Light.Rules`: Derived rules: time that is not typed, blocks, counting loops
* `TCSlib.Programs.Light.RunsStayInLimits`: Runs stay within their limits
* `TCSlib.Programs.Light.Syntax`: The light language
* `TCSlib.Programs.Light.Tactics`: Tactics for proofs about programs

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of the vendored files (see each file's header and the repository NOTICE).
-/
