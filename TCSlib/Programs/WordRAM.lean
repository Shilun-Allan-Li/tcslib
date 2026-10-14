/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.WordRAM.Basic
import TCSlib.Programs.WordRAM.Extended
import TCSlib.Programs.WordRAM.Steps

/-!
# Programs: the word RAM

The word RAM of [AFM26]: its nine instructions, runs, and the facts about runs that compiled code needs; and its extension by input, output, coins and halving, with footprints (`Extended`, not vendored).

## Contents

* `TCSlib.Programs.WordRAM.Basic`: The word RAM
* `TCSlib.Programs.WordRAM.Extended`: The extended word RAM: input, output, coins and halving; footprints and halting
* `TCSlib.Programs.WordRAM.Steps`: Running the word RAM: words, steps, pieces of code, straight-line code, branches

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of the vendored files (see each file's header and the repository NOTICE).
-/
