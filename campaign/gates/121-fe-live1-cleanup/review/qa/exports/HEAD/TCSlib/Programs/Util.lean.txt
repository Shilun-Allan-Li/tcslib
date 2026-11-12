/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Util.Basic
import TCSlib.Programs.Util.CountingSort
import TCSlib.Programs.Util.Index
import TCSlib.Programs.Util.List
import TCSlib.Programs.Util.Odometer
import TCSlib.Programs.Util.StablePass

/-!
# Programs: general facts

Lists, sums, digits, indices and counting facts that the language and its routines use.

## Contents

* `TCSlib.Programs.Util.Basic`: What most files use of Mathlib
* `TCSlib.Programs.Util.CountingSort`: The pure side of counting sort
* `TCSlib.Programs.Util.Index`: Index arithmetic: a pair of numbers as one number
* `TCSlib.Programs.Util.List`: Lists: entries with a default, blocks, sums, counting, sorted lists
* `TCSlib.Programs.Util.Odometer`: Counting in base `b` without division: an odometer
* `TCSlib.Programs.Util.StablePass`: One stable pass of a radix sort, on lists

## References

* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: the source of the vendored files (see each file's header and the repository NOTICE).
-/
