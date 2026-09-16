/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassP.Examples

/-!
# Complexity — DTIME and the class P

Deterministic time-bounded computation and the class `P`, following [AB09, §1.3, §1.6]
(see `AroraBarakChapter1Plan.md` for the chapter-level plan).

## Contents

* `DTIME` — deciding a language within a time bound; the classes `DTIME T`
  [AB09, Definition 1.12].
* `TimeConstructible` — time-constructible functions [AB09, §1.3].
* `P` — the class `P` [AB09, Definition 1.13] and basic membership lemmas.
* `Examples` — the palindrome language is in `DTIME (n + 1)` and in `P`
  [AB09, Examples 1.1, 1.4].
-/
