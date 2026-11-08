# Existing-API fixed-shift probe

Checked at frozen Gate06 source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`, Lean4.25.0 and its existing467-module reconciled tree. The exact scratch source is retained as `FixedShift.source.txt` (SHA256 `b2f50194df1be165490330a69c69256bed090caca68944b9834f8fceb148e2a0`). The one-module checker returns0/no diagnostics,1.826 seconds, fresh nonempty object. Its named theorem's axiom print is exactly propext/Classical.choice/Quot.sound, with no sorryAx.

The proof is the previously drafted term `hμ.comp_of_le (fun n => n + s) (fun n => Nat.le_add_right n s)`, importing the existing theorem through `ZeroKnowledge.NP`. No library source, public API, theorem home or Gate06 source pin changed. The optional relocation patch remains unapplied/uncompiled; shifted collections and their correctness/one-wayness transports remain unproved.

The probe is an internal maintainer check, not an issued external gate/fill or a PKE existence theorem. Its scratch module/object remains outside library source/census counts.
