# ZF-B2 continuation: uniform scheme

Task 1 is complete. `exists_effectiveMachineCode2` is proved; its proof is
unchanged from the applied ZF-B patch. Exactly 46 format-independent private
copies were removed. The 24 required two-tape-specific declarations remain.
No speculative simulator or new admitted helper was introduced.

## Scope conflict requiring resolution

`briefs/zone-f1-batchB2.md`, under **Owned file**, permits precisely the
`MathlibBridge` and `Mathlib.Tactic.FinCases` imports and says:
"No other import changes are allowed."

The same brief, under **In-repo proved precedents** and **ZF-B's continuation
frontier**, requires citation of the `Build/VirtualInput.lean` virtual-input
hosts and the `Build/Catalog.lean` administrative machinery. Neither module
belongs to the transitive import closure of `Codes2Tape.lean`. The source
closure is in `codes2-import-closure.txt`; `Axioms.lean` independently queries
the compiled environment and `axioms.log` records that all five sampled
required names are absent.

The narrow requested amendment is to sanction these imports, in the owned file:

```lean
import TCSlib.Complexity.TuringMachine.Build.VirtualInput
import TCSlib.Complexity.TuringMachine.Build.Catalog
```

This is an implementation-scope conflict, not a counterexample to
`exists_uniformMachineCode2`. No import was added without that amendment,
no public declaration was copied to evade it, and no theorem was weakened.
Import permission alone does not complete the simulator: the full finite
controller and its joint polynomial ledger remain to be proved.

## Concrete construction frontier

1. Retain the concrete decoder `zfBDecode` and the canonizer assembled by
   `codePrim_machine zfBCanonical zfBPrimCanonical`; do not choose an opaque
   witness of `exists_effectiveMachineCode2`.
2. Parse `pairEncode (pairEncode (Nat.bits t) α) x`. Keep both the deadline
   and the claimed state count in binary while checking the canonical count
   and the guard `351 * (n + 1) ≤ rest.length`. Only then may state/table
   enumeration begin. A malformed count, record, or suffix selects
   `zfBFallback`. The parser/scanner definitions already put the guard before
   recursion; their primitive-recursive compilation carries no polynomial
   time guarantee and cannot discharge this machine-cost obligation.
3. Host the two coded work tapes on two physical tapes, with administration
   and the buffered virtual input separate. Cite `Turing.vhostEmitTM` or
   `Turing.vhostSilentTM` and their contracts; do not reduce the tape count.
   These names are in namespace `Turing`, not `Turing.FinTM`.
4. Maintain the binary countdown and the append-only output status: empty,
   exactly `[true]`, or permanently other. Inspect the state and output after
   the final permitted transition before timeout. The source-side zero-time
   fact is already public and available:
   `Turing.FinTM.not_computesInTime_zero M x [true]`. Cite it instead of
   re-proving the zero-time impossibility; the simulator must also implement
   its false answer.
5. Prove the positive and negative branches against
   `(zfBDecode α).toFinTM.ComputesInTime x [true] t`. The controller must work
   for malformed encodings, empty payloads, zero deadline, and a halt on
   transition `t`. One coefficient and degree must bound both branches by
   `simDegree * (α.length + x.length + t + 1) ^ simDegree`.
6. When instantiating loop rows, account for their literal types:
   `exists_loopTM` and its space row use `R : ℕ → ℕ`, with fuel
   `Nat.bits (R input.length)` and rounds `0` through `R input.length`.
   The requested deadline depends on input contents, not just their length.
   Do not silently identify these quantities or infer the desired joint
   bound from a length-only exponential envelope. The actual clock and its
   per-input time ledger need their own justified composition.

The one-tape `exists_uniformMachineCode` in
`TCSlib/Complexity/Diagonalization/EXPCOM.lean` is itself sorried at the
recorded base. It is a binding construction sketch, not a proved simulator
that can be specialized. The arbitrary-time `codePrim_machine` theorem
also supplies no substitute for the missing uniform polynomial proof.

## Next delivery checks

Use only `scripts/lean_check_tree.sh` for Lean verification. Keep the 24
retained format-specific declarations unless the maintainer separately
commissions their generalization. Preserve all nine public signatures;
never use or edit `NDCodes.exists_effectiveNDMachineCode`. The completed
uniform target must have no `sorryAx`; the final owned module must then
produce no sorry warnings. Preserve the full joint budget and both verdict
branches.
