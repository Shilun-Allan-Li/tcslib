# Scope request: reuse ordered emission

Request (2026-11-15): allow the following one-line import in the new file
`TCSlib/Cryptography/SecureComputation/Yao/HybridProof/Garbling.lean`:

```diff
+import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
```

Reason: `TCSlib.Cryptography.ColMachines.polyTimeComputable_flatMap_range`, at
`ThreeColoring/Machines.lean:159`, is an existing proved public generic lemma exactly matching
ordered message-list construction. It is outside the issued order. The brief's helper-import
scope requires a request for any such import, and its duplication rule forbids silently
re-proving this public result. No frozen source file would change. Approval entails computing
the added import closure, extending the single-module bootstrap, and fetching only any newly
needed Mathlib roots. The lighter `FormulaKit.Emit` counterpart is admitted at the issue base
and would introduce an impermissible admission dependency.

Question sent via request_user_input_async:
Scope request: may the new garbling helper import
`TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines` to reuse its proved
`ColMachines.polyTimeComputable_flatMap_range`? This module is outside the issued order;
reuse avoids re-proving an existing public loop lemma. I would extend the narrowed bootstrap
and roots for this import.

User answer (verbatim): "Approve the extra helper import". Approved 2026-11-15.
