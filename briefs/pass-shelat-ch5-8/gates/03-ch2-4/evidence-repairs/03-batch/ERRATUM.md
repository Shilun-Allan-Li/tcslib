# Erratum (2026-11-06): two tool faults in this evidence, found by the delta audits

Both faults are in the maintainer's evidence tools, not in the Lean code. Neither changes a
conclusion of the batch's attestation.

1. **`statements.txt`, `Turing.ModuleHost.Clean.envelope` (gate 03l round 3, minor 2).** The
   extractor (`decls.py`) stopped at the next line starting with `|`, meant to catch a
   pattern-matching arm, so a conclusion starting with an absolute-value bar was cut. Now it
   stops only at an arm (`| … =>`). The output is regenerated over the same 21 files, base
   `092083cd10be7a284db4e97fcf42eddb8296edf7`, head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`:
   the same 12 rows with the same names and classes; only this entry's text changes. The full entry:

   `theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ} (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) : |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤ (B arg.length : ℤ)`

   The tool is `decls-fixed.py.txt`, and its output is `decls-fixed.tsv`.
2. **`axioms.log`, the count "548 names" (gate 03f1 round 2, note R2-7; gate 03e round 3).** The
   comparator (`axcmp.py`) read names up to the first apostrophe, so
   `TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic'` merged with its unprimed namesake;
   both are standard. Now it reads whole lines. Re-run over the same outputs
   (`axcmp-fixed.out`): **549 prints at the head and 539 at the base, 10 new, 0 changed axiom
   sets, 0 missing, `sorryAx` in 100 at both, no other non-standard axiom.**

The fixed tools replace the old ones in the maintainer's tool set for later rounds.
