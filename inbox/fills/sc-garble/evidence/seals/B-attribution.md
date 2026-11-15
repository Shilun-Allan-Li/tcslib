# Complete seal-B attribution

Base A: all 6 files pass strict and coe (12/12). Final A: all 14 files pass strict and
coe (28/28). B has 21 baseline diagnostics per coercion variant in three files, and 30 final
diagnostics per variant in five files. Every B failure is an explicitly attributed
PolyExpr.eval notation conversion. Strict and coe have identical diagnostic declarations;
there is no coercion-sensitive failure difference. All 80 base/final whole-file matrix
entries are complete; corrected runs supersede retained historical failures.

A and B differ only by sealing PolyExpr.eval. The per-error explanations below identify
the actual blocked conversion. All raw diagnostics and captured sources remain delivered.
The detailed inventory lists every declaration in each strict/coe run.

## Final: every diagnostic

### TCSlib/Cryptography/SecureComputation/GarblingSecurity.lean

- `nestedSpecial_wrongKeyBot`, line 73: Frozen PRFOut (var+var) G₁ hypothesis needs Fin ((var+var).eval n) = Fin (n+n).
- `nestedSpecial_wrongKeyBot`, line 76: New spDecStr_wrongKey var G₁ call needs the same output-width conversion. This added body error is separate from the header error.
- `garbling_good_whp`, line 102: Frozen garbling_good_whp PRFOut hypothesis needs the same var+var output-width conversion.

Raw log: `evidence/logs/seals-final/evidence__seals__final__GarblingSecurity_B_coe.log`. The strict counterpart has the same diagnostics.

### TCSlib/Cryptography/SecureComputation/GarblingSecurity/NestedBounds.lean

- `nestedSpecial_wrongKeyBot_of_string_bounds`, line 107: New helper rfl after evaluator/ofFn length readers needs (var+innerLen).eval n = n+innerLen.eval n.

Raw log: `evidence/logs/seals-final/evidence__seals__final__NestedBounds_B_coe.log`. The strict counterpart has the same diagnostics.

### TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity.lean

- `PRFOut`, line 71: Frozen PRFOut field OracleEnsemble.keyed uses the var-sized point domain; Finn versus Fin (var.eval n) no longer reduces.
- `prfOut_var_iff`, line 77: Frozen prfOut_var_iff uses PRFOut var F; its output Fin n needs Fin (var.eval n).
- `specialScheme_multiMessageSecure`, line 200: Frozen scheme multi-message PRFOut (var+var) G hypothesis needs Fin (n+n) as Fin ((var+var).eval n).
- `spDecStr_wrongKey`, line 269: New string-event reader call has G′ output Fin ((var+ℓ).eval n), while the generic reader expects Fin (n+ℓ.eval n). The raw pretty-printer suppresses this length distinction and prints identical-looking predicates.
- `specialScheme_wrongKey`, line 286: Frozen scheme wrong-key PRFOut (var+var) G hypothesis needs the var+var output-width conversion.
- `specialScheme_wrongKey`, line 296: New spDecStr_wrongKey var G call needs Fin (n+n) as Fin ((var+var).eval n).

Raw log: `evidence/logs/seals-final-correction-01/evidence__seals__final__SpecialEncryptionSecurity_B_coe.log`. The strict counterpart has the same diagnostics.

### TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity/WrongKey.lean

- `exists_negligible_prefix_collision`, line 102: New oracle-indistinguishability hypothesis uses keyed var and needs Fin (var.eval n) as its Fin n point domain.
- `exists_negligible_prefix_collision`, line 118: New χ equivalence has its second coordinate Fin (var.eval n) from the uniform test-machine coin API, while the stated coordinate is Fin n.
- `exists_negligible_prefix_collision`, line 124: New hcoins statement applies eD.symm to k : Fin n → Bool; eD expects Fin (var.eval n) → Bool.
- `exists_negligible_prefix_collision`, line 126: The new preservation-reader application repeats that same eD input-width mismatch.
- `exists_negligible_prefix_collision`, line 127: The new χ/φ pointwise equation repeats the same eD input-width mismatch.

Raw log: `evidence/logs/seals-final-correction-01/evidence__seals__final__WrongKey_B_coe.log`. The strict counterpart has the same diagnostics.

### TCSlib/Cryptography/SecureComputation/Yao.lean

- `yaoCoins_eval`, line 281: Frozen yaoCoins_eval rfl needs evaluation of the add/mul polynomial syntax.
- `yaoHybrid`, line 589: Frozen yaoHybrid callA needs calls.eval n = inB.eval n*n.
- `yaoHybrid`, line 590: Frozen yaoHybrid callA body uses the same call-index product conversion.
- `yaoHybrid`, line 591: Frozen yaoHybrid callB uses the same call-index product conversion.
- `yaoHybrid_callA`, line 597: Frozen yaoHybrid_callA reader needs the same call-index conversion.
- `yaoHybrid_callB`, line 605: Frozen yaoHybrid_callB reader needs the same call-index conversion.
- `yaoHybrid_answersB_getD`, line 716: Frozen yaoHybrid_answersB_getD callA hypothesis needs the call-index conversion.
- `yaoHybrid_answersB_getD`, line 717: Frozen yaoHybrid_answersB_getD callB hypothesis needs the call-index conversion.
- `yaoHybrid_answersB_getD`, line 723: Frozen yaoHybrid_answersB_getD callA conclusion needs the call-index conversion.
- `yaoHybrid_answersB_getD`, line 724: Frozen yaoHybrid_answersB_getD callB conclusion needs the call-index conversion.
- `yaoSeed_good_whp`, line 807: The frozen yaoSeed_good_whp PRFOut (var+var) G₁ header needs the n+n output-width conversion; its new body is not reached under B.
- `yaoHybrid_simulators`, line 936: Frozen outside-unit yaoHybrid_simulators PRFOut hypothesis needs the n+n output-width conversion.
- `yaoHybrid_simulators`, line 938: Frozen yaoHybrid_simulators joint-family append needs evaluation of the total output polynomial.
- `yaoHybrid_hbcSecure`, line 960: Frozen yaoHybrid_hbcSecure PRFOut hypothesis needs the n+n output-width conversion.
- `yaoHybrid_hbcSecure`, line 962: Frozen yaoHybrid_hbcSecure joint-family append needs evaluation of the total output polynomial.

Raw log: `evidence/logs/seals-final/evidence__seals__final__Yao_B_coe.log`. The strict counterpart has the same diagnostics.

## Exact base comparison

Base B has four diagnostics in SpecialEncryptionSecurity, two in GarblingSecurity, and
fifteen in Yao per coercion variant. The other three baseline files pass B. These are the
same frozen header/index/polynomial-evaluation conversions identified individually above.
The final additions are two body calls in SpecialEncryptionSecurity, one body call in
GarblingSecurity, five coordinate/hypothesis diagnostics in the new WrongKey helper, and
one length conversion in the new NestedBounds helper: nine added diagnostics per B variant.
All nine are enumerated above; none is summarized merely as a baseline failure.

## Corrected historical A failures

The original SpecialEncryptionSecurity A runs reported two local-alias matching failures;
the original WrongKey A runs reported one. The local ek/er/eD expansions fixed them through
published equivalence readers. Their corrected strict/coe A runs pass. The old B alias
failures disappeared as well. Original logs and exact source snapshots remain under
`evidence/logs/seals-final/`; final selection uses correction-01 and correction-02 where
applicable. This distinction is recorded in correction-notes.md.
