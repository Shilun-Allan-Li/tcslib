# Canonical seal correction

The first complete SpecialEncryptionSecurity A seals (both strict and coe) found two
implicit reductions in specialScheme_wrongKey's local hk/hr facts. Their raw logs and
captured sources are retained under evidence/logs/seals-final/.

The proof previously relied on simpa matching the published coin-preservation reader's
explicit equivalence against a local alias. In the unsealed environment simplification
could reduce the imported coin maps; sealing blocked that hidden route. Adding only the
local alias ek or er to the simp list makes the equivalence and its inverse syntactically
match Equiv.apply_symm_apply. No foreign definition is explicitly unfolded and no statement
or frozen file changes. The fix is local proof commit 9c09f4471.

The four probes for that already-completed file were regenerated at its verified import
boundary; other running or pending probes were left untouched. The first regeneration
attempt stopped at a guard because the import boundary was 12 lines, not the assumed 5;
no probe was rewritten before that assertion. The corrected script derives the boundary
from the source imports. The diagnostic analyzer now reads each runner's captured source,
so original logs retain their exact original source even after probe regeneration.

The correction phase checks the source unsealed and reruns all four whole-file variants.
Its results supersede the original four results in the final matrix; the historical
failures remain delivered and are not presented as passing checks.

The full matrix also found the same local-alias mismatch in WrongKey's prefix-test coin
map eD (source line 125). The analogous explicit local eD expansion fixes it using only
NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn and Equiv.apply_symm_apply. The correction batch
therefore recompiles both affected source modules and reruns all eight whole-file variants.
All original diagnostics and source snapshots are retained.
