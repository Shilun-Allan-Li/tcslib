#!/usr/bin/env bash
# C11 duplication searches (gsw-6b-u15-u17): rg over TCSlib (and Mathlib where named) at the head,
# with hit counts. usage: searches.sh OUT
cd /workspace/gsw2/repo
M=.lake/packages/mathlib/Mathlib
run() { local title=$1; shift; local hits; hits=$("$@" 2>/dev/null); echo "=== $title :: ${*}"; echo "hits: $(printf '%s' "$hits" | grep -c . )"; printf '%s\n' "$hits" | head -40; echo; }
{
run "evk-free view, fheView projections" rg -n 'fheView|noEvk' TCSlib
run "phase-5 bound and its users" rg -n 'distAdv_encrypt_le' TCSlib
run "leveled hybrids" rg -n 'levelHybrid|leveledView|levelReduction|challengeDist' TCSlib --glob '!**/GSW/LeveledSecurity.lean'
run "position hybrids / planting over a seed tuple" rg -n 'theorem (distAdv_multi_le_sum|distAdv_tuple_le_sum|acceptProb_plant|acceptProb_update|uprob_update)' TCSlib
run "marginalization lemmas" rg -n 'theorem (acceptProb_fst|acceptProb_snd|uprob_fst|acceptProb_coins_fst|uexp_fst)' TCSlib
run "averaging pointwise-close functions" rg -n 'theorem (abs_uexp_sub_le|abs_uexp_le_uexp_abs|exists_abs_uexp_le|exists_abs_uexp_sub_le|uexp_sub)' TCSlib
run "acceptance as an average of sections" rg -n 'theorem (acceptProb_eq_uexp|acceptProb_eq_uexp_sections|acceptProb_eq_uexp_fst|exists_fixSeed)' TCSlib
run "uniform-key statistical step and its users" rg -n 'uniformKey_uniform_advantage_le|real_uniformKey_advantage' TCSlib
run "telescoping hybrid argument users" rg -n 'abs_sub_le_sum_hybrids' TCSlib
run "key-seed planting by Function.update in a seed tuple (Regev / Lossy / GSW)" rg -n 'Function.update .*keygen|update .* e.succ|update .* 0 k' TCSlib/Cryptography
run "N - 1 + 1 index casts" rg -n 'Nat.sub_one_add_one' TCSlib
run "Mathlib: averaging a pointwise bound" rg -n 'theorem abs_sum_le_sum_abs|theorem sum_le_card_nsmul' $M/Algebra/Order/BigOperators/Group/Finset.lean
} > "$1"
grep -c '^===' "$1"
