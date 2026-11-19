#!/usr/bin/env bash
# C11 duplicate/near-relative searches for gsw-6b-u14-u16: each command with its hit count.
cd /workspace/u1416
B=bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d; H1=$(git rev-parse origin/iO/phase-a-base); H2=$(git rev-parse origin/cleanup/stage2-s2a)
M=.lake/packages
echo "# C11 searches (gsw-6b-u14-u16), $(date -u +%FT%TZ); base $B, iO/phase-a-base $H1, cleanup/stage2-s2a $H2; Mathlib/Batteries/core under $M"
gg() { for rev in $B $H1 $H2; do n=$(git grep -n "$@" $rev -- TCSlib audits | wc -l); echo "git grep -n $* <$rev> -- TCSlib audits: $n lines"; done; }
gl() { n=$(git grep -n "$@" $B -- TCSlib audits | wc -l); echo "git grep -n $* <base> -- TCSlib audits: $n lines"; git grep -n "$@" $B -- TCSlib audits | sed "s/^$B://" | cut -c1-160 | sed 's/^/    /' | head -${LIM:-12}; }
mg() { n=$(grep -rnE "$1" $M --include=*.lean | wc -l); echo "grep -rnE '$1' $M: $n lines"; grep -rnE "$1" $M --include=*.lean | cut -c1-160 | sed 's/^/    /' | head -${LIM:-8}; }
echo "## 1. target and helper names"
for n in encrypts_bootNAND decrypt_fheEval decrypt_fheEvalCircuit decrypt_keygen_fheEvalCircuit bootNoise_le encrypts_leveledEval decrypt_keygen_leveledEvalCircuit encrypts_bootGate four_pow_clog_le; do gg -w $n; done
echo "## 2. shapes of the public helper (a gate step from argument decryptions)"
LIM=20 gl -E 'theorem [a-zA-Z_]*(Gate|gate)[a-zA-Z_]*encrypt|encrypts_[a-zA-Z]*Gate|homGate_encrypts'
gl -E 'IsNAND.*Encrypts|Encrypts.*IsNAND'
gl -E 'decrypt P s \(cts\.getD'
echo "## 3. the runWith_rel pattern (near relatives)"
LIM=20 gl -w runWith_rel
gl -w eval_encrypts
gl -w decrypt_keygen_eval
echo "## 4. G13: 4^clog / 2^clog bounds"
LIM=20 gl -E '\^ Nat\.clog 2 [a-zA-Z(]'
gl -E 'pow_pred_clog_lt_self'
LIM=20 mg 'theorem [a-zA-Z_]*clog[a-zA-Z_]*'
mg 'b \^ clog b [a-z]+ < b \* |pow_clog_lt|pow_clog_le_mul'
echo "## 5. L3 literal ciphertexts and level index"
gl -E 'litInput_castAdd|litInput_natAdd'
gl -E 'Fin\.addCases'
gl -E 'layerNAND_(eval|depth|isLayered|isNANDForm)'
gl -E 'homNot_eq|homAnd_singleton'
echo "## 6. honest-key rewriting (G12)"
gl -E 'LWE\.sample_fst P\.lwe χ'
gl -E 'encrypts_keygen_encrypt'
gl -w encrypts_evalKey
gl -w encrypts_levelKey
