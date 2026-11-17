#!/usr/bin/env bash
# design_table_check.sh <repo> (bb1-sim-statements, lead): design r1 §2.4's near-relatives table and the
# brief's added rows, each name checked at its file:line at the issue base (git show; OK when the line
# contains the name).
R=$1; B=bdcadd858cbe043e8c41e465a96e81feb1eecda1; C=TCSlib/Cryptography
while IFS='|' read n f l; do got=$(git -C $R show $B:$C/$f 2>/dev/null | sed -n "${l}p")
  case "$got" in *"$n"*) echo "OK   $n $f:$l";; *) echo "MISS $n $f:$l";; esac
done <<'T'
expect_simulate_congr|Games/Hopping.lean|384
simulate_eq_of_abs|Games/Simulate.lean|334
simulate_eq_of_abs_bounded|Games/Simulate.lean|357
expect_simulate_abs|Encryption/PrivateKey/EncryptThenTag/Tools.lean|65
expect_simulate_abs_inv|Encryption/PrivateKey/EncryptThenTag/Tools.lean|88
expect_eq_until_bad|Games/Hopping.lean|201
prob_eq_until_bad|Games/Hopping.lean|252
identical_until_bad|Games/Hopping.lean|306
identical_until_bad_init|Games/Hopping.lean|343
expect_simulate_eager|Games/Hopping.lean|494
expect_simulate_eager|Encryption/PublicKey/OracleSecurity/ChallengeSim.lean|148
expect_simulate_rImpl_eager|Encryption/PublicKey/NonMalleability/Simulation/Hybrid.lean|267
simulate_tapeImpl_congr|Encryption/PrivateKey/EncryptThenTag/Tools.lean|145
expect_simulate_tapeImpl|Encryption/PrivateKey/EncryptThenTag/Tools.lean|167
freshImpl|Encryption/PrivateKey/EncryptThenTag/Tools.lean|116
tapeImpl|Encryption/PrivateKey/EncryptThenTag/Tools.lean|130
simulate_tapeImpl_congr|Encryption/PublicKey/AdaptiveCPA/Hybrid.lean|170
expect_tapeImpl|Encryption/PublicKey/AdaptiveCPA/Hybrid.lean|244
expect_lazyImpl|Encryption/PrivateKey/OracleFromPRF/Lazy.lean|351
expect_ettImpl_lazy|Encryption/PrivateKey/EncryptThenTag/Lazy.lean|499
expect_ettLazyTape|Encryption/PrivateKey/EncryptThenTag/Lazy.lean|461
simulate_eImpl_congr|Encryption/PrivateKey/OracleFromPRF/Games.lean|199
expect_simulate_sample_once|Authentication/Signatures/HashAndSign/OneQuerySampling.lean|47
planted_coupling|Authentication/Signatures/Lamport/Planted.lean|403
expect_runB_good|Encryption/PublicKey/NonMalleability/Simulation/SimIND.lean|702
abs_expect_sub_le_expect|Encryption/PrivateKey/EncryptThenTag/Forgery.lean|515
abs_expect_sub_le|Games/Probability.lean|392
expect_sample_equiv|Games/Probability.lean|303
pow_val_mul|Pairing/Group.lean|192
pow_val_mul_GT|Pairing/Group.lean|197
pow_val_bijective|Pairing/Group.lean|224
pow_val_mul_mul|KeyExchange/Joux.lean|90
schnorr_completeness|SchnorrProtocol.lean|69
T
