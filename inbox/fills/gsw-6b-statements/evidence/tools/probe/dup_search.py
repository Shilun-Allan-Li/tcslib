"""dup_search.py <repo> <rev> <mathlib-root> <batteries-root> <core-root> (gsw-6b-statements, sub-agent probe; new;
check 12). For every new declaration of the 6b statement head (and O2), a list of shape patterns (regexes on one
source line) chosen by hand from its statement or body; each pattern is searched in TCSlib/ at <rev> (git grep,
the new files excluded) and in Mathlib, Batteries and core sources (ripgrep-free Python walk). Prints, per
declaration and pattern, the hit count and the first hits. The table in dup/dup-table.md is written from this
output (relations judged by hand)."""
import os, re, subprocess, sys
repo, rev, ml, bt, core = sys.argv[1:6]
NEW = ('GSW/Branching.lean', 'GSW/DecryptFormula.lean', 'GSW/Bootstrap.lean', 'GSW/Circular.lean',
       'GSW/Leveled.lean', 'GSW/LeveledSecurity.lean', 'GSW/PolyRatio.lean', 'GSW/Asymptotic.lean',
       'LWE/Ratio.lean')
P = {
 'select': [r'mul P \(gadget P - ', r'gadget P - C\)', r'def (sel|select|mux|cmux)\b'],
 'homEvalPBP': [r'evalWith \(', r'def homEval'],
 'homEvalFormula': [r'barrington [^ ]+ sigma1', r'barrington c '],
 'keyBits': [r'decomposeVec P \(secretVector', r'def (keyBits|secretBits|bitsOfSecret)'],
 'decConstants': [r'vecMul \(decryptColumn', r'decryptColumn P C\) \(gadget'],
 'decryptFormula': [r'modSumInterval \(', r'def decrypt(Formula|Circuit)'],
 'nandFormula': [r'and2 .*\)\.neg', r'def nand(Formula|Circuit)'],
 'decDepth': [r'modSumDepth (P|N|M)'],
 'bootNoise': [r'4 \^ \(.*\+ 1\) \* \(2 \* ', r'def bootNoise'],
 'bootNAND': [r'homEvalFormula P \(', r'def boot'],
 'bootGate / homGate': [r'match g\.args with', r'def homGate'],
 'fheEval / GSW.eval': [r'runWith \((homGate|bootGate|fun g)', r'\(runWith .*\)\.getD'],
 'evalKey': [r'encrypt P pk \(', r'def (evalKey|evk|bootKey)'],
 'PublicKey/Secret/Coins/KeySeed': [r'abbrev (PublicKey|Secret|Coins|KeySeed|Seed)\b',
     r'Matrix \(Fin P\.lwe\.samples\) \(Fin P\.columns\) Bool'],
 'FheView/Seeds/fheView': [r'abbrev (FheView|View|Seeds)\b', r'Regev\.keygen P\.lwe χ r\.1'],
 'WeakCircularSecure(Family)': [r'(?i)def \S*circular', r'def \S*Secure\S* .*: Prop'],
 'levelKey / LevelCoins': [r'd\.succ\) \(ss d\.castSucc', r'(?i)def \S*levelkey'],
 'literalCts': [r'Fin\.append cts', r'homNot P \[cts', r'Fin\.append x fun'],
 'levelGate / leveledEval': [r'depthAt vs\.length', r'(?i)def \S*leveled'],
 'leveledView / levelHybrid': [r'(?i)def \S*hybrid\b', r'if h ≤ e\.val then'],
 'levelReduction / hybridPlant': [r'hybridPlant \(', r'reduction P \('],
 'levelTerm / challengeTerm': [r'decisionAdvantage P\.lwe χ \(.*\) \+', r'extractionError P\.lwe\)'],
 'RatioBounded': [r'(?i)ratio', r'Bounded \(B κ\)'],
 'Parameters.ofFamily': [r'residueBits\.eval κ', r'modulus_le_pow κ', r'def \S*ofFamily'],
 'pBoot': [r'\.const \(2 \^', r'def pBoot'],
 'encodeCiphertext/View/FheView/LeveledView': [r'encodeMatrix P\.width', r'encodeMatrix .* C\b',
     r'def encode\S*View'],
 'ReductionEfficient / LeveledReductionEfficient': [r'∃ D\' : NUPPT', r'(?i)def \S*efficient'],
 'decodeLo/decodeHi/decode_iff_mem_Ico': [r'/ 2 / 2', r'decode P .* = true ↔', r'(?i)valMinAbs_natAbs_eq_min',
     r'mem_Ico'],
 'neZero_columns': [r'NeZero .*columns', r'NeZero .*width'],
 'G1 Encrypts.select': [r'theorem Encrypts\.', r'Encrypts P t \(\(1 - b\)'],
 'G2/G3 encrypts_homEval*': [r'evalWith_rel', r'Encrypts P t .*homEval'],
 'G5 vecMul_secretVector_eq_sum': [r'secretVector P s ⬝ᵥ', r'dotProduct \(secretVector', r'vecMul \(secretVector',
     r'gadget_mulVec_decomposeVec', r'dotProduct_mulVec'],
 'G6/G7 *Formula_eval': [r'\.eval \(keyBits', r'modSumInterval_eval'],
 'G8 depth/fan-in/decDepth_le': [r'modSumDepth_le', r'depth_modSumInterval_le', r'maxFanin_modSumInterval_le'],
 'G9/G10/G18/G12 bootstrapping correctness': [r'theorem (eval_encrypts|decrypt_keygen_eval)',
     r'decrypt P .* \(eval P', r'Encrypts\.nand'],
 'G11/L1 citations': [r'theorem encrypts_(keygen_)?encrypt\b'],
 'G13 bootNoise_le': [r'pow_pred_clog_lt_self', r'4 \^ 33'],
 'G15 distAdv_fheView_noEvk_le': [r'theorem distAdv_encrypt_le', r'uprob_fst'],
 'L2/L3 leveled correctness': [r'layerNAND_eval', r'litInput'],
 'L4/L5 hybrids': [r'theorem distAdv_multi_le_sum', r'theorem abs_sub_le_sum_hybrids'],
 'G16/G17 ratio': [r'bootNoise .* ≤ .*eval', r'RatioBounded'],
 'A1/A3 asymptotic IND-CPA': [r'Negligible fun κ =>\s*$', r'Negligible \(fun κ => distAdv', r'negligible_polyExpr_mul',
     r'Negligible\.polyExpr_mul'],
}
def git_grep(pat):
    r = subprocess.run(['git', '-C', repo, 'grep', '-n', '-P', pat, rev, '--', 'TCSlib'], capture_output=True,
                       text=True).stdout.split('\n')
    return [l[len(rev) + 1:] for l in r if l and not any(n in l for n in NEW)]
def walk(root, rx):
    hits = []
    for dp, _, fn in os.walk(root):
        for f in fn:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                for i, l in enumerate(open(p, encoding='utf-8', errors='replace'), 1):
                    if rx.search(l): hits.append(f'{os.path.relpath(p, os.path.dirname(root))}:{i}: {l.strip()[:120]}')
    return hits
for k, pats in P.items():
    print(f'## {k}')
    for p in pats:
        t = git_grep(p); rx = re.compile(p); ext = []
        for root in (ml, bt, core): ext += walk(root, rx)
        print(f'  pattern {p!r}: TCSlib {len(t)}, Mathlib/Batteries/core {len(ext)}')
        for h in t[:6]: print(f'    T {h[:170]}')
        for h in ext[:4]: print(f'    X {h[:170]}')
