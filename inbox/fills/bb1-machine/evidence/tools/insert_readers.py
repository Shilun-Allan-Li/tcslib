"""insert_readers.py <worktree> <BB1ReadersMin.lean.txt>: insert the seven approved readers verbatim
(brief: Defs.lean after line 387 = blank + approved 27-68; BonehBoyen.lean after line 387 = blank + 74-97,
after line 551 = blank + 99-109). Pure insertions; checks base and result hashes."""
import sys, hashlib
wt, src = sys.argv[1:3]
A = open(src, encoding='utf-8').read().split('\n')
blk = lambda a, b: A[a - 1:b]
base = 'TCSlib/Cryptography/AdvancedEncryption/IdentityBased/'
H = lambda s: hashlib.sha256(s.encode()).hexdigest()
plan = {'Defs.lean': ([(387, blk(27, 68))], '9af4b7738f041d2b7f166df6b6ef7c35cf1fcf41c891e04317b50bdff06cf4a8',
                      '4e220eadd4bf71ea62372bc371a3e2062b9f213acc696dbb66994c1f64069dfd',
                      '    S.oracleImpl κ init key chal 2 x s = chal x s := rfl'),
        'BonehBoyen.lean': ([(387, blk(74, 97)), (551, blk(99, 109))],
                            '22caae4f61102c6c31b242fbc37f486939442960049b5e6e4c54790fca96ecd6',
                            'da875140806706f26c4cdbb5cf765f522144f3a5a885c5156a58b8c611cd25f4', None)}
for f, (ins, h0, h1, anchor) in plan.items():
    p = wt + '/' + base + f
    s = open(p, encoding='utf-8').read()
    assert H(s) == h0, f
    L = s.split('\n')
    if anchor: assert L[386] == anchor
    for at, b in sorted(ins, reverse=True):
        L[at:at] = [''] + b
    out = '\n'.join(L)
    print(f, len(s.split('\n')) - 1, '->', len(L) - 1, 'lines', H(out), 'OK' if H(out) == h1 else 'MISMATCH')
    assert H(out) == h1
    open(p, 'w', encoding='utf-8').write(out)
