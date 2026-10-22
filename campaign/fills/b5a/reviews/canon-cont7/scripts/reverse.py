import sys
# usage: reverse.py base head ins_start ins_len body_start body_len out
# Drop head lines [ins_start, ins_start+ins_len) and replace [body_start, body_start+body_len) by "  sorry";
# compare with base byte for byte.
base, head, a, n, b, m, out = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:7]), sys.argv[7]
H = open(head, encoding='utf-8').read().split('\n')
B = open(base, encoding='utf-8').read().split('\n')
assert H[a - 2].strip() == '' , ('line before insertion not blank', H[a-2])
ins = H[a - 1:a - 1 + n]
body = H[b - 1:b - 1 + m]
rest = H[:a - 1] + H[a - 1 + n:b - 1] + ['  sorry'] + H[b - 1 + m:]
open(out, 'w', encoding='utf-8').write('\n'.join(rest))
print('reconstructed == base:', rest == B, f'({len(rest)} vs {len(B)} lines)')
print('inserted block first/last lines:', repr(ins[0][:80]), '|', repr(ins[-1][:80]))
print('line after insertion:', repr(H[a - 1 + n][:80]))
print('body first/last lines:', repr(body[0][:80]), '|', repr(body[-1][:80]))
print('line before body:', repr(H[b - 2][:100]))
print('line after body:', repr(H[b - 1 + m][:80]))
