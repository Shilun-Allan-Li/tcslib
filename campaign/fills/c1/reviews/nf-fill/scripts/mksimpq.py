"""The head with its four unrestricted simp calls turned into simp? / simp_all? (python3 -I).
usage: python3 -I mksimpq.py <head.lean> <out.lean>"""
import sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
edits = {137: ('  | nil => simp [nf_ctlStop]', '  | nil => simp? [nf_ctlStop]'),
         145: ("      simp [nf_ctlStop, hz']", "      simp? [nf_ctlStop, hz']"),
         153: ("      simp [nf_ctlStop, hn']", "      simp? [nf_ctlStop, hn']"),
         580: ('    split_ifs with h hj <;> simp_all', '    split_ifs with h hj <;> simp_all?')}
for n, (a, b) in edits.items():
    assert L[n - 1] == a, (n, L[n - 1]); L[n - 1] = b
open(sys.argv[2], 'w', encoding='utf-8').write('\n'.join(L))
print('wrote', sys.argv[2])
