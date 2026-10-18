import sys
# usage: reverse.py <base file> <head file>: drop the inserted home block and swap the appendix
# paragraph back; the result must equal the base byte for byte.
b = open(sys.argv[1], encoding='utf-8').read().split('\n'); h = open(sys.argv[2], encoding='utf-8').read().split('\n')
# head: home insert is between base line 224 (cw_head_bound's last line) and the target docstring
hs = next(i for i, l in enumerate(h) if l.startswith('/-- **H3 with the configuration-count clock**'))
bs = next(i for i, l in enumerate(b) if l.startswith('/-- **H3 with the configuration-count clock**'))
ins = h[bs:hs]  # inserted lines (head lines bs+1..hs)
h2 = h[:bs] + h[hs:]
ha = next(i for i, l in enumerate(h2) if l.startswith('**Fill appendix (B6-F3'))
hc = next(i for i in range(ha, len(h2)) if h2[i] == ' -/')
ba = next(i for i, l in enumerate(b) if l.startswith('**Fill appendix (B6-F3'))
bc = next(i for i in range(ba, len(b)) if b[i] == ' -/')
h3 = h2[:ha] + b[ba:bc] + h2[hc:]
print('inserted home block: head lines %d..%d (%d lines)' % (bs + 1, hs, len(ins)))
print('head appendix: head lines %d..%d (%d lines) -> base appendix %d..%d' % (ha + 1 + len(ins), hc + len(ins), hc - ha, ba + 1, bc))
print('reversal equals base byte for byte:', h3 == b)
