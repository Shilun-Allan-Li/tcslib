"""A brief's import overlay (read-only): the authorized imports inserted after a given line of the
owned file. The insertion is asserted (the line is the file's last import, and removing the
inserted lines reproduces the input).
Usage: python3 -I mkimportoverlay.py <owned file> <after line> <out> <import>..."""
import sys
src, after, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
imps = sys.argv[4:]
ls = open(src, encoding='utf-8').read().split('\n')
assert ls[after - 1].startswith('import ') and not ls[after].startswith('import '), (ls[after - 1], ls[after])
new = [f'import {m}' for m in imps]
assert not any(n in ls for n in new)
o = ls[:after] + new + ls[after:]
assert o[:after] + o[after + len(new):] == ls
open(out, 'w', encoding='utf-8').write('\n'.join(o)); print('overlay written:', len(o), 'lines')
