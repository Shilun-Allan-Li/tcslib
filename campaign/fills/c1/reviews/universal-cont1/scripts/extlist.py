import sys, re
txt = open(sys.argv[1], encoding='utf-8').read()
i = txt.index('EXTLIST total')
seg = txt[i:]
seg = seg[seg.index('[') + 1: seg.index(']')]
names = [s.strip() for s in seg.replace('\n', ' ').split(',') if s.strip()]
open(sys.argv[2], 'w').write('\n'.join(names) + '\n')
print(len(names))
