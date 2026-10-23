"""usage: python3 -I mkkinds.py <SLKinds.lean template> <names file> <module for imports> <out>"""
import sys
kinds = open(sys.argv[1], encoding='utf-8').read()
body = kinds[kinds.index('open Lean Meta Elab Command in'):kinds.rindex('\n#kinds ') + 1]
names = [l.strip() for l in open(sys.argv[2], encoding='utf-8') if l.strip() and not l.startswith('_private')]
imps = [l for l in open(sys.argv[3], encoding='utf-8') if l.startswith('import ')]
open(sys.argv[4], 'w', encoding='utf-8').write(''.join(imps) + 'import Lean\n' + body + '#kinds ' + ' '.join(names) + '\n')
print(len(names))
