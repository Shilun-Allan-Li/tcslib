#!/usr/bin/env python3
"""Regenerate scratch/census/Census.lean for an order list: one import per module, in order, and
the module set of the census. usage: gen_census.py ORDER"""
import re, sys
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
p = '/workspace/folds/scratch/census/Census.lean'
src = open(p).read()
body = src[src.index('\nopen Lean Elab Command Meta'):]
mods = ', '.join('`' + m.replace('/', '.') for m in order)
body = re.sub(r'Std\.HashSet\.ofList \[[^\]]*\]', 'Std.HashSet.ofList [' + mods + ']', body, count=1)
imports = '\n'.join('import ' + m.replace('/', '.') for m in order)
open(p, 'w').write(imports + '\n' + body)
print(len(order), 'modules')
