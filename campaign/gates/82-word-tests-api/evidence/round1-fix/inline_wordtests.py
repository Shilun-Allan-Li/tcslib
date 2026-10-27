"""Inline Build/WordTests into a consumer (python3 -I): the consumer's imports without the WordTests
import, its options, the WordTests module from its docstring on, then the consumer from its first
line after the options. usage: inline_wordtests.py <WordTests.lean> <consumer.lean> <out>"""
import sys
wt, cons, out = sys.argv[1:4]
W = open(wt, encoding='utf-8').read()
C = open(cons, encoding='utf-8').read()
imp = 'import TCSlib.Complexity.TuringMachine.Build.WordTests\n'
assert C.count(imp) == 1
C = C.replace(imp, '')
opts = 'set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n'
assert C.count(opts) == 1 and W.count(opts) == 1
head, tail = C.split(opts, 1)
wbody = W.split(opts, 1)[1].lstrip('\n')
open(out, 'w', encoding='utf-8').write(head + opts + '\n' + wbody.rstrip('\n') + '\n' + tail)
