#!/usr/bin/env python3
"""Build the C3 metadata-control probe: header + cp2OutDir + the census core + the two controls +
`#cp2c3 [_current]`. python3 -I c3controls.py <out.lean> <outdir>"""
import sys
out, outdir = sys.argv[1:3]
head = open('/workspace/cp2/tools/lean/C3Controls.lean.txt').read()
core = open('/workspace/cp2/tools/lean/CensusCore.lean.txt').read()
ctl = '''
open Turing

-- C3-POS: a foreign generated equation in the value
theorem cp2_c3_pos : pairDecode [] = none := (pairDecode.eq_def []).trans rfl

-- C3-NEG: the published case reader
theorem cp2_c3_neg : pairDecode [] = none := pairDecode_nil

#cp2c3 [_current]
'''
open(out, 'w').write(head + f'\ndef cp2OutDir : String := "{outdir}"\n' + core + ctl)
