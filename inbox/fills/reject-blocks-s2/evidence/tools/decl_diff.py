#!/usr/bin/env python3
"""Declarations (by `def/theorem/lemma/abbrev/inductive/structure/instance` keyword and name) added
or deleted in each owned file between the ancestor and a commit, from source text."""
import re, subprocess, sys
F='/workspace/tcslib-fill'; ANC='31348fcf7dee32f84db1fc8f929d80653137995e'; head=sys.argv[1]
D=re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private |protected |noncomputable )*)(def|theorem|lemma|abbrev|inductive|structure|instance) (\S+)',re.M)
for f in ['Concrete','DiscreteLog','ElGamal','RSA','Rabin']:
    p=f'TCSlib/Cryptography/Candidates/{f}.lean'
    def decls(rev):
        s=subprocess.run(['git','-C',F,'show',f'{rev}:{p}'],capture_output=True,text=True).stdout
        return {m.group(3):(m.group(1).strip(),m.group(2)) for m in D.finditer(s)}
    a,b=decls(ANC),decls(head)
    dele=sorted(set(a)-set(b)); add=sorted(set(b)-set(a))
    print(f'## {f}: deleted {len(dele)}, added {len(add)}')
    for n in dele: print(f'- deleted {a[n][0]} {a[n][1]} `{n}`')
    for n in add: print(f'+ added {b[n][0]} {b[n][1]} `{n}`')
