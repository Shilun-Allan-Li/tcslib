#!/usr/bin/env python3
"""Lexical code-token census: counts `sorry`, `admit`, `axiom`, `sorryAx` tokens in Lean files,
excluding nested block comments /- -/, line comments --, string literals (with escapes),
char literals and «quoted» identifiers. Usage: census.py <root> [files...] (default: TCSlib/**.lean)."""
import os, re, sys, json
def code_tokens(src):
    out=[]; i=0; n=len(src); depth=0
    while i<n:
        if src.startswith('/-',i): depth+=1; i+=2; continue
        if depth:
            if src.startswith('-/',i): depth-=1; i+=2
            else: i+=1
            continue
        if src.startswith('--',i):
            j=src.find('\n',i); i=n if j<0 else j; continue
        c=src[i]
        if c=='"':
            i+=1
            while i<n and src[i]!='"':
                i+= 2 if src[i]=='\\' else 1
            i+=1; out.append(' '); continue
        if c=='«':
            j=src.find('»',i); i=n if j<0 else j+1; out.append(' '); continue
        if c=="'" and i+2<n and (src[i+2]=="'" or (src[i+1]=='\\' and "'" in src[i+2:i+6])):
            # char literal 'x' or '\n'
            j=src.find("'",i+1 if src[i+1]!='\\' else i+2); i=j+1; out.append(' '); continue
        out.append(c); i+=1
    return ''.join(out)
TOK=re.compile(r"(?<![A-Za-z0-9_'.!?])(sorry|admit|axiom|sorryAx)(?![A-Za-z0-9_'!?])")
def count(path):
    t=code_tokens(open(path,encoding='utf-8').read())
    c={'sorry':0,'admit':0,'axiom':0,'sorryAx':0}
    for m in TOK.finditer(t): c[m.group(1)]+=1
    return c
root=sys.argv[1]; files=sys.argv[2:]
if not files:
    files=sorted(os.path.relpath(os.path.join(d,f),root) for d,_,fs in os.walk(os.path.join(root,'TCSlib')) for f in fs if f.endswith('.lean'))
tot={'sorry':0,'admit':0,'axiom':0,'sorryAx':0}; per={}
for f in files:
    c=count(os.path.join(root,f)); per[f]=c
    for k in tot: tot[k]+=c[k]
print(json.dumps({'total':tot,'nonzero':{f:c for f,c in per.items() if any(c.values())}},indent=1))
