#!/usr/bin/env python3
"""Declaration blocks of the five owned files at the ancestor and at a head, compared with
comments stripped (nested /- -/ incl. docstrings, `--` line comments; strings kept).

Usage: blocks.py <head-rev> <out.json>
A block runs from a column-0 declaration line (modifiers/attributes included) to the line before
the next column-0 declaration or command (section/end/namespace/open/variable/attribute/...).
Reports per file: deleted, added, changed (code differs), unchanged; for public declarations the
header (text before the first top-level `:=`, ` where`, or `|`) and, for public non-theorems,
the whole block."""
import re, subprocess, sys, json, hashlib
F = '/workspace/tcslib-fill'; ANC = '31348fcf7dee32f84db1fc8f929d80653137995e'
FILES = ['Concrete', 'DiscreteLog', 'ElGamal', 'RSA', 'Rabin']
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque|axiom)\b\s*([^\s(:{\[]*)")
CMD = re.compile(r"^(section|end|namespace|open|variable|attribute|set_option|omit|include|noncomputable section|universe|#|import|@\[)")

def strip_comments(s):
    out = []; i = 0; n = len(s); depth = 0
    while i < n:
        if s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth:
            if s.startswith('-/', i): depth -= 1; i += 2
            else:
                out.append('\n' if s[i] == '\n' else ''); i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = n if j < 0 else j; continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(s[i:j + 1]); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)

def blocks(src):
    L = strip_comments(src).split('\n')
    res = {}; cur = None; anon = {}
    for i, l in enumerate(L):
        m = DECL.match(l)
        if m:
            name = m.group(3)
            if not name or name.startswith(':'):
                anon[m.group(2)] = anon.get(m.group(2), 0) + 1
                name = f'<anonymous {m.group(2)} #{anon[m.group(2)]}>'
            cur = {'name': name, 'kind': m.group(2), 'mods': m.group(1).split(), 'line': i + 1, 'lines': [l]}
            key = name
            k = 2
            while key in res: key = f'{name}#{k}'; k += 1
            res[key] = cur
            continue
        if l and not l[0].isspace() and CMD.match(l):
            cur = None; continue
        if cur is not None: cur['lines'].append(l)
    for b in res.values():
        code = '\n'.join(b['lines']).rstrip()
        b['code'] = re.sub(r'[ \t]+\n', '\n', code)
        b['sha'] = hashlib.sha256(b['code'].encode()).hexdigest()
        b['private'] = 'private' in b['mods']
        c = b['code']
        # header: up to the first top-level ':=' (or ' where' / leading '|' line for inductives)
        m = re.search(r':=|\bwhere\b|\n\s*\|', c)
        b['header'] = re.sub(r'\s+', ' ', c[:m.start()] if m else c).strip()
        del b['lines']
    return res

def show(rev, f):
    return subprocess.run(['git', '-C', F, 'show', f'{rev}:TCSlib/Cryptography/Candidates/{f}.lean'],
                          capture_output=True, text=True, check=True).stdout

head = sys.argv[1]; out = {}
for f in FILES:
    a, b = blocks(show(ANC, f)), blocks(show(head, f))
    r = {'deleted': [], 'added': [], 'changed': [], 'unchanged': 0, 'public_header_changes': [],
         'public_body_changes': []}
    for k in a:
        if k not in b: r['deleted'].append({'name': k, 'kind': a[k]['kind'], 'private': a[k]['private'], 'line': a[k]['line']})
    for k in b:
        if k not in a:
            r['added'].append({'name': k, 'kind': b[k]['kind'], 'private': b[k]['private'], 'line': b[k]['line']}); continue
        if a[k]['sha'] != b[k]['sha']:
            r['changed'].append({'name': k, 'kind': b[k]['kind'], 'private': b[k]['private'],
                                 'anc_line': a[k]['line'], 'head_line': b[k]['line'],
                                 'header_same': a[k]['header'] == b[k]['header']})
        else: r['unchanged'] += 1
        if not b[k]['private']:
            if a[k]['header'] != b[k]['header'] or a[k]['mods'] != b[k]['mods']:
                r['public_header_changes'].append(k)
            if b[k]['kind'] not in ('theorem', 'lemma') and a[k]['sha'] != b[k]['sha']:
                r['public_body_changes'].append(k)
    out[f] = r
json.dump(out, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
for f, r in out.items():
    print(f"## {f}: deleted {len(r['deleted'])}, added {len(r['added'])}, changed {len(r['changed'])}, "
          f"unchanged {r['unchanged']}; public header changes {r['public_header_changes']}; "
          f"public non-theorem body changes {r['public_body_changes']}")
    for c in r['changed']:
        print(f"   changed {'private ' if c['private'] else 'PUBLIC '}{c['kind']} {c['name']} "
              f"(anc {c['anc_line']} -> head {c['head_line']}; header same: {c['header_same']})")
    for c in r['added']:
        print(f"   added {'private ' if c['private'] else 'PUBLIC '}{c['kind']} {c['name']}")
