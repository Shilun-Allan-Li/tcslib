#!/usr/bin/env python3
"""Source-level public-surface comparison of owned files between two revisions (cleanup-part2).

python3 -I surface_diff.py <base-rev> <head-rev> <owned-files.txt> <out.json>

For every declaration (theorem/lemma/def/abbrev/structure/inductive/class/instance/opaque) the
full name is reconstructed from the `namespace`/`section` stack, and two normalized texts are
compared (comments removed, whitespace collapsed):
* header: attributes + modifiers + signature up to the top-level `:=`/`where`/`|` (for theorems
  this is the claim);
* body: for non-theorem declarations, the text after the header up to the next declaration.
Reports declarations added, removed, header-changed and (non-theorem) body-changed, each with its
visibility, kind and file at both revisions."""
import sys, re, json, subprocess
base, head, owned_f, out = sys.argv[1:5]
CLONE = '/workspace/cp2/src'
owned = [l.strip() for l in open(owned_f) if l.strip()]
DECL = re.compile(r"^((?:@\[[^\]]*\]\s*)*)((?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*)"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom)\b\s*([^\s(:{\[]*)")

def blank_comments(s):
    out = []; i = 0; n = len(s); depth = 0
    while i < n:
        if s.startswith('/-', i): depth += 1; i += 2; out.append('  '); continue
        if depth:
            if s.startswith('-/', i): depth -= 1; i += 2; out.append('  ')
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(s[i:j + 1]); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)

def split_header(text, kind):
    depth = 0; i = 0
    while i < len(text):
        c = text[i]
        if c in '([{⟨': depth += 1
        elif c in ')]}⟩': depth -= 1
        elif depth == 0:
            if text.startswith(':=', i): return text[:i], text[i:]
            if kind in ('structure', 'class', 'inductive', 'instance', 'def', 'abbrev') and re.match(r'\swhere\b', text[i:]):
                return text[:i], text[i:]
            if kind in ('def', 'theorem', 'lemma', 'abbrev', 'instance', 'inductive') and text.startswith('\n', i) and re.match(r'\n\s*\|', text[i:]):
                return text[:i], text[i:]
        i += 1
    return text, ''

def decls(rev, path):
    try:
        src = subprocess.run(['git', '-C', CLONE, 'show', f'{rev}:{path}'], capture_output=True, text=True, check=True).stdout
    except subprocess.CalledProcessError:
        return {}
    code = blank_comments(src)
    lines = code.split('\n')
    stack = []; res = {}; anon = 0
    starts = []
    for i, l in enumerate(lines):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1)))
        elif re.match(r'^section\b', l): stack.append(('sec', ''))
        elif re.match(r'^end\b', l) and stack: stack.pop()
        d = DECL.match(l)
        if d: starts.append((i, d, '.'.join(x[1] for x in stack if x[0] == 'ns')))
    bounds = [s[0] for s in starts] + [len(lines)]
    for k, (i, d, ns) in enumerate(starts):
        # the declaration text ends at the next declaration or a top-level command
        j = bounds[k + 1]
        for t in range(i + 1, j):
            if re.match(r'^(namespace|end|section|open|variable|omit|include|set_option|attribute|#|noncomputable section|universe|@\[)', lines[t]):
                j = t; break
        text = '\n'.join(lines[i:j])
        attrs, mods, kind, name = d.group(1), d.group(2), d.group(3), d.group(4)
        if not name or kind == 'instance' and (name.startswith(':') or name.startswith('[')):
            anon += 1; name = f'<anon {kind} {anon}>'
        full = name[len('_root_.'):] if name.startswith('_root_.') else (ns + '.' + name if ns else name)
        hdr, body = split_header(text[d.end():], kind)
        # self-references spelled with the namespace prefix inside the namespace are the same name
        if ns:
            for k2 in range(len(ns.split('.')), 0, -1):
                pre = '.'.join(ns.split('.')[-k2:]) + '.'
                hdr = re.sub(r'(?<![\w.])' + re.escape(pre) + r'(?=\w)', '', hdr)
                if body: body = re.sub(r'(?<![\w.])' + re.escape(pre) + r'(?=\w)', '', body)
        norm = lambda s: re.sub(r'\s+', ' ', s).strip()
        key = full if 'private' not in mods else f'{path}::{full}'
        res[key] = {'kind': kind, 'private': 'private' in mods, 'attrs': norm(attrs), 'mods': norm(mods),
                     'header': norm(hdr), 'body': norm(body) if kind not in ('theorem', 'lemma') else None,
                     'path': path, 'line': i + 1}
    return res

report = {'added': [], 'removed': [], 'header_changed': [], 'body_changed': [], 'moved': []}
B = {}; H = {}
for p in owned:
    for n, v in decls(base, p).items(): B[n] = v
    for n, v in decls(head, p).items(): H[n] = v
for n in sorted(set(B) | set(H)):
    b, h = B.get(n), H.get(n)
    if b and not h: report['removed'].append({'name': n, 'header': (b['attrs'] + ' ' + b['mods'] + ' ' + b['header']).strip(), **{k: b[k] for k in ('kind', 'private', 'path', 'line')}})
    elif h and not b: report['added'].append({'name': n, 'header': (h['attrs'] + ' ' + h['mods'] + ' ' + h['header']).strip(), **{k: h[k] for k in ('kind', 'private', 'path', 'line')}})
    else:
        if b['path'] != h['path']: report['moved'].append({'name': n, 'kind': h['kind'], 'private': h['private'], 'from': b['path'], 'to': h['path'],
                                                          'header_unchanged': (b['header'], b['attrs'], b['mods']) == (h['header'], h['attrs'], h['mods'])})
        if (b['header'], b['attrs'], b['mods']) != (h['header'], h['attrs'], h['mods']):
            report['header_changed'].append({'name': n, 'kind': h['kind'], 'private': h['private'], 'path': h['path'],
                                             'line': h['line'], 'base': (b['attrs'] + ' ' + b['mods'] + ' ' + b['header']).strip(),
                                             'head': (h['attrs'] + ' ' + h['mods'] + ' ' + h['header']).strip()})
        if b['body'] is not None and b['body'] != h['body']:
            report['body_changed'].append({'name': n, 'kind': h['kind'], 'private': h['private'], 'path': h['path'], 'line': h['line'],
                                           'base_body': b['body'][:400], 'head_body': h['body'][:400]})
report['summary'] = {k: len(v) for k, v in report.items() if isinstance(v, list)}
report['summary_public'] = {k: sum(1 for x in v if not x.get('private', False)) for k, v in report.items() if isinstance(v, list)}
json.dump(report, open(out, 'w'), indent=1, ensure_ascii=False)
print(json.dumps(report['summary'])); print(json.dumps(report['summary_public']))
