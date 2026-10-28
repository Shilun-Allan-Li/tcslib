"""List declarations without a docstring, proofs over 20 lines without a literal
**Proof sketch.**, and lines over 100 characters, in the given Lean files."""
import re, sys
DECL = re.compile(r"^(?:private\s+)?(theorem|lemma|def|abbrev|inductive|structure|instance)\b\s*([^\s:({\[]*)")
for fn in sys.argv[1:]:
    lines = open(fn, encoding='utf-8').read().split('\n')
    decls = [i for i, l in enumerate(lines) if DECL.match(l)]
    for k, i in enumerate(decls):
        m = DECL.match(lines[i])
        j = i - 1
        while j >= 0 and (lines[j].startswith('@[') or lines[j].startswith('attribute')):
            j -= 1
        has_doc = j >= 0 and lines[j].rstrip().endswith('-/')
        doc = ''
        if has_doc:
            s = j
            while s >= 0 and '/--' not in lines[s]:
                s -= 1
            doc = '\n'.join(lines[s:j + 1])
        # proof length: from decl line to next decl/blank-separated top-level or end
        end = decls[k + 1] if k + 1 < len(decls) else len(lines)
        # back up over the next declaration's docstring
        e = end - 1
        while e > i and (lines[e].strip() == '' or lines[e].startswith('/-') or lines[e].startswith(' ') is False and lines[e].strip().startswith('-/') ):
            e -= 1
        body = [l for l in lines[i:end] if l.strip() != '']
        # crude: count lines after ':= by' or ' := ' start
        start = None
        for t in range(i, end):
            if ':= by' in lines[t] or lines[t].rstrip().endswith(':=') or ' where' in lines[t]:
                start = t
                break
        plen = 0
        if start is not None:
            t = start + 1
            while t < end and not lines[t].startswith('/--') and not DECL.match(lines[t]) \
                    and not lines[t].startswith('attribute') and not lines[t].startswith('end '):
                if lines[t].strip():
                    plen += 1
                t += 1
        if not has_doc:
            print(f"NODOC   {fn}:{i+1}: {m.group(1)} {m.group(2)}")
        elif m.group(1) in ('theorem', 'lemma') and plen > 20 and '**Proof sketch.**' not in doc:
            print(f"NOSKETCH {fn}:{i+1}: {m.group(2)} ({plen} proof lines)")
    for i, l in enumerate(lines):
        if len(l) > 100:
            print(f"LONG    {fn}:{i+1}: {len(l)}")
