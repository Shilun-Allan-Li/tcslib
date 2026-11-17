"""leanindex.py: a static (no Lean) index of TCSlib sources at one git revision.

Reads every TCSlib .lean blob at <rev> from git objects (never the working tree) and gives:
  imports(path)      -> TCSlib and other modules imported, in file order;
  decls(path)        -> declarations (full name, kind, private, line), namespaces resolved
                        (the decls2.py scanner, extended to private and anonymous declarations);
  sorries(path)      -> declaration names whose body holds a `sorry` token (comments and strings
                        stripped, tokens attributed to the enclosing declaration).
Approximate by design: the elaborated environment is authoritative (the job's collector)."""
import re, subprocess

KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
MODS = r'(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*' + MODS + KW + r'\b\s*([^\s(:{\[⦃]*)')


def git(repo, *a, binary=False):
    r = subprocess.run(['git', '-C', repo, *a], check=True, capture_output=True)
    return r.stdout if binary else r.stdout.decode('utf-8')


def blobs(repo, rev, paths):
    """path -> text, read from git objects at rev with one cat-file --batch process."""
    p = subprocess.Popen(['git', '-C', repo, 'cat-file', '--batch'], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE)
    out = {}
    for path in paths:
        p.stdin.write(f'{rev}:{path}\n'.encode()); p.stdin.flush()
        head = p.stdout.readline().split()
        if head[-1] == b'missing':
            continue
        size = int(head[2]); data = p.stdout.read(size); p.stdout.read(1)
        out[path] = data.decode('utf-8')
    p.stdin.close(); p.wait()
    return out


def strip(src):
    """Remove comments (nested block comments, line comments) and string literals,
    keeping line structure."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        c = src[i]
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            i = j; continue
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0:
            if src.startswith('-/', i):
                depth -= 1; i += 2; continue
            if c == '\n':
                out.append('\n')
            i += 1; continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('"' + '\n' * src[i:j].count('\n') + '"'); i = j + 1; continue
        if c == "'" and i + 2 < n and (src[i + 2] == "'" or (src[i + 1] == '\\' and src[i + 3:i + 4] == "'")):
            j = src.find("'", i + 1)
            if j > 0 and j - i <= 4 and '\n' not in src[i:j]:
                out.append("' '"); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)


def imports(src):
    res = []
    for line in strip(src).split('\n'):
        m = re.match(r'^\s*import\s+(.+)$', line)
        if m:
            res.extend(m.group(1).split())
    return res


def decls(src):
    """[(full_name, kind, private, line_no)]; anonymous instances get name '<anon>'."""
    lines = strip(src).split('\n')
    out, ns = [], []
    for i, line in enumerate(lines):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop(); continue
        m = DECL.match(line)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        head = line[:m.start(1)]
        private = bool(re.search(r'\bprivate\b', head))
        if not name or name.startswith(':') or name in ('where', ':='):
            name = '<anon>'
        if name.startswith('_root_.'):
            full = name[len('_root_.'):]
        elif name == '<anon>':
            full = '.'.join(ns + ['<anon>'])
        else:
            full = '.'.join(ns + [name])
        out.append((full, kind, private, i + 1))
    return out


def sorries(src):
    lines = strip(src).split('\n')
    ds = decls(src)
    starts = [(d[3], d[0]) for d in ds]
    hits = {}
    for i, line in enumerate(lines):
        if re.search(r'(?<![\w.])sorry(?![\w])', line):
            owner = None
            for ln, name in starts:
                if ln <= i + 1:
                    owner = name
                else:
                    break
            hits[owner or '<file>'] = hits.get(owner or '<file>', 0) + 1
    return hits
