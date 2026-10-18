"""Static checks of the B6-F1 v2 prescribed blocks (rule 10, revised).

Usage: python3 -I routescan.py <repo-root> <CounterLoopOverlay.lean> <SymbolLiftOverlay.lean>
                               <block.lean.txt> [<block.lean.txt> ...]

For every block given (the StepClock home block, the headline glue, the route obligations):
  1. it names no private declaration of the promoted CounterLoop or SymbolLift (inlining in the
     stitched route probe would otherwise hide such a citation);
  2. no `simp`, `simp only`, `simp_all`, `simpa`, `dsimp`, `rw`, `unfold` or `delta` argument
     is a definition of `Build/CounterLoop`, `SymbolLift`, `Build/Embed` or
     `Build/Contract/Basic` (those definitions are reached only through their equation lemmas).
Prints every finding and exits 1 on any; prints the counts and exits 0 otherwise."""
import re, sys

root, cl_p, sl_p, blocks = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
read = lambda p: open(p, encoding='utf-8').read()
def strip_comments(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S)
    return re.sub(r'--[^\n]*', ' ', s)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)'
                  r'(def|theorem|lemma|abbrev|instance|structure|inductive)\s+([^\s(:{\[]+)', re.M)
def decls(p):
    return [(m.group(2), m.group(3), 'private' in m.group(1)) for m in DECL.finditer(read(p))]
privates = {n.split('.')[-1] for p in (cl_p, sl_p) for k, n, pr in decls(p) if pr}
P = f'{root}/TCSlib/Complexity/TuringMachine'
defkinds = ('def', 'abbrev', 'structure', 'inductive')
defs = set()
for p in (cl_p, sl_p, f'{P}/Build/Embed.lean', f'{P}/Build/Contract/Basic.lean'):
    for k, n, pr in decls(p):
        if k in defkinds:
            defs.add(n); defs.add(n.split('.')[-1]); defs.add('Turing.' + n)
ident = re.compile(r"[A-Za-z_][A-Za-z0-9_.'₀-₉]*")
TAC = re.compile(r'\b(simp only|simp_all|simpa|simp|dsimp only|dsimp|rw|rwa|unfold|delta)\b'
                 r'\s*(\[[^\]]*\]|[^\n]*)')
bad = 0; nchk = 0
for b in blocks:
    text = strip_comments(read(b))
    toks = set(ident.findall(text))
    for t in sorted(toks):
        if t.split('.')[-1] in privates and not t.startswith('sc_'):
            print(f'PRIVATE {b.split("/")[-1]}: {t}'); bad += 1
    for m in TAC.finditer(text):
        nchk += 1
        args = m.group(2)
        if m.group(1) in ('unfold', 'delta'):
            items = args.split()
        else:
            if not args.startswith('['): continue
            # the top-level, comma-separated arguments; a term argument such as
            # `show … from rfl` is not an unfolding of the names it mentions
            items, depth, cur = [], 0, ''
            for ch in args[1:-1]:
                if ch in '([{⟨': depth += 1
                if ch in ')]}⟩': depth -= 1
                if ch == ',' and depth == 0: items.append(cur); cur = ''
                else: cur += ch
            items.append(cur)
        for it in items:
            t = it.strip().lstrip('←').strip()
            if t in defs:
                print(f'UNFOLD {b.split("/")[-1]}: {m.group(1)} {t}'); bad += 1
print(f'checked {len(blocks)} blocks: {nchk} rewriting/unfolding tactics against {len(defs)} '
      f'definition names, identifiers against {len(privates)} private names: {bad} findings')
sys.exit(1 if bad else 0)
