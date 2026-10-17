"""Forbidden-construct screen (comment-stripped; docstrings and comments removed, line numbers
kept). usage: python3 -I forbidden.py <root> <file> [<file> ...]
Token hits (identifier-boundary): sorry admit axiom IO unsafe implemented_by extern
native_decide ofReduceBool opaque run_cmd run_tac csimp.
Command hits (line start, after optional attributes / local / scoped / private):
macro macro_rules syntax elab elab_rules notation infix infixl infixr prefix postfix
declare_syntax_cat, and any `#` command (#eval, #print, #check, #exit, ...).
set_option: every occurrence, classified as one of the three standard header options at
top level, or OTHER.
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines

root, files = sys.argv[1], sys.argv[2:]
TOKS = ['sorry', 'admit', 'axiom', 'IO', 'unsafe', 'implemented_by', 'extern', 'native_decide',
        'ofReduceBool', 'opaque', 'run_cmd', 'run_tac', 'csimp']
TOK = re.compile(r"(?<![A-Za-z0-9_.'])(" + '|'.join(TOKS) + r")(?![A-Za-z0-9_'])")
CMD = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:local|scoped|private)\s+)*'
                 r'(macro_rules|macro|syntax|elab_rules|elab|notation|infixl|infixr|infix|prefix|'
                 r'postfix|declare_syntax_cat)\b')
HASH = re.compile(r'^\s*(#[a-z_]+)')
STD = {'set_option maxHeartbeats 0', 'set_option relaxedAutoImplicit false',
       'set_option autoImplicit false'}
tok_hits, cmd_hits, so_std, so_other = [], [], 0, []
for f in files:
    s = strip_keep_lines(open(os.path.join(root, f), encoding='utf-8').read())
    for ln, l in enumerate(s.split('\n'), 1):
        for m in TOK.finditer(l): tok_hits.append((f, ln, m.group(1), l.strip()))
        m = CMD.match(l)
        if m: cmd_hits.append((f, ln, m.group(1), l.strip()))
        m = HASH.match(l)
        if m: cmd_hits.append((f, ln, m.group(1), l.strip()))
        for m in re.finditer(r'set_option\s+\S+\s+\S+', l):
            occ = m.group(0)
            if occ in STD and l.strip() == occ: so_std += 1
            else: so_other.append((f, ln, l.strip()))
print(f'files screened: {len(files)}')
print(f'token hits ({", ".join(TOKS)}): {len(tok_hits)}')
for h in tok_hits: print('  %s:%d  [%s]  %s' % h)
print(f'command hits (macro/syntax/elab/notation/... and # commands): {len(cmd_hits)}')
for h in cmd_hits: print('  %s:%d  [%s]  %s' % h)
print(f'set_option: {so_std} standard header lines; {len(so_other)} other occurrences')
for h in so_other: print('  %s:%d  %s' % h)
