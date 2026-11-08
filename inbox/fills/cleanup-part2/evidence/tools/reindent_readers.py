#!/usr/bin/env python3
"""Re-indent the multi-line bodies of the generated `<name>_def` readers (cleanup-part2 style pass):
continuation lines of the body are placed at column 8 plus their relative indentation, the
closing type-ascription line is kept. python3 -I reindent_readers.py <new-readers.txt> <base-rev>"""
import re, subprocess, sys
short = {l.strip().split('.')[-1] for l in open(sys.argv[1]) if l.strip()}
files = [f for f in subprocess.run(['git', 'diff', sys.argv[2], '--name-only'], capture_output=True,
                                   text=True).stdout.split() if f.endswith('.lean')]
tot = 0
for f in files:
    lines = open(f).read().split('\n')
    i = 0; changed = False
    while i < len(lines):
        m = re.match(r'^(?:private )?theorem (\S+_def)\b', lines[i])
        if m and m.group(1) in short:
            j = i
            while j < len(lines) and not lines[j].rstrip().endswith(' ='): j += 1
            k = j + 1
            while k < len(lines) and ':= rfl' not in lines[k]: k += 1
            body = lines[j + 1:k + 1]
            if len(body) > 1:
                cont = body[1:]
                if (len(cont) >= 2 and re.match(r'^ {8}\S', cont[-1])
                        and cont[-1].rstrip().endswith(') := rfl') and cont[-2].rstrip().endswith(' :')):
                    cont = cont[:-1]
                if cont:
                    mn = min(len(c) - len(c.lstrip()) for c in cont if c.strip())
                    new = [' ' * (8 + len(c) - len(c.lstrip()) - mn) + c.lstrip() if c.strip() else c
                           for c in cont]
                    if new != cont:
                        lines[j + 2:j + 2 + len(cont)] = new; changed = True; tot += 1
            i = k + 1
            continue
        i += 1
    if changed: open(f, 'w').write('\n'.join(lines))
print('reindented', tot)
