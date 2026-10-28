"""Report dev-module lines that would exceed 100 characters once landed (with `private `)."""
import re
import sys
DECL = re.compile(r'^(theorem|lemma|def|abbrev|inductive|structure|instance|noncomputable def)\b')
for m in sys.argv[1:]:
    p = f'/home/user/tcslib/evidence/dev/{m}.lean'
    for i, l in enumerate(open(p).read().split('\n'), 1):
        n = len(l) + (8 if DECL.match(l) else 0)
        if n > 100:
            print(f'{m}:{i}: {n}')
