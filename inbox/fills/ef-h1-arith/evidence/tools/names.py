import re,sys
for p in sys.argv[1:]:
    for l in open(p,encoding='utf-8'):
        m=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|instance)\s+(\S+)',l)
        if m: print(m.group(2))
