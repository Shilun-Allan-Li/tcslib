import sys
p = sys.argv[1]
s = open(p, encoding='utf-8').read()
def rep(old, new):
    global s
    n = s.count(old)
    assert n == 1, (n, old[:70])
    s = s.replace(old, new)
rep("""file's closure): `campaign/fills/s13d/drafts/s13d-fill-g4-cont4/preship-97299639/`. Issue-time
items: ⟨ANCESTOR⟩, ⟨BASE⟩, ⟨IN-FLIGHT⟩, ⟨SNAPSHOT⟩, ⟨SORRIES⟩ (30 at `97299639`; it moves as #147,
#150 and megafill A land), ⟨SCREEN⟩ (846/477 at `97299639`), the megafill banner, and re-running
the pre-ship at the issue commit. -->""",
"""file's closure): `campaign/fills/s13d/drafts/s13d-fill-g4-cont4/preship-97299639/`; re-run at
`6e761018` (`preship-6e761018/`, against `oleans-lslsk`; TCSlib unchanged to megafill C's drafting
base). Issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩, ⟨SNAPSHOT⟩, ⟨SORRIES⟩ (27 at
`6e761018`), ⟨SCREEN⟩ (846/477 at `6e761018`), the out-of-scope sorries' placeholder, the megafill
banner (number, cover file, budget), and re-running the pre-ship at the issue commit (#156 edits
`Build/Seam`, in the screen population). -->""")
rep("""  `campaign/fills/s13d/orders/s13d-fill-g4-cont4.txt` (**95 modules**: the upstream closure of""",
"""  `campaign/fills/s13d/orders/s13d-fill-g4-cont4.txt` (**96 modules**: the upstream closure of""")
rep("""  FAIL (base: 0 FAIL, 33 WARN over 39 files; this file's are its size and three public""",
"""  FAIL (base: 0 FAIL, 33 WARN over 40 files; this file's are its size and three public""")
open(p, 'w', encoding='utf-8').write(s)
print('g4 ok')
