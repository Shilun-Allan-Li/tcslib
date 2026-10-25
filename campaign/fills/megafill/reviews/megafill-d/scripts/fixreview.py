import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
a = "5. Re-triage F6 when #161 merges, as a possible third item."
b = "5. Re-triage F6 now that #161 has merged, as a possible third item."
assert s.count(a) == 1
s = s.replace(a, b)
open(p, "w", encoding="utf-8").write(s)
print("ok")
