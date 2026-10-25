import sys
p = sys.argv[1]
s = open(p, encoding="utf-8").read()
a = '(The report\'s "docstring 239–269" starts inside ,\n  whose docstring is 236–241 and statement 242–247.)'
b = '(The report\'s "docstring 239–269" starts inside the\n  docstring of `acceptLang_mem_NTIME`, lines 234–241; its statement is 242–247.)'
assert s.count(a) == 1
open(p, "w", encoding="utf-8").write(s.replace(a, b))
print("fixed")
