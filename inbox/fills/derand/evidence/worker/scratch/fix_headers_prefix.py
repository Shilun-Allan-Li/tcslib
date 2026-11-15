from pathlib import Path
path = Path('evidence/tools/frozen_headers.py')
text = path.read_text()
Path('evidence/development/frozen-headers-v1.py').write_text(text)
old = "openin = re.search(r'(?m)^open [^\\n]+ in\\s*$', prior)"
new = "openin = re.search(r'(?m)^open [^\\n]+ in[ \\t]*\\Z', prior)"
assert old in text
text = text.replace(old, new)
path.write_text(text)
