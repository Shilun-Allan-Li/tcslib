from pathlib import Path
path = Path('evidence/tools/explicit_unfold_scan.py')
text = path.read_text()
anchor = '\ndef scan(path, source):'
helper = r'''
def unfolding_heads(match):
    if match[1] is not None:
        body = re.split(r'\bat\b', match[1], maxsplit=1)[0]
        return identifier.findall(body)
    body = match[2]
    pieces, start, depth = [], 0, 0
    for index, character in enumerate(body):
        if character in '([{':
            depth += 1
        elif character in ')]}':
            depth -= 1
        elif character == ',' and depth == 0:
            pieces.append(body[start:index])
            start = index + 1
    pieces.append(body[start:])
    result = []
    for piece in pieces:
        piece = piece.strip().removeprefix('←').strip()
        if piece.startswith('-'):
            continue
        found = identifier.match(piece)
        if found and found[0] not in {'show', 'by', 'fun', 'if'}:
            result.append(found[0])
    return result
'''
assert anchor in text
text = text.replace(anchor, helper + anchor)
text = text.replace('for token in identifier.findall(body):', 'for token in unfolding_heads(match):')
Path('evidence/development/explicit-unfold-v2.py').write_text(path.read_text())
path.write_text(text)
