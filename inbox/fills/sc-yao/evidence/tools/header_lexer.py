#!/usr/bin/env python3
"""Lexer adapted from sc-garble evidence at exchange a73072f1 (retained in inputs).

Retains offsets while masking nested comments/strings; records declaration headers,
including include/omit/open prefixes. The sc-yao checker supplies its own scope policy.
"""
import re

DECL = re.compile(r'^(?:@\[[\s\S]*?\][ \t\n]*)?'
    r'(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*'
    r'(?P<kind>theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\b', re.M)
COMMAND = re.compile(r'^(?:namespace|section|end|variable|open|include|omit|set_option|attribute)\b', re.M)

def lex(text):
    """Blank nested comments and strings while preserving all offsets."""
    code = list(text)
    comments = []
    i = 0
    while i < len(text):
        start = i
        if text.startswith('/-', i):
            depth = 1
            i += 2
            while depth:
                if text.startswith('/-', i): depth += 1; i += 2
                elif text.startswith('-/', i): depth -= 1; i += 2
                else: i += 1
                if i > len(text): raise ValueError('unclosed comment')
            comments.append((start, i))
        elif text.startswith('--', i):
            i = text.find('\n', i)
            if i < 0: i = len(text)
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if code[j] != '\n': code[j] = ' '
    return ''.join(code), comments

def declarations(text):
    code, comments = lex(text)
    matches = list(DECL.finditer(code))
    boundaries = sorted([m.start() for m in matches] + [m.start() for m in COMMAND.finditer(code)]
                        + [len(code)])
    result = []
    for index, match in enumerate(matches):
        start = match.start()
        end = next(x for x in boundaries if x > start)
        end = start + len(code[start:end].rstrip())
        depth = 0
        cut = None
        pos = match.end()
        while pos < end:
            c = code[pos]
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            if depth == 0 and (code.startswith(':=', pos) or
                re.match(r'\b(?:where|by)\b', code[pos:]) or c == '|'):
                cut = pos
                break
            pos += 1
        cut = end if cut is None else cut
        token = re.match(r'\s*([^\s({\[:=]+)', code[match.end():cut])
        name = token.group(1) if token else '@anonymous_' + str(index)
        prefix = ''
        previous = code[:start].rstrip()
        if previous:
            line_start = previous.rfind('\n') + 1
            if re.fullmatch(r'(?:include|omit|open)\b[^\n]*\bin', previous[line_start:]):
                prefix = text[line_start:len(previous)] + '\n'
        doc = next(((a, b) for a, b in reversed(comments)
                    if b <= start and text[a:a+3] == '/--'), None)
        result.append(dict(name=name, kind=match.group('kind'),
            header=prefix + text[start:cut], full=text[start:end],
            start=start, end=end, cut=cut,
            doc=text[doc[0]:doc[1]] if doc else '', doc_range=doc))
    return result

