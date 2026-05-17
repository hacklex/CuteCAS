#!/usr/bin/env python3
"""Restore newlines in FStar.CAS.Matrix.Determinant.fst after a catastrophic
Set-Content -NoNewline collapsed the file to one line. F* is whitespace
insensitive, so we just need to insert separators between tokens that wound
up adjacent.  Insert a newline before any top-level F* keyword that is
preceded by a non-separator character.
"""
import re, sys

path = 'FStar.CAS.Matrix.Determinant.fst'
text = open(path, 'r', encoding='utf-8').read()

# Keywords that, in this codebase, typically begin a top-level construct.
# Order matters for multi-word patterns (longer first).
keywords = [
    r'#push-options',
    r'#pop-options',
    r'#reset-options',
    r'#restart-solver',
    r'inline_for_extraction',
    r'irreducible',
    r'private\s+let',
    r'private\s+val',
    r'unfold\s+let',
    r'noeq\s+type',
    r'noeq',
    r'assume\s+val',
    r'assume',
    r'module\s+[A-Z]',
    r'open\s+[A-Z]',
    r'class\s+[a-zA-Z]',
    r'instance\s+[a-zA-Z]',
    r'type\s+[a-zA-Z]',
    r'val\s+[a-zA-Z_]',
    r'let\s+rec',
    r'let\s+[a-zA-Z_]',
]

# Apply each pattern: insert a newline before the keyword when it is
# preceded by an alphanumeric/closing punct character (i.e. they got glued
# together when newlines were stripped).
prev_chars = r'[a-zA-Z0-9_)\]\}>?!\']'

for kw in keywords:
    pat = re.compile(r'(' + prev_chars + r')(' + kw + r')')
    text = pat.sub(r'\1\n\2', text)

# Comments: `(*` preceded by an alnum, and `*)` followed by alnum.
text = re.sub(r'(' + prev_chars + r')\(\*', r'\1\n(*', text)
text = re.sub(r'\*\)(' + prev_chars + r')', r'*)\n\1', text)

# Ensure ending with a newline.
if not text.endswith('\n'):
    text += '\n'

open(path, 'w', encoding='utf-8', newline='\r\n').write(text)
print('Done. New length:', len(text), 'lines:', text.count('\n'))
