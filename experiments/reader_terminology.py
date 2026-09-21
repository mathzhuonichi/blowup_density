"""Apply the reviewed terminology map to prose, preserving TeX math and identifiers."""
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
RULES = json.loads((ROOT / 'paper/terminology.json').read_text())['replacements']
PROTECTED = re.compile(
    r'\\begin\{(equation\*?|align\*?|gather\*?|verbatim)\}.*?\\end\{\1\}'
    r'|\\\[.*?\\\]|\\\(.*?\\\)|(?<!\\)\$.*?(?<!\\)\$'
    r'|\\(?:label|eqref|ref|paperref|code|src|nolinkurl|cite)(?:\[[^\]]*\])?\{[^}]*\}',
    re.S,
)

def replace_prose(text):
    for rule in RULES:
        pattern = r'\b' + r'\s+'.join(re.escape(x) for x in rule['old'].split()) + r'\b'
        def substitute(match):
            value = rule['new']
            return value[0].upper() + value[1:] if match[0][0].isupper() else value
        text = re.sub(pattern, substitute, text, flags=re.I)
    return text

def normalize_terms(text):
    pieces, end = [], 0
    for match in PROTECTED.finditer(text):
        pieces += [replace_prose(text[end:match.start()]), match[0]]
        end = match.end()
    pieces.append(replace_prose(text[end:]))
    return ''.join(pieces)
