#!/usr/bin/env python3
"""Check reader-document correspondence and layout logs, not mathematical correctness."""
import json
import hashlib
import re
from reader_terminology import PROTECTED
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'paper'
REVISED = PAPER / 'revised'
RESULT = re.compile(r'\\begin\{(theorem|proposition|lemma|corollary)\}(.*?)\\end\{\1\}', re.S)


def expand(path):
    text = path.read_text()
    return re.sub(r'\\input\{([^}]+)\}', lambda m: expand(path.parent / (m[1] + '.tex')), text)


def main():
    revised = expand(REVISED / 'blowup_density_revised.tex')
    revised_statements = [(m[1], m[2]) for m in RESULT.finditer(revised)]
    assert len(revised_statements) == 26, 'Expected 26 numbered article statements'
    main_labels = {'thm:main', 'thm:Rmain'}
    titled = re.findall(r'\\begin\{(?:theorem|proposition|lemma|corollary|remark|definition)\}\[[^\]]*\]\s*\\label\{([^}]+)\}', revised)
    assert set(titled) == main_labels and len(titled) == 2, 'Only the two main theorems retain subtitles'
    prose = PROTECTED.sub(' ', revised.split(r'\begin{thebibliography}', 1)[0])
    assert not re.search(r'\b(?:insertion|inserted|packet|singular forces?)\b', prose, re.I), 'Retired article terminology reintroduced'
    assert not re.search(r'\b(?:Lean|Mathlib|compatibility|formalization)\b', prose, re.I), 'Software discussion belongs only in the guide'
    revised_labels = re.findall(r'\\label\{([^}]+)\}', revised)
    assert len(re.findall(r'\\section\{', revised)) == 4, 'The article has four numbered sections'
    assert r'\section{Conclusion}' not in revised
    assert r'\appendix' not in revised, 'The concise revision must have no appendices'
    assert len(revised_labels) == len(set(revised_labels)), 'Duplicate label'
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', revised)
    assert set(refs) <= set(revised_labels), 'Missing reference target'
    cites = {key for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', revised) for key in group.split(',')}
    bib = re.findall(r'\\bibitem\{([^}]+)\}', revised)
    assert len(bib) == len(set(bib)) and cites == set(bib), 'Bibliography mismatch'
    guide = (PAPER / 'formalization_guide.tex').read_text()
    assert len(re.findall(r'\\section\{', guide)) == 4, 'The guide should have four sections'
    assert 'Article statement &' in guide and 'Article result &' not in guide
    assert r'\section{Differences in proof methods}' in guide
    assert r'\section{Classical results available for future reference}' in guide
    assert r'L^2_t\dot H^{-1/2}_x' not in guide, 'Proposition 4.4 uses the inhomogeneous norm'
    assert r'L^2_tH^{-1/2}_x' in guide
    guide_labels = re.findall(r'\\label\{([^}]+)\}', guide)
    assert {r for r in re.findall(r'\\ref\{([^}]+)\}', guide) if '#' not in r} <= set(guide_labels), 'Missing guide section target'
    guide_cites = {key for group in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}', guide) for key in group.split(',')}
    guide_bib = re.findall(r'\\bibitem\{([^}]+)\}', guide)
    assert len(guide_bib) == len(set(guide_bib)) and guide_cites == set(guide_bib), 'Guide bibliography mismatch'
    classical = guide.split(r'\section{Classical results available for future reference}', 1)[1].split(r'\end{enumerate}', 1)[0]
    entries = classical.split(r'\item ')[1:]
    assert len(entries) == 6 and all(r'\cite[' in entry for entry in entries), 'Each classical entry needs a located literature citation'
    mapped = re.findall(r'\\mapped\{([^}]+)\}\{([^}]+)\}', guide)
    coverage = re.findall(r'\\mapped\{[^}]+\}\{([^}]+)\}\s*&\s*\\coverage\{([^}]+)\}', guide)
    assert len(coverage) == len(mapped), 'Every article row needs an explicit coverage label'
    status = dict(coverage)
    assert set(status.values()) <= {'Closed', 'Partial'}
    partial = {'prop:local', 'prop:multiple', 'prop:conservative'}
    assert {label for label, state in status.items() if state == 'Partial'} == partial
    assert status['rem:peaks'] == 'Closed' and 'forceAmplitude_diverges' in guide
    assert status['cor:boundary'] == 'Closed' and status['thm:Rinsert'] == 'Closed'
    assert status['lem:correction'] == 'Closed' and 'correctionStatementArticle_holds' in guide
    assert 'wholeSpaceInsertion_holds' in guide
    assert status['thm:packet'] == 'Closed' and 'source_breakdown' in guide
    assert 'kernel-checked proof' in guide and 'No unproved theorem input' in guide
    assert r'\paragraph{Boundary IBP' not in guide
    result_map = (ROOT / 'formalization/blueprint/RESULT_MAP.md').read_text()
    for label, state in coverage:
        assert f'`{label}` | {state} |' in result_map, ('Blueprint coverage drift', label)
    assert 'boundaryInsertion_from_data' in guide
    assert 'H^1$-uniform' in guide and 'not proved' in guide
    expected_map = {(kind.capitalize(), re.search(r'\\label\{([^}]+)\}', body)[1])
                    for kind, body in revised_statements} | {('Remark', 'rem:peaks')}
    assert len(mapped) == len(expected_map) and set(mapped) == expected_map, 'Incomplete or duplicate result mapping'
    locations = re.findall(r'\\source\{([^}]+)\}\{(\d+)\}\{([^}]+)\}\{(theorem|def)\}', guide)
    assert locations and r'\checked{' not in guide, 'Use proof locations, not acceptance wrappers'
    roots = {'F/': ROOT / 'formalization/NSFormalization', 'B/': ROOT / 'verification/Bindings'}
    for filename, line, declaration, kind in locations:
        source = roots[filename[:2]] / (filename[2:] + '.lean')
        actual = source.read_text().splitlines()[int(line) - 1]
        assert re.search(r'\b' + kind + r'\s+' + re.escape(declaration) + r'(?=\s|[:({]|$)', actual), (source, line, declaration)
    rows = re.split(r'\\mapped\{', guide)[1:]
    assert all(r'\source{' in row for row in rows), 'Missing proof location in a mapped row'
    for label in re.findall(r'\\paperref\{([^}]+)\}', guide):
        assert label.startswith('#') or label in revised_labels, label
    for name in re.findall(r'\\code\{([^}]+\.lean)\}', guide):
        if name.startswith('#'):
            continue
        if name in {'R3ActualCandidate.lean', 'R3FiniteEnergyComparison.lean', 'ComparatorR3Theorem.lean'}:
            path = ROOT / 'vendor/NavierStokesAndEuler/NavierStokes' / name
        elif name.startswith('verification/'):
            path = ROOT / name
        elif name.startswith(('Section3/', 'Section4/', 'Source/')):
            path = ROOT / 'formalization/NSFormalization' / name
        else:
            path = ROOT / 'verification/Tests' / name
        assert path.is_file(), path
    corpus = json.loads((ROOT / 'reference/sources.json').read_text())['sources']
    for doc, keys in [('article', bib), ('guide', guide_bib)]:
        catalog = {entry['citation_keys'][doc]: entry for entry in corpus if doc in entry['citation_keys']}
        assert set(catalog) == set(keys), ('Source inventory mismatch', doc)
        source_text = (REVISED / 'references.tex').read_text() if doc == 'article' else guide
        for key, entry in catalog.items():
            body = re.search(r'\\bibitem\{' + re.escape(key) + r'\}(.*?)(?=\\bibitem|\\end\{thebibliography\})', source_text, re.S)[1]
            assert ' '.join(body.split()) == ' '.join(entry['bibliography_tex'].split()), ('Bibliography style drift', key)
    for entry in corpus:
        assert entry['files'], entry['id']
        for record in entry['files']:
            data = (ROOT / record['path']).read_bytes()
            assert hashlib.sha256(data).hexdigest() == record['sha256'], record['path']
            if record['path'].endswith('.pdf'):
                assert data.startswith(b'%PDF-'), record['path']
    missing = [entry['id'] for entry in corpus if entry['coverage'] == 'metadata_only']
    print(f"Source inventory: {len(corpus)} works; missing full text: {', '.join(missing) or 'none'}. Chapter-only coverage is explicitly marked.")
    registry = json.loads((ROOT / 'verification/contracts.json').read_text())['contracts']
    for c in registry:
        test = ROOT / 'verification' / (c['test_module'].replace('.', '/') + '.lean')
        assert c['declaration'].split('.')[-1] in test.read_text(), test
    for name in ('blowup_density_revised', 'formalization_guide'):
        text = (ROOT / 'output/pdf' / (name+'.log')).read_text()
        assert not re.search(r'Warning|Overfull|Underfull|undefined|^!', text, re.M), name
        assert (ROOT / 'output/pdf' / (name+'.pdf')).is_file()
    print(f'{len(revised_statements)} numbered article statements and their guide mappings checked.')
    print(f'{len(mapped)} article results mapped, including the numbered remark; proof declaration kinds and source line numbers verified.')
    print(f'{len(revised_labels)} article labels resolved.')
    print(f'{len(bib)} bibliography entries resolved; {len(registry)} registry declarations found; guide code paths verified.')
    print('Both PDF build logs are clean. Scope: structural checks, not a new proof certification.')


if __name__ == '__main__':
    main()
