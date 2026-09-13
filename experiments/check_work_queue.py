#!/usr/bin/env python3
"""Validate ownership and distinguish specification work from proof completion."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    nodes = {x['id']: x for x in json.loads((ROOT / 'formalization/blueprint/tasks.json').read_text())['nodes']}
    queue = json.loads((ROOT / 'collaboration/work_items.json').read_text())
    registered = {c['id'] for c in json.loads((ROOT / 'verification/contracts.json').read_text())['contracts']}
    items = queue['items']
    assert len(items) == len({x['id'] for x in items})
    assert {x['id'] for x in items} == set(nodes)
    states = {'ready', 'needs-specification', 'reference-available', 'deferred', 'in-progress', 'in-review', 'merged'}
    kinds = {'reference', 'specification', 'compatibility', 'proof', 'assembly'}
    for item in items:
        assert item['state'] in states and item['kind'] in kinds
        assert item['owner'] is None or item['owner'] in queue['collaborators']
        assert set(item['contracts']) <= registered
        if item['kind'] in {'proof', 'assembly'} and item['state'] in {'ready', 'in-progress', 'in-review', 'merged'}:
            assert item['contracts'], f'Proof work needs a registered contract: {item["id"]}'
        text = (ROOT / f'collaboration/tasks/{item["id"]}.md').read_text()
        assert nodes[item['id']]['contract'] in text, f'Stale goal: {item["id"]}'
        assert f'State: {item["state"]}.' in text, f'Stale state: {item["id"]}'
        assert f'Owner: {item["owner"] or "unassigned"}.' in text, f'Stale owner: {item["id"]}'
    print(f'{len(items)} work items: ownership, contract registration and task cards consistent.')


if __name__ == '__main__':
    main()
