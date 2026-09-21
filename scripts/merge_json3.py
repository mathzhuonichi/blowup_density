#!/usr/bin/env python3
"""Three-way merge for contracts.json / work_items.json during a lane rebase.
Usage: merge_json3.py <path> <merge-base-json> <integration-json> <lane-json>
Result: integration's file + the entries the lane changed relative to the merge-base."""
import json, sys
p, fb, fi, fl = sys.argv[1:5]
base, integ, lane = (json.load(open(x)) for x in (fb, fi, fl))
if p.endswith('contracts.json'):
    ids = {c['id'] for c in integ['contracts']}
    bids = {c['id']: c for c in base['contracts']}
    for c in lane['contracts']:
        if c['id'] not in ids:
            integ['contracts'].append(c)
        elif c != bids.get(c['id']):  # lane modified an existing entry
            integ['contracts'] = [c if x['id'] == c['id'] else x for x in integ['contracts']]
else:
    bitems = {it['id']: it for it in base['items']}
    iitems = {it['id']: it for it in integ['items']}
    for it in lane['items']:
        if it != bitems.get(it['id']):
            iitems[it['id']] = it
    integ['items'] = [iitems[k] for k in iitems]
with open(p, 'w') as f:
    json.dump(integ, f, indent=2, ensure_ascii=False); f.write('\n')
