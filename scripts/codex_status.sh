#!/usr/bin/env bash
# One-line status per codex lane: running/done, log size, minutes elapsed, last non-empty log line.
cd /data_8T/ping/blowup_density/tmp/codex 2>/dev/null || exit 0
for r in run_*.sh; do [ -f "$r" ] || continue; L=${r#run_}; L=${L%.sh}
  st="running"; [ -f "$L.DONE" ] && st="done rc=$(cat "$L.DONE")"
  sz=$(wc -c < "$L.log" 2>/dev/null || echo 0)
  t0=$(grep -m1 '^== start' "$L.log" 2>/dev/null | awk '{print $3}')
  mins=""; [ -n "$t0" ] && mins=$(( ( $(date -u +%s) - $(date -u -d "$t0" +%s) ) / 60 ))m
  last=$(grep -v '^\s*$' "$L.log" 2>/dev/null | tail -1 | cut -c1-90)
  printf '%-32s %-12s %7sB %5s  %s\n' "$L" "$st" "$sz" "$mins" "$last"
done
