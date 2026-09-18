# Lane 409-T22-UB3-cutoff-datum

## Theorems

No new theorem was closed. The intended statements are `exists_cutoff` and
`isCutoffDatum_realizes_zeroExtension` from U-B3.

## Files

Added `research/T22/ATTEMPTS_UB3.md`, `research/T22/axioms_ub3.lean`, and the
basic domain probe `research/T22/probes/cutoff_datum_closes.lean`.

## Gaps

The pinned Mathlib reports `unknown identifier` for both
`exists_smooth_tsupport_subset` and `exists_contDiff_one_nhds_of_subset`. The
zero-extension pairing bridge required by the second theorem is also absent from
current T22 imports. No prohibited placeholder was introduced.

## Commands

`#check` probes were run with `cd verification && lake env lean`; both named cutoff
lemmas failed with `unknown identifier`. The basic probe and axioms audit remain to
be run after a replacement cutoff API is identified.

The probe gate also stops before elaboration because the dependent `Domain.olean` has not
been built in this worktree (`object file .../Section3/T22/Domain.olean does not exist`).
