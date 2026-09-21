# Lane 497 attempts

P5.1 constructs cube-free placements from raw packet data, uses the full open
presingular slab as its neighborhood, and normalizes pressure with T23.
Global support follows from T15 raw scaled support lemmas, without periodization.

First elaboration: `simpa only [inv_pow, inv_inv, sub_add_cancel] using h`
normalized the pressure amplitude but not the opaque `scaledPressure` target,
producing `Type mismatch: After simplification, term h`. Replaced this with
an explicit horizon identity, `rw [he] at h`, and `exact h`.

Authorized existing-file edits: entrypoints.json (new proof module registration),
T24_SPLIT.md (unit status). No canonical existing Lean module is changed.

P5.1 gate: dependency build and component build pass; direct Lean and the field
probe emit zero output. All 16 definitions/theorems print the standard three axioms.
