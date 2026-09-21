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

P5.2 closes by adapting the torus finite-sum calculus. Velocity slices are
smooth globally from I03; normalized pressure slices are globally smooth by
subtracting a spatial constant. Thus the full spatial Laplacian calculation
can be reused, while only the final momentum statement is restricted to Ω.
The neighborhood where one velocity stays nonzero forces every other velocity
to vanish, which proves crossTransport_eq_zero, including ball boundaries.

Resolved elaboration diagnostics: `typeclass instance problem is stuck
NormedSpace ℝ ?m.37` came from indentation in the empty finite-sum case;
`Type mismatch smoothOnClosedSlab_finset_sum ?m.33 ...` required explicit
`Finset.univ`; the pressure-slice constant required `change` to expose the
constant time argument; the temporal smoothness proof required the explicit
point `(t,x)`. No extra mathematical hypotheses were needed.

P5.2 module and expanded exact-field probe pass with zero output. All 45
module definitions/theorems print exactly [propext, Classical.choice, Quot.sound].
First make check stopped with `AssertionError: Source changed: rerun the article
axiom audit`. Running the required article audit and refreshing AXIOM_AUDIT.json
is necessary because the two new modules change the source fingerprint; this
additional existing-file edit is authorized by the common closing procedure.

Final gate: full article audit passed (56 targets, no forbidden axioms); reviewed
report copied to AXIOM_AUDIT.json. Regenerated graph is unchanged. `make check`
then passed, including contract policy tests. M316_B coverage remains Partial.
