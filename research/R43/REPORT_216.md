# Lane 216 report — critical datum path

## 1. Delivered result

The new module `NSFormalization.Section4.R43.CriticalDatumPath` constructs the
six homogeneous datum paths used by lane 175:

- velocity at orders `1/2` and `3/2`;
- Laplacian, advection, pressure gradient, and force at order `1/2`.

All six `IsHomogeneousSliceDatum` fields are proved. The four spatial
compatibilities are also unconditional: `order_shift`, `laplacian_symbol`,
`velocity_transverse`, and `pressure_longitudinal`.

The exact consumer structure is assembled by `criticalDatumPath`, and
`exists_criticalDatumPath` returns `Nonempty (CriticalDatumPath w hf)` under the
single fallback proposition `CriticalDatumInputs w hf`. The corollary
`rcritical1_of_classical` has no `hcrit` binder and applies lane 214's
`rcritical1_of_hcrit'` to this assembled carrier.

## 2. Construction and mathematical content

The new homogeneous datum constructor is the bounded Bessel-to-homogeneous
multiplier

`|ξ|^s (1 + |ξ|²)^(-s/2)`.

It converts an inhomogeneous order-`s` angular datum into a homogeneous datum of
the same physical distribution for every `s ≥ 0`. Applied to the smooth
square-integrable jets already available for classical solution slices, it
supplies all six carriers. `MemForceR` is sufficient for the force slice at
order `1/2`; G3 needs no extra slicewise integrability premise.

The order-shift identity follows by comparing the same angular Fourier
transform at orders `1/2` and `3/2`. The Laplacian identity is proved from two
physical directional-derivative Fourier identities and normalized angular
dilation. Transversality and longitudinality are transported from the existing
order-zero divergence-free and curl-free identities through the common radial
half-order weight, then discharged by the Leray multiplier lemmas.

## 3. Exact remaining condition

The result is not unconditional because the current tree does not provide a
smooth homogeneous order-`1/2` datum path for an arbitrary
`ClassicalSolutionR`. A01 lane 169 differentiates its local-theory/Duhamel
carrier and does not export the missing representative-to-classical momentum
transport.

`CriticalDatumInputs` therefore contains exactly:

1. `ContDiffOn ℝ ∞ (criticalVelocityHalf w) (Ico 0 T)`;
2. the datum-level momentum identity for its derivative on `Ioo 0 T`.

No spatial carrier, symbol identity, pressure fact, trilinear estimate, pairing
identity, or energy inequality is assumed. The conformance file proves that
`A04.zeroSol` with `f = 0` satisfies this structure, so it is a genuine
restriction of the standard classical-solution time regularity rather than a
vacuous premise.

For R43 G3/G4/S6, the new force result is slicewise only. Lane 165 already
closes the inhomogeneous `H^{1/2}` force-norm finiteness. A measurable
`L¹_t Ḣ^{1/2}` homogeneous datum path—and hence the homogeneous force-norm
finiteness, time primitive, and FTC regularity—remains open.

## 4. Conformance, verification, and commits

`research/R43/axioms_critical_datum.lean` audits every declaration in the new
module. Each prints exactly
`[propext, Classical.choice, Quot.sound]`; the zero-solution fallback witness
prints the same set.

The implementation was committed in the requested stages:

- `4220a6d` — six paths and all datum fields;
- `0868d5a` — four spatial compatibility fields;
- `0eceb30` — the exact two-field time-path fallback;
- `cbd0734` — assembly and no-`hcrit` `eq:Rcritical1` corollary.

Verification completed with the target build, direct zero-output Lean check of
the module, the conformance file, and repository `make check`. The target build
replayed pre-existing dependency linter messages; the new module itself emitted
no warning or error, and its direct Lean gate was silent. `make check` exited
successfully while retaining the repository's pre-existing copied-source
`BoundaryCorollary.lean` admission notice and `source_hashes_match: false`
architecture status.
