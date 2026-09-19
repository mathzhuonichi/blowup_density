# Lane 477 / U2 attempts

Initial scope: exact G0 counterexample and repaired quantifiers; raw local
correction, spatial extension and un-periodised cross transport.

The implementation layer cannot import Contracts. Exact Spec checks therefore
run in a standalone research probe; no substitute API is introduced.

Initial inspection: `sed` on a guessed T14/PacketImport.lean and
`rg` on T16/CompactCorrection.lean failed with `No such file or directory`.
The actual local radial-potential results live in T16/BallPotential.lean.

## Un-periodised cancellation: first elaboration

Replacing the lattice-support step with closure of the physical support gave:
```text
LocalCorrection.lean:174:4: error: Type mismatch: After simplification, term
  hy
 has type
  y ∈ Function.support fun x => scaledVelocity U x₀ T ε (t, x)
but is expected to have type
  parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y) ≠ 0
```
Fix: expose membership as a nonzero value before the definitional rescaling bridge.

Exposing membership still left the rescaling names unequal to the elaborator:
```text
LocalCorrection.lean:175:4: error: Type mismatch: After simplification, term
  hy
 has type
  @Ne Space (scaledVelocity U x₀ T ε (t, y)) 0
but is expected to have type
  @Ne Space (parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y)) 0
```
Next: unfold both rescalings explicitly.

## Cross transport endpoint

`simp only [spatialDerivative, hz, fderiv_const]` failed:
```text
LocalCorrection.lean:230:69: error: unsolved goals
⊢ fderiv ℝ (fun x => 0) x = 0
LocalCorrection.lean:231:40: warning: This simp argument is unused:
  fderiv_const
```
Fix: follow the checked T18 proof and finish the constant derivative with `simp`.

## Spatial transport warning

The cylinder agreement lemma closed, but emitted:
```text
SpatialExtension.lean:84:5: warning: Variable name `hr` is not explicitly referenced.
```
Removed the unnecessary positivity hypothesis: the nonzero spatial cutoff
already places the queried point in the ball, which suffices for the segment.
Additional guessed-path searches for T17/Support.lean and
Paper1/CorrectionDerivativeBounds.lean returned `No such file or directory`;
no proof depended on these paths.

## Closed route and exact remaining obligations

The original global-hypothesis gap is now split constructively:

1. `exists_spatial_solenoidal_extension`: curl of the local radial potential
   times a fixed spatial bump; full spatial-slab smoothness/divergence and
   agreement on `ball x₀ (r/2)`.
2. `exists_solenoidal_window_extension`: a fixed time cutoff gives globally
   smooth, globally solenoidal `V`, equal to `v` on the closed window.
3. `physicalCorrection_eq_of_cylinder` and
   `correctionForce_eq_of_open_agreement`: global function equalities,
   including all uncontrolled exterior points.
4. `exists_matching_global_correction`: one `V` and one threshold work for
   **every** scale in that range. Hence equality of all correction and force
   jets is actual function congruence, not an assumed estimate.
5. `exists_localCorrection_with_derivative_bounds`: shrink the constructed
   core's threshold and retain **one D**, the same force, all core properties,
   domain support, global force smoothness/compactness, and the two exact
   I02 derivative-rate statements.

Still open (not represented by placeholder declarations):

### R1. Registered matching supplier and the remaining norm fields

The raw implementation cannot import Contracts. At the contract-facing bridge,
with `ν : ℝ`, `P : PacketAPI ν`, `T δ : ℝ`, `x₀ : Space`, local reference `v`,
and a *jointly chosen* raw `D`, the remaining matching target contains the
following exact Lean conjunction (open the V1 contract namespace):

```lean
∃ (C : CorrectionAPI ν P) (A : ScalingAPI ν P),
  A.correction = C ∧ C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧
  D.ε₀ ≤ A.ε₀ ∧
  (∀ ε ∈ Set.Ioc (0 : ℝ) D.ε₀,
    D.correction ε = C.correction ε ∧
    NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε)
```

This must be **constructed from** the local reference, not threaded as a new
input or inferred from an arbitrary inhabited correction. The chosen cutoff fields,
the chosen packet and the `A.correction = C` equation must stay aligned. The
current raw constructor and fixed-extension theorem do not claim to provide
this registered pair. A cutoff generated independently by I02 must not simply
be identified with our chosen cutoff.

At the same chosen family the exact remaining norm targets include, with
`Data := BlowupDensity.Contracts.V1.Data` in the contract-facing context:

```lean
∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) D.ε₀,
  Data.energyENorm T (D.correction ε) ≤
    ENNReal.ofReal (C * ε ^ ((3 : ℝ) / 2))
```

and (after I03 matching, for each `q` with `1 ≤ q`, `0 ≤ s`, `s ≤ 1`):

```lean
∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) D.ε₀,
  Data.forceSobolevENorm q s
      (NSFormalization.Section3.T23.correctionForce ν v D ε) ≤
    ENNReal.ofReal (C *
      (ε ^ (2 / q.toReal - 1 / 2) + ε ^ (2 / q.toReal - 1 / 2 - s)))
```

No equality between that measurable-path infimum and T23's per-slice domain
integral is asserted. The latter bridge remains U6's separate obligation.
The mixed-Lebesgue bound and energy/gradient packaging likewise remain open.
The new jet estimates do not by themselves constitute these norm bounds.

### R2. Canonical G0 location

The exact Spec API counterexample and repaired definition are kernel checked in
`probes/g0_counterexample.lean`, which copies the original Spec verbatim.
`StatementRepair.lean` only contains the raw cutoff and threshold obstruction.
Moving the **full** literal and repaired statements to that canonical module
requires the canonical domain/insertion vocabulary. We deliberately did not
import Contracts into the proof implementation or introduce a second placement
record. This requested location is unfinished. The exact repaired statement is
recorded in the SPEC_ISSUES G0 addendum; no proof of it is claimed.

### Error status

There is **no remaining compiler error** in the delivered Lean files. The exact
failed elaborations above are retained and were repaired. R1/R2 are unimplemented
assembly/vocabulary obligations, not the final goals of a failing proof that
has been hidden with an admission. The available spatial/window bridge removes
the original local-to-global smoothness obstruction, but does not silently
complete the registered supplier or any unproved norm estimate.

Potential identity caveat: the core retains the original reference's radial
potential on all of spacetime. A whole-space supplier for `V` has the radial
potential of `V`, which only agrees on the controlled cylinder. Do not infer
global equality of those potentials from the correction equality. The G0
repair's raw `D` copies the supplier potential; the boundary API does not assert
the core's stronger global original-reference potential formula. This adapter
distinction must be retained when completing R1/R2.
