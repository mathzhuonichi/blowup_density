# Lane 162 — A01 constructor row c6 (divergence)

## Result

The new module `Section4/A01/ConstructorDivergence.lean` closes the requested c6 split:

1. `divergence_ae_of_cylinder` descends the three length-one spatial cylinder words and proves the
   diagonal derivative sum of a smooth ordinary representative is zero a.e.
2. `divergence_of_cylinder_pointwise_of_contDiff` assumes the c3 spatial smoothness handoff for a
   candidate velocity and returns the exact `ClassicalSolutionR.divergence` conclusion.

Both declarations print exactly `[propext, Classical.choice, Quot.sound]`.  The conformance file
contains examples with `u := 0`, `U := 0`, the vendor zero smooth field, and zero spacetime velocity.

## Source audit and the actual divergence notion

The brief points to `vendor/HeliCorgi/Formal/R3InversionConsistency.lean:139`.  Reading the cited
source shows that
`MNS2.r3DecodedFrequency_incompressible_ae_decoder` is a theorem about HeliCorgi's separate
frequency carrier `R3L2SolenoidalSubmodule`: it constructs a `C¹` physical representative, proves
its classical divergence is zero everywhere, and identifies it a.e. with the decoder.

The cylinder pair from `Horizon.localTheory_on_prescribed_horizon` instead carries

```lean
value 1 (u t) ∈ EulerLiftedGradientSpace.divergenceFreeSpace 1 1 0.
```

The definition is in `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:1340`:

```lean
def divergenceFreeSpace (κ : ℝ) (m : Vector3) : Submodule ℝ (LiftL2 period) :=
  (gradientSpace period κ m).orthogonal
```

Thus it is not definitionally the equation `∑ᵢ ∂ᵢuᵢ = 0`.  Its immediate coordinate-free
content is the compact-test weak identity `weak_divergence_test_integral` (`EulerProof.lean:1354`).
The vendor performs the weak-to-classical analysis in
`Euler.ClassicalDivergence.divergenceFree_classical_divergence_zero`: a smooth representative `g`
of a member of `divergenceFreeSpace period κ m` obeys

```lean
∀ x, ∑ i : Fin 3,
  (fieldDerivative period (coordinateDirection κ m i) g x) i = 0.
```

For `period = κ = 1`, `m = 0`, and the angle-independent representative
`g (x,θ) = Z.field x`, `MeanCylinderSolenoidal.fieldDerivative_spatial` reduces this verbatim to
`∑ i, (fderiv ℝ Z.field x (coordinateVector i)) i = 0`.  No Fourier normalization enters.

Before recording that there was no Section4-local lemma exposing a direct cylinder word-sum
equation, the required search was run over every mandated tree:

```text
grep -rnE 'divergence.*word|word.*divergence|divergenceFreeSpace' \
  formalization/NSFormalization/Section4/D01 \
  formalization/NSFormalization/Section4/A03 \
  formalization/NSFormalization/Section4/A04 \
  formalization/NSFormalization/Section4/A01 \
  formalization/NSFormalization/Section4/C01
```

The hits were only the divergence-free clauses in A01 horizon/continuation modules; there was no
coordinate-word sum bridge.  The bridge used here is therefore the vendor's already-proved
`ClassicalDivergence` theorem, not a new weak-divergence argument.

## Proof route

For a fixed cylinder slice:

1. Set `n := 1`; `n ≤ q+1` for every `q`.
2. For each `i : Fin 3`, use `word_descent_ae_top` to choose `Zi i : EulerMeanSolenoidal.L2` with
   `ordinaryLift (Zi i) = word 1 u hn (fun _ => i.succ)`.
3. Use `word_descent_ae_full` and `wordField_field` to identify
   `Zi i x i = (fderiv ℝ Z.field x (coordinateVector i)) i` a.e.
4. Lift `Z.field =ᵐ ⇑U` through the measure-preserving projection to obtain the smooth
   angle-independent cylinder representative of `value 1 u`.
5. Apply `divergenceFree_classical_divergence_zero`; simplify its cylinder derivative formula with
   `fieldDerivative_spatial`, `coordinateDirection`, and `coordinateVector`.
6. Sum the three a.e. component identities.  This explicitly yields zero for the sum of the three
   descended words, and then for the stated classical derivative sum.

For the pointwise handoff, at each `t ∈ Ico 0 T`:

1. Apply the first theorem to `u τ`, `U τ`, `Z τ`, where `τ : Icc 0 T` is the same time.
2. The derivative sum of `Z τ` is continuous, so `Continuous.ae_eq_iff_eq volume` turns a.e. zero
   into equality everywhere.
3. The candidate slice and `(Z τ).field` are continuous and agree a.e. through `U τ`, so the
   same lemma identifies them as functions.
4. Unfold `spatialDivergence`/`spatialDerivative` and rewrite by this equality.

The family `Z : Icc 0 T → SmoothL2Field Space` is explicit in the pointwise theorem.  Constructing
that all-order smooth `L²` representative family is not silently assigned to c6; it is part of the
carrier/c3 constructor work.

## Failed probes retained as diagnostics

The first prototype omitted two namespaces.  Lean correctly reported:

```text
Function expected at SmoothL2Field
Hint: The identifier `SmoothL2Field` is unknown
Unknown identifier `localFieldLift`
```

Opening `EulerLpTranslation` and `EulerMetricTransport` fixed the spellings.

The first-order word reduction was initially attempted with `rfl` after `wordField_field`; Lean
reported that `iteratedFDeriv ℝ 1 ...` was not definitionally the displayed `fderiv`.  The correct
API is the simp theorem `iteratedFDeriv_one_apply`.

The conformance probe also established that `SmoothL2Field` has no `Zero` instance:

```text
failed to synthesize instance of type class OfNat (SmoothL2Field Space) 0
```

The inhabitant is the existing `EulerLpTranslation.SmoothL2Field.zeroField` from
`Euler.LpSmoothFieldAlgebra`; no duplicate zero-field declaration was added.
