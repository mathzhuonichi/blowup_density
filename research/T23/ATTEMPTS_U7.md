# Lane 478 — U7 attempts

Initial skeleton: exact Spec domain vocabulary and raw ClassicalSolutionOmega record.
No uniqueness theorem asserted. Box boundary integration is the first analytic target.

Source inspection: T11/Uniqueness delegates to periodic Flow uniqueness.
Mathlib divergence theorem uses HasFDerivAt (not the WithinAt name in the brief).

## Box IBP attempt 03

Missing FDeriv.Mul import and underconstrained constant direction in integral_add. Exact output:
```text
../formalization/NSFormalization/Section3/T23/BoxIntegration.lean:86:68: error(lean.invalidField): Invalid field `mul`: The environment does not contain `HasFDerivAtFilter.mul`, so it is not possible to project the field `mul` from an expression
  DifferentiableAt.hasFDerivAt (ContDiffAt.differentiableAt (hf x hx) one_ne_zero)
of type
  HasFDerivAtFilter f (fderiv ℝ f x) (nhds x ×ˢ pure x)
../formalization/NSFormalization/Section3/T23/BoxIntegration.lean:101:4: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a : Fin 3 → ℝ) in Icc a b,
    ((fun x => (fderiv ℝ f x) ?m.544) * g) a + (f * fun x => (fderiv ℝ g x) ?m.595) a ∂?m.601
in the target expression
  ∫ (x : Fin 3 → ℝ) in Icc a b, (fderiv ℝ f x) (Pi.single j 1) * g x + f x * (fderiv ℝ g x) (Pi.single j 1) ∂volume = 0

a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
f g : (Fin 3 → ℝ) → ℝ
hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
hg : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 g x
hzero : ∀ x ∈ frontier (Icc a b), f x = 0
j : Fin 3
F : (Fin 3 → ℝ) → Fin 3 → ℝ := fun x => Pi.single j (f x * g x)
hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 F x
hz :
  ∫ (x : Fin 3 → ℝ) in Icc a b, (fderiv ℝ f x) (Pi.single j 1) * g x + f x * (fderiv ℝ g x) (Pi.single j 1) ∂volume = 0
hderiv :
  ∀ x ∈ Icc a b,
    ∑ i, (fderiv ℝ F x) (Pi.single i 1) i = (fderiv ℝ f x) (Pi.single j 1) * g x + f x * (fderiv ℝ g x) (Pi.single j 1)
hcf : ContinuousOn f (Icc a b)
hcg : ContinuousOn g (Icc a b)
hdf : ContinuousOn (fderiv ℝ f) (Icc a b)
hdg : ContinuousOn (fderiv ℝ g) (Icc a b)
⊢ ∫ (x : Fin 3 → ℝ) in Icc a b, f x * (fderiv ℝ g x) (Pi.single j 1) =
    -∫ (x : Fin 3 → ℝ) in Icc a b, (fderiv ℝ f x) (Pi.single j 1) * g x
```
Fix: import FDeriv.Mul and give both integrability facts explicit types.

## Box IBP attempt 04

Product-rule summands were reversed; simplification did not select the single nonzero coordinate.
```text
../formalization/NSFormalization/Section3/T23/BoxIntegration.lean:92:85: error: Application type mismatch: The argument
  hp
has type
  HasFDerivAt (f * g) (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x
but is expected to have type
  HasFDerivAt (fun x => f x * g x) (g x • fderiv ℝ f x + f x • fderiv ℝ g x) x
in the application
  HasFDerivAt.comp x (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun x => ℝ) j)) hp
../formalization/NSFormalization/Section3/T23/BoxIntegration.lean:86:83: error: unsolved goals
a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
f g : (Fin 3 → ℝ) → ℝ
hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x
hg : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 g x
hzero : ∀ x ∈ frontier (Icc a b), f x = 0
j : Fin 3
F : (Fin 3 → ℝ) → Fin 3 → ℝ := fun x => Pi.single j (f x * g x)
hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 F x
hz : ∫ (x : Fin 3 → ℝ) in Icc a b, ∑ i, (fderiv ℝ F x) (Pi.single i 1) i = 0
x : Fin 3 → ℝ
hx : x ∈ Icc a b
hp : HasFDerivAt (f * g) (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x
hv : HasFDerivAt F (ContinuousLinearMap.single ℝ (fun x => ℝ) j ∘SL (g x • fderiv ℝ f x + f x • fderiv ℝ g x)) x
⊢ ∑ x_1,
      (g x * Pi.single j ((fderiv ℝ f x) (Pi.single x_1 1)) x_1 +
        f x * Pi.single j ((fderiv ℝ g x) (Pi.single x_1 1)) x_1) =
    g x * (fderiv ℝ f x) (Pi.single j 1) + f x * (fderiv ℝ g x) (Pi.single j 1)
```
Fix: match the product-rule order and use Finset.sum_eq_single before simplification.

## Energy integrability attempt 01

Line break before chained dot notation parsed as a dotted identifier.
```text
../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:165:6: error: Invalid dotted identifier notation: The name `continuousAt.continuousWithinAt` must be atomic
../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:168:6: error: Invalid dotted identifier notation: The name `continuousAt.continuousWithinAt` must be atomic
```
Fix: keep the field chain attached to its receiver.

## Zero-energy attempt 01
```text
../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:179:43: error(lean.unknownIdentifier): Unknown identifier `pow_eq_zero`
```
Fix: use sq_eq_zero_iff.mp.

## Derivative bound attempt 01

Composition spelling did not match under rewrite.
```text
../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:202:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fderiv ℝ (u.velocity ∘ fun f => (t, f)) x
in the target expression
  ‖fderiv ℝ (fun y => u.velocity (t, y)) x‖ ≤ max C 0

ν T : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
u : ClassicalSolutionOmega ν Ω a g T
hΩ : Bornology.IsBounded Ω
S : ℝ
hS : S < T
N : Set SpaceTime
hN : IsOpen N
hsub : Ico 0 T ×ˢ closure Ω ⊆ N
hu : ContDiffOn ℝ ∞ u.velocity N
hsub' : Icc 0 S ×ˢ closure Ω ⊆ N
hc : ContinuousOn (fderiv ℝ u.velocity) (Icc 0 S ×ˢ closure Ω)
C : ℝ
hC : ∀ x ∈ Icc 0 S ×ˢ closure Ω, ‖fderiv ℝ u.velocity x‖ ≤ C
t : ℝ
ht : t ∈ Icc 0 S
x : Space
hx : x ∈ closure Ω
hd : HasFDerivAt (u.velocity ∘ fun f => (t, f)) (fderiv ℝ u.velocity (t, x) ∘SL ContinuousLinearMap.inr ℝ ℝ Space) x
⊢ ‖fderiv ℝ (fun y => u.velocity (t, y)) x‖ ≤ max C 0
```
Fix: change the target to the composition spelling before rewriting.

## Derivative bound attempt 02
```text
../formalization/NSFormalization/Section3/T23/NoSlipUniqueness.lean:207:16: error: Type mismatch: After simplification, term
  hC (t, x) ⟨ht, hx⟩
 has type
  ‖fderiv ℝ u.velocity (t, x)‖ ≤ C
but is expected to have type
  ‖fderiv ℝ u.velocity (t, x)‖ * ‖ContinuousLinearMap.inr ℝ ℝ Space‖ ≤ C
```
Fix: explicitly rewrite ContinuousLinearMap.norm_inr (not a simp lemma).

## Supplier search and exact remaining obligations

Commands executed (after reading the referenced sources with `sed -n`):

```sh
grep -rnE 'theorem.*(noSlip|domain.*unique|unique.*domain)' formalization vendor --include='*.lean'
grep -rnEi 'theorem.*(divergence|stokes)|integral.*(regularLevel|regular_level)' verification/.lake/packages/mathlib/Mathlib --include='*.lean'
```

The first search found boundary-support lemmas and the conditional corrected
corollary, not a domain uniqueness supplier. The second returned:

```text
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:83:theorem for Bochner integral. The divergence theorem for Bochner integral
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:101:  in the main theorem `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:108:private theorem integral_divergence_of_hasFDerivWithinAt_off_countable_aux₁ (I : Box (Fin (n + 1)))
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:141:private theorem integral_divergence_of_hasFDerivAt_off_countable_aux₂ (I : Box (Fin (n + 1)))
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:266:theorem integral_divergence_of_hasFDerivAt_off_countable (hle : a ≤ b)
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:296:theorem integral_divergence_of_hasFDerivAt_off_countable' (hle : a ≤ b)
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:313:theorem integral_divergence_of_hasFDerivAt_off_countable_of_equiv {F : Type*}
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:427:theorem integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le (f g : ℝ × ℝ → E)
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:482:theorem integral_divergence_prod_Icc_of_hasFDerivAt_of_le (f g : ℝ × ℝ → E)
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:503:theorem integral2_divergence_prod_of_hasFDerivAt_off_countable (f g : ℝ × ℝ → E)
verification/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:550:theorem integral2_divergence_prod_of_hasFDerivAt (f g : ℝ × ℝ → E)
verification/.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:40:Henstock-Kurzweil integral, integral, Stokes theorem, divergence theorem
verification/.lake/packages/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:265:theorem hasIntegral_GP_divergence_of_forall_hasDerivWithinAt
verification/.lake/packages/mathlib/Mathlib/Analysis/Complex/CauchyIntegral.lean:93:divergence theorem, see `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`

```

This is a scoped negative search, not a proof that a general divergence theorem
cannot be built from other Mathlib infrastructure. The brief's WithinAt name
appears only as a private auxiliary theorem with the suffix `_aux₁`; the public
box theorem is `integral_divergence_of_hasFDerivAt_off_countable`.

### Smooth-domain residual (not a declaration or assumed input)

With the namespace and imports of `NoSlipUniqueness.lean`, the following exact
proposition remains unproved:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω → IsRegularLevelDomain Ω →
  ∀ (f g : Space → ℝ),
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 f x) →
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 g x) →
    (∀ x ∈ frontier Ω, f x = 0) →
    ∀ j : Fin 3,
      (∫ x in Ω, f x * fderiv ℝ g x (coordinateVector j)) =
        -(∫ x in Ω, fderiv ℝ f x (coordinateVector j) * g x)
```

No connectedness assumption is needed. No such theorem was inserted with a
missing proof or as a hypothesis of uniqueness. No compiler error is claimed
for this mathematical residual: it has not been implemented.

### Box scope and difference-energy residual

`box_integral_mul_fderiv_eq_neg` is fully proved on the closed coordinate box
`Icc a b : Set (Fin 3 → ℝ)`, with local C¹ regularity and genuine frontier
vanishing. It does not yet provide a theorem for the Spec's open box in
`Space = EuclideanSpace ℝ (Fin 3)`. Remaining transport uses the volume-preserving
PiLp coordinate equivalence and `Measure.univ_pi_Ioo_ae_eq_Icc`.
**Full box velocity uniqueness is not proved.**

For either shape, with solutions u₁,u₂ and `0 < S < min T₁ T₂`, put

```lean
w := fun z : SpaceTime => u₁.velocity z - u₂.velocity z
E := fun t : ℝ => ∫ x in Ω, ‖w (t, x)‖ ^ 2
```

The central remaining proposition is

```lean
∀ t ∈ Ioo (0 : ℝ) S,
  HasDerivAt E
    (-2 * ν * (∫ x in Ω, ∑ i : Fin 3,
      ‖spatialDerivative w t x (coordinateVector i)‖ ^ 2)
     - 2 * (∫ x in Ω,
       inner ℝ (spatialDerivative u₂.velocity t x (w (t, x))) (w (t, x)))) t
```

This requires differentiation under the domain integral, pressure cancellation,
transport cancellation, and viscous integration by parts. The bound on
`spatialDerivative u₂` is now proved from the original solution fields;
the integral convection estimate, energy differential inequality and Grönwall
application are still unproved. The final zero-energy-to-pointwise implication
is proved. No pressure equality or domain connectedness is asserted.

The precise final target remains the U7 proposition in T23_SPLIT.md; there is
intentionally no `noSlip_uniqueness` declaration and no substitute conditional
uniqueness theorem.

## Verification

All seven theorem axiom lists are exactly `[propext, Classical.choice, Quot.sound]`.
The seven vocabulary definitions and the solution record are literal Spec copies;
no artificial dependencies were inserted into definitions to force axiom lists.
The entire copied vocabulary/record block was checked byte-for-byte against Spec.
No new analytic premises or fields were added to the solution record.

The module and probe compile without output. Build, `make check`, `lake test`,
and mutation tests pass. Existing dependency warnings are replayed by Lake.
`make check` still reports the repository-wide historical BoundaryCorollary
admission and source-manifest mismatch without failing; the new module does not
import that module. Source import traversal found no path to BoundaryCorollary.
