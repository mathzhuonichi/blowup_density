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

## Continuation: physical-box transport

The first API probe used an absent name:
```text
Unknown identifier `frontier_closure`
```
Use `frontier_closure_subset`; equality is unnecessary. First proof diagnostics:
```text
../research/T23/probes/box_transport_work.lean:30:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⇑e.toHomeomorph ⁻¹' closure ?s
in the target expression
  ⇑e ⁻¹' closure Ω = Icc a b

a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
⊢ ⇑e ⁻¹' closure Ω = Icc a b
../research/T23/probes/box_transport_work.lean:32:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⇑e.toHomeomorph ⁻¹' frontier ?s
in the target expression
  ⇑e ⁻¹' frontier Ω = frontier U

a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
hecl : ⇑e ⁻¹' closure Ω = Icc a b
⊢ ⇑e ⁻¹' frontier Ω = frontier U
../research/T23/probes/box_transport_work.lean:42:32: error(lean.unknownIdentifier): Unknown identifier `univ_pi_Ioo_ae_eq_Icc`
../research/T23/probes/box_transport_work.lean:62:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (fderiv ℝ (g ∘ ⇑e) y) (Pi.single j 1)
in the target expression
  (fun x => f (e x) * (fderiv ℝ g (e x)) (coordinateVector j)) y =
    (fun x => (f ∘ ⇑e) x * (fderiv ℝ (g ∘ ⇑e) x) (Pi.single j 1)) y

case e'_2
a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
hecl : ⇑e ⁻¹' closure Ω = Icc a b
hefr : ⇑e ⁻¹' frontier Ω = frontier U
hfr : frontier (Icc a b) ⊆ frontier U
hint : ∀ (F : Space → ℝ), ∫ (x : Space) in Ω, F x = ∫ (y : Fin 3 → ℝ) in Icc a b, F (e y)
f g : Space → ℝ
hf : ∀ x ∈ closure {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, ContDiffAt ℝ 1 f x
hg : ∀ x ∈ closure {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, ContDiffAt ℝ 1 g x
hz : ∀ x ∈ frontier {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, f x = 0
j : Fin 3
hc : ∀ (q : Space → ℝ), (∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x) → ∀ y ∈ Icc a b, ContDiffAt ℝ 1 (q ∘ ⇑e) y
hd :
  ∀ (q : Space → ℝ),
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x) →
      ∀ y ∈ Icc a b, (fderiv ℝ (q ∘ ⇑e) y) (Pi.single j 1) = (fderiv ℝ q (e y)) (coordinateVector j)
h :
  ∫ (x : Fin 3 → ℝ) in Icc a b, (f ∘ ⇑e) x * (fderiv ℝ (g ∘ ⇑e) x) (Pi.single j 1) =
    -∫ (x : Fin 3 → ℝ) in Icc a b, (fderiv ℝ (f ∘ ⇑e) x) (Pi.single j 1) * (g ∘ ⇑e) x
y : Fin 3 → ℝ
hy : y ∈ Icc a b
⊢ (fun x => f (e x) * (fderiv ℝ g (e x)) (coordinateVector j)) y =
    (fun x => (f ∘ ⇑e) x * (fderiv ℝ (g ∘ ⇑e) x) (Pi.single j 1)) y
../research/T23/probes/box_transport_work.lean:67:8: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (fderiv ℝ (f ∘ ⇑e) y) (Pi.single j 1)
in the target expression
  (fun x => (fderiv ℝ f (e x)) (coordinateVector j) * g (e x)) y =
    (fun x => (fderiv ℝ (f ∘ ⇑e) x) (Pi.single j 1) * (g ∘ ⇑e) x) y

case e'_3
a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
hecl : ⇑e ⁻¹' closure Ω = Icc a b
hefr : ⇑e ⁻¹' frontier Ω = frontier U
hfr : frontier (Icc a b) ⊆ frontier U
hint : ∀ (F : Space → ℝ), ∫ (x : Space) in Ω, F x = ∫ (y : Fin 3 → ℝ) in Icc a b, F (e y)
f g : Space → ℝ
hf : ∀ x ∈ closure {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, ContDiffAt ℝ 1 f x
hg : ∀ x ∈ closure {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, ContDiffAt ℝ 1 g x
hz : ∀ x ∈ frontier {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}, f x = 0
j : Fin 3
hc : ∀ (q : Space → ℝ), (∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x) → ∀ y ∈ Icc a b, ContDiffAt ℝ 1 (q ∘ ⇑e) y
hd :
  ∀ (q : Space → ℝ),
    (∀ x ∈ closure Ω, ContDiffAt ℝ 1 q x) →
      ∀ y ∈ Icc a b, (fderiv ℝ (q ∘ ⇑e) y) (Pi.single j 1) = (fderiv ℝ q (e y)) (coordinateVector j)
h :
  ∫ (x : Fin 3 → ℝ) in Icc a b, (f ∘ ⇑e) x * (fderiv ℝ (g ∘ ⇑e) x) (Pi.single j 1) =
    -∫ (x : Fin 3 → ℝ) in Icc a b, (fderiv ℝ (f ∘ ⇑e) x) (Pi.single j 1) * (g ∘ ⇑e) x
y : Fin 3 → ℝ
hy : y ∈ Icc a b
⊢ (fun x => (fderiv ℝ f (e x)) (coordinateVector j) * g (e x)) y =
    (fun x => (fderiv ℝ (f ∘ ⇑e) x) (Pi.single j 1) * (g ∘ ⇑e) x) y

```
Fixes: use the homeomorphism equalities via `Eq.trans` (coercion spelling),
qualify `Measure.univ_pi_Ioo_ae_eq_Icc`, and use `congrArg` for beta-redex
integrands. The second attempt still needed explicit `congrArg closure heU` and
`congrArg frontier heU` to bridge the homeomorphism coercion.
```text
../research/T23/probes/box_transport_work.lean:30:60: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⇑e ⁻¹' Ω
in the target expression
  closure (⇑e.toHomeomorph ⁻¹' Ω) = Icc a b

a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
⊢ closure (⇑e.toHomeomorph ⁻¹' Ω) = Icc a b
../research/T23/probes/box_transport_work.lean:32:61: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ⇑e ⁻¹' Ω
in the target expression
  frontier (⇑e.toHomeomorph ⁻¹' Ω) = frontier U

a b : Fin 3 → ℝ
hab : ∀ (i : Fin 3), a i < b i
e : (Fin 3 → ℝ) ≃L[ℝ] PiLp 2 fun x => ℝ := (PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ).symm
U : Set (Fin 3 → ℝ) := univ.pi fun i => Ioo (a i) (b i)
Ω : Set Space := {x | ∀ (i : Fin 3), a i < x.ofLp i ∧ x.ofLp i < b i}
heU : ⇑e ⁻¹' Ω = U
hcl : closure U = Icc a b
hecl : ⇑e ⁻¹' closure Ω = Icc a b
⊢ frontier (⇑e.toHomeomorph ⁻¹' Ω) = frontier U

```

## Continuation: energy cancellations and parameter integrals

Failed proof diagnostics (all corrected):

### energy_errors01.log
```text
../formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:47:11: warning: Possibly looping simp theorem: `NavierStokes.PeriodicUniqueness.fderiv_apply_eq_sum`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
../formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:47:11: error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information

```

### energy_errors03.log
```text
../formalization/NSFormalization/Section3/T23/NoSlipEnergy.lean:150:4: error: Type mismatch: After simplification, term
  integral_inner_partial hI hΩ hm hw (fun x hx => contDiffAt_partial (hw x hx) i) hz i
 has type
  @Eq ℝ
    (∫ (x : Space) in Ω,
      ⟪w (t, x), (fderiv ℝ (fun y => (fderiv ℝ (fun y => w (t, y)) y) (coordinateVector i)) x) (coordinateVector i)⟫_ℝ)
    (-∫ (x : Space) in Ω, ‖(fderiv ℝ (fun y => w (t, y)) x) (coordinateVector i)‖ ^ 2)
but is expected to have type
  @Eq ℝ
    (∫ (a : Space) in Ω,
      ⟪w (t, a), (fderiv ℝ (fun y => (spatialDerivative w t y) (coordinateVector i)) a) (coordinateVector i)⟫_ℝ)
    (-∫ (a : Space) in Ω, ‖(spatialDerivative w t a) (coordinateVector i)‖ ^ 2)

```

### time_errors01.log
```text
../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:16:2: warning: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:40:2: warning: Try this: 
  haveI̵

The goal is a proposition, so `have` is preferred over `haveI`.
The difference between `have` and `haveI` is that `haveI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:85:41: error: unsolved goals
Ω : Set Space
hΩ : Bornology.IsBounded Ω
hm : MeasurableSet Ω
I : Set ℝ
hI : IsOpen I
F : SpaceTime → ℝ
hF : SmoothOnClosedSlab I Ω F
t : ℝ
ht : t ∈ I
G : SpaceTime → ℝ := fun z => (fderiv ℝ F z) (1, 0)
hd : ∀ s ∈ I, ∀ x ∈ closure Ω, HasDerivAt (fun r => F (r, x)) (G (s, x)) s
z : SpaceTime
hz : z ∈ I ×ˢ closure Ω
⊢ ¬?m.274 z hz = ω
../formalization/NSFormalization/Section3/T23/DomainTimeIntegral.lean:76:51: error: unsolved goals
Ω : Set Space
hΩ : Bornology.IsBounded Ω
hm : MeasurableSet Ω
I : Set ℝ
hI : IsOpen I
F : SpaceTime → ℝ
hF : SmoothOnClosedSlab I Ω F
t : ℝ
ht : t ∈ I
G : SpaceTime → ℝ := fun z => (fderiv ℝ F z) (1, 0)
hd : ∀ s ∈ I, ∀ x ∈ closure Ω, HasDerivAt (fun r => F (r, x)) (G (s, x)) s
⊢ HasDerivAt (fun s => ∫ (x : Space) in Ω, F (s, x)) (∫ (x : Space) in Ω, deriv (fun s => F (s, x)) t) t

```

Fixes: rewrite the directional-derivative sum once (recursive simp loops);
unfold `spatialDerivative` explicitly in the vector IBP application; specify
`m := ∞` for continuity of the derivative; use `have` for local measure instances.
Both new modules build successfully.
