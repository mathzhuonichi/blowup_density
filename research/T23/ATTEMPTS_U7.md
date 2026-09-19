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

## Continuation: difference energy and Grönwall (closed)

Diagnostics from the failed attempts, in order:

### difference_errors01.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:69:6: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?r * ∫ (a : ?m.300), ?f a ∂?m.302
in the target expression
  differenceEnergy Ω u.velocity v.velocity = fun s => ∫ (x : Space) in Ω, ‖(u.velocity - v.velocity) (s, x)‖ ^ 2

case e'_8
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hΩ : Bornology.IsBounded Ω
hm : MeasurableSet Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
hu : SmoothOnClosedSlab (Ioo 0 (min T₁ T₂)) Ω u.velocity
hv : SmoothOnClosedSlab (Ioo 0 (min T₁ T₂)) Ω v.velocity
h :
  HasDerivAt (fun s => ∫ (x : Space) in Ω, ‖(u.velocity - v.velocity) (s, x)‖ ^ 2)
    (∫ (x : Space) in Ω, deriv (fun s => ‖(u.velocity - v.velocity) (s, x)‖ ^ 2) t) t
⊢ differenceEnergy Ω u.velocity v.velocity = fun s => ∫ (x : Space) in Ω, ‖(u.velocity - v.velocity) (s, x)‖ ^ 2
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:100:20: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  fderiv ℝ
    (fun y =>
      (fderiv ℝ (fun y => u (t, y)) y) (coordinateVector i) - (fderiv ℝ (fun y => v (t, y)) y) (coordinateVector i))
    x
in the target expression
  (fderiv ℝ (fun y => (spatialDerivative u t y) (coordinateVector i) - (spatialDerivative v t y) (coordinateVector i))
        x)
      (coordinateVector i) =
    (fderiv ℝ (fun y => (spatialDerivative u t y) (coordinateVector i)) x) (coordinateVector i) -
      (fderiv ℝ (fun y => (spatialDerivative v t y) (coordinateVector i)) x) (coordinateVector i)

Ω : Set Space
hΩ : IsOpen Ω
u v : SpaceTimeField
t : ℝ
hu : ∀ x ∈ Ω, ContDiffAt ℝ ∞ (fun y => u (t, y)) x
hv : ∀ x ∈ Ω, ContDiffAt ℝ ∞ (fun y => v (t, y)) x
x : Space
hx : x ∈ Ω
i : Fin 3
a✝ : i ∈ Finset.univ
he :
  (fun y => (spatialDerivative (u - v) t y) (coordinateVector i)) =ᶠ[𝓝 x] fun y =>
    (spatialDerivative u t y) (coordinateVector i) - (spatialDerivative v t y) (coordinateVector i)
⊢ (fderiv ℝ (fun y => (spatialDerivative u t y) (coordinateVector i) - (spatialDerivative v t y) (coordinateVector i))
        x)
      (coordinateVector i) =
    (fderiv ℝ (fun y => (spatialDerivative u t y) (coordinateVector i)) x) (coordinateVector i) -
      (fderiv ℝ (fun y => (spatialDerivative v t y) (coordinateVector i)) x) (coordinateVector i)

```

### difference_errors02.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:74:6: error: Application type mismatch: The argument
  ContDiffAt.differentiableAt
    (ContDiffAt.comp t (SmoothOnClosedSlab.contDiffAt (SmoothOnClosedSlab.sub hu hv) ⟨?m.342, subset_closure ?m.347⟩)
      (ContDiffAt.prodMk contDiffAt_id contDiffAt_const))
has type
  ∞ ≠ 0 → DifferentiableAt ℝ ((u.velocity - v.velocity) ∘ fun x => (id x, ?m.394)) t
but is expected to have type
  DifferentiableAt ℝ (fun s => ?m.323 (s, ?m.325)) ?m.324
in the application
  NavierStokes.PeriodicUniqueness.energy_density_derivative
    (ContDiffAt.differentiableAt
      (ContDiffAt.comp t (SmoothOnClosedSlab.contDiffAt (SmoothOnClosedSlab.sub hu hv) ⟨?m.342, subset_closure ?m.347⟩)
        (ContDiffAt.prodMk contDiffAt_id contDiffAt_const)))

```

### difference_errors03.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:74:6: error: Application type mismatch: The argument
  ContDiffAt.differentiableAt
    (ContDiffAt.comp t (SmoothOnClosedSlab.contDiffAt (SmoothOnClosedSlab.sub hu hv) ⟨?m.342, subset_closure ?m.347⟩)
      (ContDiffAt.prodMk contDiffAt_id contDiffAt_const))
has type
  ∞ ≠ 0 → DifferentiableAt ℝ ((u.velocity - v.velocity) ∘ fun x => (id x, ?m.394)) t
but is expected to have type
  DifferentiableAt ℝ (fun s => ?m.323 (s, ?m.325)) ?m.324
in the application
  NavierStokes.PeriodicUniqueness.energy_density_derivative
    (ContDiffAt.differentiableAt
      (ContDiffAt.comp t (SmoothOnClosedSlab.contDiffAt (SmoothOnClosedSlab.sub hu hv) ⟨?m.342, subset_closure ?m.347⟩)
        (ContDiffAt.prodMk contDiffAt_id contDiffAt_const)))
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:120:25: error: don't know how to synthesize implicit argument `x`
  @SmoothOnClosedSlab.contDiffAt_slice Space (PiLp.normedAddCommGroup 2 fun x => ℝ) (PiLp.normedSpace 2 ℝ fun x => ℝ)
    (Ico 0 T₁) Ω u.velocity u.velocity_smooth t ht₁ (?m.196 y) (subset_closure hy)
context:
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hΩ : IsOpen Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
x : Space
hx : x ∈ Ω
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
y : ?m.176
hy : ?m.196 y ∈ Ω
⊢ Space
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:120:65: error: don't know how to synthesize implicit argument `a`
  @subset_closure Space (PiLp.topologicalSpace 2 fun x => ℝ) Ω (?m.196 y) hy
context:
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hΩ : IsOpen Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
x : Space
hx : x ∈ Ω
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
y : ?m.176
hy : ?m.196 y ∈ Ω
⊢ Space
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:120:19: error(lean.inferBinderTypeFailed): Failed to infer type of binder `hy`
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:120:17: error(lean.inferBinderTypeFailed): Failed to infer type of binder `y`
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:120:7: error: failed to infer `have` declaration type
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:117:56: error: unsolved goals
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hΩ : IsOpen Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
x : Space
hx : x ∈ Ω
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
⊢ temporalDerivative (u.velocity - v.velocity) t x =
    ν • spatialLaplacian (u.velocity - v.velocity) t x -
          (spatialDerivative (u.velocity - v.velocity) t x) (u.velocity (t, x)) -
        (spatialDerivative v.velocity t x) ((u.velocity - v.velocity) (t, x)) -
      pressureGradient (u.pressure - v.pressure) t x
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:165:36: warning: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).

```

### difference_errors04.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:150:24: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:153:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

```

### difference_errors05.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:150:24: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:153:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:244:50: error: unsolved goals
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hI : IBP Ω
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
w : SpaceTimeField := u.velocity - v.velocity
p : SpaceTimeScalar := u.pressure - v.pressure
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
hu : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => u.velocity (t, y)) x
hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => v.velocity (t, y)) x
hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x
hp : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => p (t, y)) x
hwz : ∀ x ∈ frontier Ω, w (t, x) = 0
hwd : ∀ x ∈ Ω, spatialDivergence w t x = 0
hL :
  ∫ (x : Space) in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ =
    -∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative w t x) (coordinateVector i)‖ ^ 2
hP : ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ = 0
hU : ∫ (x : Space) in Ω, ⟪w (t, x), (fderiv ℝ (fun y => w (t, y)) x) (u.velocity (t, x))⟫_ℝ = 0
hiL : IntegrableOn (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) Ω volume
hiP : IntegrableOn (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) Ω volume
hiU : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) Ω volume
hiV : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) Ω volume
x : Space
hx : x ∈ Ω
⊢ ν * ⟪w (t, x), spatialLaplacian (u.velocity - v.velocity) t x⟫_ℝ -
          ⟪w (t, x), (spatialDerivative (u.velocity - v.velocity) t x) (u.velocity (t, x))⟫_ℝ -
        ⟪w (t, x), (spatialDerivative v.velocity t x) ((u.velocity - v.velocity) (t, x))⟫_ℝ -
      ⟪w (t, x), pressureGradient (u.pressure - v.pressure) t x⟫_ℝ =
    ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ - ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ -
        ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ -
      ⟪w (t, x), pressureGradient p t x⟫_ℝ
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:251:12: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (a_1 : Space) in Ω,
    (((fun x => ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) - fun x =>
            ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) -
          fun x => ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ)
        a_1 -
      ⟪w (t, a_1), pressureGradient p t a_1⟫_ℝ
in the target expression
  ∫ (x : Space) in Ω,
      ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ - ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ -
          ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ -
        ⟪w (t, x), pressureGradient p t x⟫_ℝ =
    (((ν * ∫ (x : Space) in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) -
          ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) -
        ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) -
      ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ

ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hI : IBP Ω
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
w : SpaceTimeField := u.velocity - v.velocity
p : SpaceTimeScalar := u.pressure - v.pressure
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
hu : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => u.velocity (t, y)) x
hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => v.velocity (t, y)) x
hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x
hp : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => p (t, y)) x
hwz : ∀ x ∈ frontier Ω, w (t, x) = 0
hwd : ∀ x ∈ Ω, spatialDivergence w t x = 0
hL :
  ∫ (x : Space) in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ =
    -∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative w t x) (coordinateVector i)‖ ^ 2
hP : ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ = 0
hU : ∫ (x : Space) in Ω, ⟪w (t, x), (fderiv ℝ (fun y => w (t, y)) x) (u.velocity (t, x))⟫_ℝ = 0
hiL : IntegrableOn (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) Ω volume
hiP : IntegrableOn (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) Ω volume
hiU : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) Ω volume
hiV : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) Ω volume
⊢ ∫ (x : Space) in Ω,
      ν * ⟪w (t, x), spatialLaplacian w t x⟫_ℝ - ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ -
          ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ -
        ⟪w (t, x), pressureGradient p t x⟫_ℝ =
    (((ν * ∫ (x : Space) in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) -
          ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) -
        ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) -
      ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:254:10: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∫ (x : Space) in Ω, ⟪w (t, x), (fderiv ℝ (fun y => w (t, y)) x) (u.velocity (t, x))⟫_ℝ
in the target expression
  ∫ (x : Space) in Ω, ⟪w (t, x), temporalDerivative w t x⟫_ℝ =
    (((ν * -∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative w t x) (coordinateVector i)‖ ^ 2) -
          ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) -
        ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) -
      ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ

ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hI : IBP Ω
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ioo 0 (min T₁ T₂)
w : SpaceTimeField := u.velocity - v.velocity
p : SpaceTimeScalar := u.pressure - v.pressure
ht₁ : t ∈ Ico 0 T₁
ht₂ : t ∈ Ico 0 T₂
hu : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => u.velocity (t, y)) x
hv : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => v.velocity (t, y)) x
hw : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => w (t, y)) x
hp : ∀ x ∈ closure Ω, ContDiffAt ℝ ∞ (fun y => p (t, y)) x
hwz : ∀ x ∈ frontier Ω, w (t, x) = 0
hwd : ∀ x ∈ Ω, spatialDivergence w t x = 0
hL :
  ∫ (x : Space) in Ω, ⟪w (t, x), spatialLaplacian w t x⟫_ℝ =
    -∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative w t x) (coordinateVector i)‖ ^ 2
hP : ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ = 0
hU : ∫ (x : Space) in Ω, ⟪w (t, x), (fderiv ℝ (fun y => w (t, y)) x) (u.velocity (t, x))⟫_ℝ = 0
hiL : IntegrableOn (fun x => ⟪w (t, x), spatialLaplacian w t x⟫_ℝ) Ω volume
hiP : IntegrableOn (fun x => ⟪w (t, x), pressureGradient p t x⟫_ℝ) Ω volume
hiU : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) Ω volume
hiV : IntegrableOn (fun x => ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) Ω volume
he :
  ∫ (x : Space) in Ω, ⟪w (t, x), temporalDerivative w t x⟫_ℝ =
    (((ν * -∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative w t x) (coordinateVector i)‖ ^ 2) -
          ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative w t x) (u.velocity (t, x))⟫_ℝ) -
        ∫ (x : Space) in Ω, ⟪w (t, x), (spatialDerivative v.velocity t x) (w (t, x))⟫_ℝ) -
      ∫ (x : Space) in Ω, ⟪w (t, x), pressureGradient p t x⟫_ℝ
⊢ HasDerivAt (differenceEnergy Ω u.velocity v.velocity)
    ((-2 * ν * ∫ (x : Space) in Ω, ∑ i, ‖(spatialDerivative (u.velocity - v.velocity) t x) (coordinateVector i)‖ ^ 2) -
      2 *
        ∫ (x : Space) in Ω,
          ⟪(spatialDerivative v.velocity t x) ((u.velocity - v.velocity) (t, x)), (u.velocity - v.velocity) (t, x)⟫_ℝ)
    t

```

### difference_errors07.log
```text
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:338:95: error: Application type mismatch: The argument
  hz
has type
  differenceEnergy Ω u.velocity v.velocity t = 0
but is expected to have type
  ContinuousOn ?m.664 Ω
in the application
  eqOn_of_integral_norm_sub_sq_eq_zero ho hz
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:339:10: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

case hz
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hν : 0 < ν
hI : IBP Ω
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ico 0 (min T₁ T₂)
x : Space
hx : x ∈ Ω
S : ℝ
htS : t < S
hS : S < min T₁ T₂
hS₀ : 0 ≤ S
C : ℝ
_hC₀ : 0 ≤ C
hC : ∀ t ∈ Icc 0 S, ∀ x ∈ closure Ω, ‖spatialDerivative v.velocity t x‖ ≤ C
E : ℝ → ℝ := ⋯
D : ℝ → ℝ := ⋯
B : ℝ → ℝ := ⋯
E' : ℝ → ℝ := ⋯
hderiv : ∀ s ∈ Ioo 0 S, HasDerivAt E (E' s) s
hbound : ∀ s ∈ Ioo 0 S, E' s ≤ 2 * C * E s
hinit : E 0 = 0
hz : differenceEnergy Ω u.velocity v.velocity t = 0
⊢ ∫ (x : Space) in Ω, ‖u.velocity (t, x) - v.velocity (t, x)‖ ^ 2 = 0
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:342:10: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

case a
ν T₁ T₂ : ℝ
Ω : Set Space
a : SpatialField
g : SpaceTimeField
hν : 0 < ν
hI : IBP Ω
ho : IsOpen Ω
hb : Bornology.IsBounded Ω
u : ClassicalSolutionOmega ν Ω a g T₁
v : ClassicalSolutionOmega ν Ω a g T₂
t : ℝ
ht : t ∈ Ico 0 (min T₁ T₂)
x : Space
hx : x ∈ Ω
S : ℝ
htS : t < S
hS : S < min T₁ T₂
hS₀ : 0 ≤ S
C : ℝ
_hC₀ : 0 ≤ C
hC : ∀ t ∈ Icc 0 S, ∀ x ∈ closure Ω, ‖spatialDerivative v.velocity t x‖ ≤ C
E : ℝ → ℝ := ⋯
D : ℝ → ℝ := ⋯
B : ℝ → ℝ := ⋯
E' : ℝ → ℝ := ⋯
hderiv : ∀ s ∈ Ioo 0 S, HasDerivAt E (E' s) s
hbound : ∀ s ∈ Ioo 0 S, E' s ≤ 2 * C * E s
hinit : E 0 = 0
hz : differenceEnergy Ω u.velocity v.velocity t = 0
⊢ x ∈ Ω
../formalization/NSFormalization/Section3/T23/DifferenceEnergy.lean:367:10: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  AlexandrovDiscrete Space

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

```

Fixes: discharge the definitionally equal function goal from `convert` with
`rfl`; explicitly unfold the spatial derivative for rewrite matching; give the
time differentiability fact and slice-smoothness families explicit types;
replace deprecated `ContinuousLinearMap.sub_apply`; use typed integrability
facts for nested differences before applying `integral_sub`; spell the transport
integral with `spatialDerivative`; supply continuity arguments before the energy
zero argument; use `isOpen_iInter_of_finite` for the three coordinate intervals.
The eighth complete attempt compiles with zero output. No heartbeat override
or admission was needed.

### Current exact residual (supersedes the previous residual list)

All box obligations, time differentiation, the difference momentum equation,
pressure/transport/viscous cancellations, convection estimate, and Grönwall are
proved. `noSlip_uniqueness_box` has no added analytic premise.
`noSlip_uniqueness_of_ibp` has exactly the explicit `IBP Ω` premise authorized
in the continuation request. The sole unproved analytic theorem is:

```lean
∀ (Ω : Set Space), IsOpen Ω → Bornology.IsBounded Ω →
  IsRegularLevelDomain Ω → IBP Ω
```

`IBP` is the scalar C¹ boundary integration-by-parts identity in
`DomainSolution.lean`; it is not an energy identity or uniqueness premise.
A future proof of this residual and a case split give unrestricted U7.
No unrestricted `noSlip_uniqueness` declaration is claimed. See SPEC_ISSUES G1.
The canonical Spec block has moved unchanged to `DomainSolution.lean` to avoid
an import cycle; importing `NoSlipUniqueness` still exposes all public results.

## Continuation verification

Final dependency build: exit 0 (8820 jobs). Direct Lean checks on all five
entry/analytic modules and all three probes: exit 0, zero output. The 40 printed
theorem axiom lists were mechanically checked to contain exactly the standard
three. `make check`, `lake test`, and `make test-mutations` pass. The canonical
Spec vocabulary/record passed byte comparison after its move to DomainSolution.
The final source dependency traversal has no forbidden BoundaryCorollary path.
See REPORT_478b for the four-part handoff and SPEC_ISSUES G1 for the sole residual.
