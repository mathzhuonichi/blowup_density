import NSFormalization.Section4.A02.SolutionClass

/-!
# A02 unit U4: restriction, slab congruence and the basepoint pressure gauge

`research/A02/COMPARISON.md` §3 unit **U4**: the three non-analytic facts about
one classical whole-space solution that `MaximalSolutionAPI` needs before any
uniqueness statement is available.

* `ClassicalSolutionR.restrict` — the `ClassicalSolutionR` analogue of
  `NSFormalization.Source.SmoothLifespan.Flow.restrict`
  (`Source/SmoothLifespan.lean:83`), i.e. the spec field
  `MaximalSolutionAPI.restrict` (`research/A02/Spec.lean:345-348`).
* `ClassicalSolutionR.congr` — the **congruence** lemma: the structure's fields
  depend only on the germ of `(velocity, pressure)` on the slab
  `Ico 0 T ×ˢ univ`, so a pair of fields agreeing there carries a solution with
  those fields *literally*.  This is what the literal equalities
  `w.velocity = u ∧ w.pressure = p` of `Spec.lean:210-214` `IsMaximalSolution`
  need, and it is the form unit **U7** consumes.
* `ClassicalSolutionR.normalizePressure` — the spec field
  `MaximalSolutionAPI.pressure_normalization` (`Spec.lean:399-403`):
  `p ↦ p − p(·,x₀)` is again a classical pressure for the same velocity.
  The two supporting facts the spec docstring names are proved separately:
  `pressureGradient_sub_basepoint` (the gradient is unchanged, so `momentum`
  and `pressure_gradient` survive) and `contDiffOn_basepoint` (`(t,x) ↦ p(t,x₀)`
  is `ContDiffOn` on the slab, so `pressure_smooth` survives), together with
  gauge invariance `normalizePressure_gauge_invariant`.

Nothing here is analytic: no Sobolev estimate, no embedding, no uniqueness.
Unit U4 is listed as **S** and depends on nothing.

## The restated D01 objects

`ClassicalSolutionR`, `maximalLifespanR`, `RegularThrough`,
`PressureGaugeEquivOn`, `initialClassR`, `MemForceR` and `IsSobolevDatum` are the
single A02-local restatement of `verification/Contracts/V1/Data.lean`; they live
in `NSFormalization.Section4.A02.SolutionClass`, imported above (lane 040 removed
the byte-identical copy that lane 032 kept inline here).  See that module's
header for why the copy exists and how it relates to the `Contracts` and D01
copies.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-! ## 1. Restriction to a shorter horizon (spec field `restrict`)

`Source/SmoothLifespan.lean:83` `Flow.restrict` transcribed to the manuscript's
class.  `Flow`'s `energy`, `velocity_bound` and `derivative_bound` are absent
here; `sobolev` and `pressure_gradient` are new, and both restrict by
monotonicity of `Ico 0 ·`. -/

/-- Restrict a classical solution to a shorter positive horizon, keeping the
*same* velocity and pressure functions. -/
def ClassicalSolutionR.restrict {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (u : ClassicalSolutionR ν a f T) {S : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    ClassicalSolutionR ν a f S where
  velocity := u.velocity
  pressure := u.pressure
  horizon_pos := hS
  velocity_smooth :=
    u.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩)
  pressure_smooth :=
    u.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩)
  initial := u.initial
  divergence := fun t ht x => u.divergence t ⟨ht.1, ht.2.trans_le hST⟩ x
  momentum := fun t ht x => u.momentum t ⟨ht.1, ht.2.trans_le hST⟩ x
  sobolev := fun m => by
    obtain ⟨G, hGc, hGd⟩ := u.sobolev m
    exact ⟨G, hGc.mono (Ico_subset_Ico le_rfl hST),
      fun t ht => hGd t ⟨ht.1, ht.2.trans_le hST⟩⟩
  pressure_gradient := fun t ht => u.pressure_gradient t ⟨ht.1, ht.2.trans_le hST⟩

/-- The `Nonempty`-witness form of `restrict`, the shape unit **U6**
(`Order.lean`) reads a realized horizon in through `maximalLifespanR`. -/
theorem ClassicalSolutionR.nonempty_restrict {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (u : ClassicalSolutionR ν a f T) {S : ℝ} (hS : 0 < S)
    (hST : S ≤ T) : Nonempty (ClassicalSolutionR ν a f S) :=
  ⟨u.restrict hS hST⟩

/-- **Spec field `MaximalSolutionAPI.restrict`** (`research/A02/Spec.lean:345-348`),
verbatim. -/
theorem exists_restrict (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) (S : ℝ) (hS : 0 < S) (hST : S ≤ T) :
    ∃ w : ClassicalSolutionR ν a f S,
      w.velocity = u.velocity ∧ w.pressure = u.pressure :=
  ⟨u.restrict hS hST, rfl, rfl⟩

/-! ## 2. Congruence: the fields depend only on the germ on the slab

`research/A02/COMPARISON.md` §1.3, the `IsMaximalSolution` row: the literal
equality clause `w.velocity = u ∧ w.pressure = p` of `Spec.lean:214` needs a
`ClassicalSolutionR` whose *literal* fields are the given pair, not merely a
solution agreeing with it on the slab.  Every field of the structure is a
statement about `Ico 0 T ×ˢ univ`, and the only two-sided derivative,
`temporalDerivative` inside `momentum`, is taken at interior times `t ∈ Ioo 0 T`
where the open `Ioo 0 T ⊆ Ico 0 T` is already a neighbourhood.  So agreement on
the slab transfers every field. -/

section Congr

variable {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}

/-- Agreement on the slab gives full agreement of every spatial slice at a time
of `[0,T)`. -/
theorem slice_eq_of_eqOn {u v : SpaceTime → Space}
    (h : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = v z)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (fun y : Space => u (t, y)) = fun y : Space => v (t, y) :=
  funext fun y => h (t, y) ⟨ht, mem_univ y⟩

/-- The same for a scalar field. -/
theorem scalarSlice_eq_of_eqOn {p q : SpaceTime → ℝ}
    (h : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), p z = q z)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (fun y : Space => p (t, y)) = fun y : Space => q (t, y) :=
  funext fun y => h (t, y) ⟨ht, mem_univ y⟩

/-- The spatial Fréchet derivative at a time of `[0,T)` only sees the slab. -/
theorem spatialDerivative_eq_of_eqOn {u v : SpaceTime → Space}
    (h : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = v z)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    spatialDerivative u t = spatialDerivative v t := by
  funext x
  simp only [spatialDerivative, slice_eq_of_eqOn h ht]

/-- The pressure gradient at a time of `[0,T)` only sees the slab. -/
theorem pressureGradient_eq_of_eqOn {p q : SpaceTime → ℝ}
    (h : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), p z = q z)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    pressureGradient p t = pressureGradient q t := by
  funext x
  simp only [pressureGradient, scalarSlice_eq_of_eqOn h ht]

/-- The two-sided time derivative at an *interior* time only sees the slab,
because `Ioo 0 T` is an open neighbourhood of `t` inside `Ico 0 T`. -/
theorem temporalDerivative_eq_of_eqOn {u v : SpaceTime → Space}
    (h : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = v z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative u t x = temporalDerivative v t x := by
  have hev : (fun s : ℝ => u (s, x)) =ᶠ[nhds t] fun s : ℝ => v (s, x) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
      (fun s hs => h (s, x) ⟨⟨hs.1.le, hs.2⟩, mem_univ x⟩)
  have hfd : fderiv ℝ (fun s : ℝ => u (s, x)) t = fderiv ℝ (fun s : ℝ => v (s, x)) t :=
    hev.fderiv_eq
  simp only [temporalDerivative, hfd]

/-- The full residual at an interior time only sees the slab. -/
theorem navierStokesResidual_eq_of_eqOn {u v : SpaceTime → Space} {p q : SpaceTime → ℝ}
    (hu : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = v z)
    (hp : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), p z = q z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν v q t x := by
  have htIco : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hsd : spatialDerivative u t = spatialDerivative v t :=
    spatialDerivative_eq_of_eqOn hu htIco
  have hval : u (t, x) = v (t, x) := hu (t, x) ⟨htIco, mem_univ x⟩
  have hadv : advection u t x = advection v t x := by
    simp only [advection, hsd, hval]
  have hlap : spatialLaplacian u t x = spatialLaplacian v t x := by
    simp only [spatialLaplacian, hsd]
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    temporalDerivative_eq_of_eqOn hu ht x, hadv, hlap,
    pressureGradient_eq_of_eqOn hp htIco]

/-- **The congruence lemma of unit U4.**  A pair of fields agreeing with a
classical solution on the slab `[0,T) × R³` *is* the pair of fields of a
classical solution of the same datum, literally. -/
def ClassicalSolutionR.congr (w : ClassicalSolutionR ν a f T)
    {u : SpaceTimeField} {p : SpaceTimeScalar}
    (hu : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = w.velocity z)
    (hp : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), p z = w.pressure z) :
    ClassicalSolutionR ν a f T where
  velocity := u
  pressure := p
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth.congr hu
  pressure_smooth := w.pressure_smooth.congr hp
  initial := fun x => by
    rw [hu (0, x) ⟨⟨le_rfl, w.horizon_pos⟩, mem_univ x⟩]; exact w.initial x
  divergence := fun t ht x => by
    simp only [spatialDivergence, spatialDerivative_eq_of_eqOn hu ht]
    exact w.divergence t ht x
  momentum := fun t ht x => by
    rw [navierStokesResidual_eq_of_eqOn hu hp ht x]; exact w.momentum t ht x
  sobolev := fun m => by
    obtain ⟨G, hGc, hGd⟩ := w.sobolev m
    refine ⟨G, hGc, fun t ht => ?_⟩
    rw [slice_eq_of_eqOn hu ht]
    exact hGd t ht
  pressure_gradient := fun t ht => by
    rw [pressureGradient_eq_of_eqOn hp ht]
    exact w.pressure_gradient t ht

/-- The shape unit **U7** consumes, and the shape `IsMaximalSolution`
(`research/A02/Spec.lean:210-214`) asks for: a solution *presented* with the
given fields. -/
theorem exists_eq_fields_of_eqOn (w : ClassicalSolutionR ν a f T)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), u z = w.velocity z)
    (hp : ∀ z ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space), p z = w.pressure z) :
    ∃ w' : ClassicalSolutionR ν a f T, w'.velocity = u ∧ w'.pressure = p :=
  ⟨w.congr hu hp, rfl, rfl⟩

/-- The pointwise-in-`(t,x)` spelling of the same statement, which is how the
manuscript's "agree on `[0,T)`" clauses are written. -/
theorem exists_eq_fields_of_agree (w : ClassicalSolutionR ν a f T)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = w.velocity (t, x))
    (hp : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, p (t, x) = w.pressure (t, x)) :
    ∃ w' : ClassicalSolutionR ν a f T, w'.velocity = u ∧ w'.pressure = p :=
  exists_eq_fields_of_eqOn w u p (fun z hz => hu z.1 hz.1 z.2) (fun z hz => hp z.1 hz.1 z.2)

end Congr

/-! ## 3. The basepoint pressure gauge (spec field `pressure_normalization`) -/

section Normalization

variable {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}

/-- Subtracting a function of time alone does not change the pressure gradient.
This is the first of the three facts `research/A02/Spec.lean:388-396` lists. -/
theorem pressureGradient_sub_basepoint (p : SpaceTimeScalar) (x₀ : Space) (t : ℝ) :
    pressureGradient (fun z : SpaceTime => p z - p (z.1, x₀)) t =
      pressureGradient p t := by
  funext x
  simp only [pressureGradient, fderiv_sub_const]

/-- `(t,x) ↦ p (t,x₀)` is smooth on the slab whenever `p` is, because
`(t,x) ↦ (t,x₀)` is smooth and maps the slab into itself.  This is the second
fact of `research/A02/Spec.lean:388-396`. -/
theorem contDiffOn_basepoint {p : SpaceTimeScalar} {S : Set SpaceTime} {x₀ : Space}
    (hp : ContDiffOn ℝ ∞ p S) (hmaps : ∀ z ∈ S, ((z.1, x₀) : SpaceTime) ∈ S) :
    ContDiffOn ℝ ∞ (fun z : SpaceTime => p (z.1, x₀)) S :=
  hp.comp ((contDiff_fst.prodMk contDiff_const).contDiffOn) hmaps

/-- **The canonical gauge.**  Subtracting the value at a fixed basepoint turns a
classical solution into a classical solution of the same datum with the same
velocity.  Spec field `MaximalSolutionAPI.pressure_normalization`. -/
def ClassicalSolutionR.normalizePressure (w : ClassicalSolutionR ν a f T) (x₀ : Space) :
    ClassicalSolutionR ν a f T where
  velocity := w.velocity
  pressure := fun z : SpaceTime => w.pressure z - w.pressure (z.1, x₀)
  horizon_pos := w.horizon_pos
  velocity_smooth := w.velocity_smooth
  pressure_smooth :=
    w.pressure_smooth.sub
      (contDiffOn_basepoint w.pressure_smooth (fun _ hz => ⟨hz.1, mem_univ x₀⟩))
  initial := w.initial
  divergence := w.divergence
  momentum := fun t ht x => by
    simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
      pressureGradient_sub_basepoint w.pressure x₀ t]
    exact w.momentum t ht x
  sobolev := w.sobolev
  pressure_gradient := fun t ht => by
    rw [pressureGradient_sub_basepoint w.pressure x₀ t]
    exact w.pressure_gradient t ht

/-- **Spec field `MaximalSolutionAPI.pressure_normalization`**
(`research/A02/Spec.lean:399-403`), verbatim. -/
theorem exists_pressure_normalization (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionR ν a f T) (x₀ : Space) :
    ∃ w' : ClassicalSolutionR ν a f T,
      w'.velocity = w.velocity ∧
      ∀ z : SpaceTime, w'.pressure z = w.pressure z - w.pressure (z.1, x₀) :=
  ⟨w.normalizePressure x₀, rfl, fun _ => rfl⟩

/-- **Gauge invariance**, the third fact of `research/A02/Spec.lean:388-396`:
two gauge-equivalent pressures have the *same* basepoint normalization on the
set where they are equivalent.  This is what makes the normalized pressure of
unit **U7** independent of which horizon it is read off. -/
theorem normalizePressure_gauge_invariant {I : Set ℝ} {p q : SpaceTimeScalar}
    (h : PressureGaugeEquivOn I p q) (x₀ : Space) :
    ∀ t ∈ I, ∀ x : Space,
      q (t, x) - q (t, x₀) = p (t, x) - p (t, x₀) := by
  obtain ⟨c, hc⟩ := h
  intro t ht x
  rw [hc t ht x, hc t ht x₀]
  ring

end Normalization

end NSFormalization.Section4.A02
