import NSFormalization.Section4.A02.Uniqueness
import NSFormalization.Section4.A02.Order

/-!
# A02 unit U7: the maximal solution — existence and uniqueness

`research/A02/COMPARISON.md` §3 unit **U7**; the two fields
`MaximalSolutionAPI.exists_maximal` and `MaximalSolutionAPI.maximal_unique`
(`research/A02/Spec.lean:421-434`), together with the predicate
`IsMaximalSolution` (`Spec.lean:210-214`) and the set `presingularTimes`
(`Spec.lean:168-169`) they are stated over.

`IsMaximalSolution` and `presingularTimes` are `⟪D01:IsMaximalSolution⟫` and (the
positive-time half of) the maximal-lifespan interval that `Contracts/V1/Data.lean`
does not define; A02 is their first consumer.  They are restated here **verbatim**
from `research/A02/Spec.lean:168-169,210-214`, the same way `SolutionClass.lean`
restates the `Contracts.V1.Data` objects and `Patch.lean` restates `limsupLeft`
and `speedENorm`.

## What is proved, and the A01 dependency

* `exists_maximal_of_localSolution` — spec field `exists_maximal`.  For every
  admissible datum there is one velocity `u` and one pressure `p` that are,
  *literally*, the fields of a classical solution on `[0,S)` for every `S` below
  `T^ν_{max,R}`.  This is the only field of U7 that needs A01: the positivity
  clause `0 < maximalLifespanR` holds precisely because A01 supplies a local
  solution.  The A01 existence clause `⟪A01:LocalTheoryAPI.solution⟫`
  (`research/A02/Spec.lean:317-321`) is taken as an **explicit hypothesis**
  `localSolution`, exactly as `Order.lean`'s `horizon_le_lifespan_of_localSolution`
  and the registered `MaximalPartial`'s `horizon_le_lifespan` do — A01 is not
  assumed globally.  Instantiating it at A01's `LocalTheoryAPI.solution` once A01
  is registered gives the spec field verbatim.

* `maximal_unique` — spec field `maximal_unique`.  Any two maximal solutions of a
  datum agree in velocity at every presingular time and have gauge-equivalent
  pressures there.  This field needs **no** A01 hypothesis: the two
  `IsMaximalSolution` hypotheses already hand over classical solutions on
  arbitrarily long subintervals, and `exists_horizon_gt_of_lt_lifespan` (U6)
  produces the horizon between a presingular `t` and `T_max`.  It is therefore
  stated as the spec field itself, with no `localSolution` argument.

## The construction (directed union over `S ↑ T_max`)

`u` and `p` are defined pointwise by classical choice: for a spacetime point `z`,
if there is any classical solution on a horizon strictly beyond `z.1`, pick one
(`chosenSol`) and read off its velocity — and, for `p`, its **basepoint-normalized**
pressure `q(z) − q(z.1,0)`.  Well-definedness across the choice is *not* needed as
a hypothesis of the construction: the two coherence lemmas `uField_eq`/`pField_eq`
show directly that on the slab of *any* solution `w` on a horizon `S`, the chosen
value coincides with `w.velocity` (by `velocity_unique_core`, U2) resp. with `w`'s
normalized pressure (by `pressure_gauge_core`, U3, and `normalizePressure_gauge_invariant`).

The **outside-the-slab issue** is settled by `Restrict.lean`'s congruence
constructor `exists_eq_fields_of_agree`: it needs the given fields to agree with a
solution only on the slab `Ico 0 S ×ˢ univ`, and returns a solution whose fields
are the given ones *literally* (as total functions on all of `ℝ × Space`).  So the
global `u`, `p` never have to match any particular `w` off the slab; every field
of `ClassicalSolutionR` constrains only the slab, and the constructor rebuilds
them from the on-slab agreement.  Hence `w.velocity = u` and `w.pressure = p`
hold as function equalities, which is what `IsMaximalSolution` demands.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-! ## 0. The two objects `Data.lean` does not define, restated from `Spec.lean` -/

/-- `research/A02/Spec.lean:168-169`, `02-preliminaries.tex:32`: the times
strictly before the maximal classical lifespan, `[0, T^ν_{max,R}(a,f))` inside
`ℝ`.  Restated verbatim; A02 is its first consumer. -/
def presingularTimes (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < maximalLifespanR ν a f}

/-- `research/A02/Spec.lean:210-214`, `⟪D01:IsMaximalSolution⟫`: `(u,p)` is *the*
maximal classical solution for `(ν,a,f)`.  Restated verbatim: the lifespan is
positive, and `u`, `p` are literally the fields of a classical solution on `[0,S)`
for every `S` below the maximal lifespan. -/
def IsMaximalSolution (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (u : SpaceTimeField) (p : SpaceTimeScalar) : Prop :=
  0 < maximalLifespanR ν a f ∧
    ∀ S : ℝ, 0 < S → ENNReal.ofReal S < maximalLifespanR ν a f →
      ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p

/-! ## 1. The pointwise directed union defining `u` and `p` -/

/-- There is a classical solution of `(ν,a,f)` on a horizon strictly beyond `t`. -/
def SolExists (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (t : ℝ) : Prop :=
  ∃ S : ℝ, t < S ∧ Nonempty (ClassicalSolutionR ν a f S)

/-- A chosen classical solution whose horizon exceeds `t`.  Its value at any point
of a slab shared with another solution is pinned by U2/U3, so the choice does not
matter — that is exactly what `uField_eq`/`pField_eq` establish. -/
def chosenSol {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {t : ℝ}
    (h : SolExists ν a f t) : ClassicalSolutionR ν a f h.choose :=
  h.choose_spec.2.some

/-- The global velocity of the maximal solution: at `z`, the velocity of any
solution living beyond `z.1`, or `0` where no solution reaches past `z.1`. -/
def uField (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (z : SpaceTime) : Space :=
  if h : SolExists ν a f z.1 then (chosenSol h).velocity z else 0

/-- The global pressure of the maximal solution: the **basepoint-normalized**
pressure `q(z) − q(z.1,0)` of a solution living beyond `z.1`.  Normalizing at the
fixed basepoint `0` is what collapses U3's per-pair gauge freedom to equality. -/
def pField (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (z : SpaceTime) : ℝ :=
  if h : SolExists ν a f z.1 then
    (chosenSol h).pressure z - (chosenSol h).pressure (z.1, (0 : Space))
  else 0

/-- **Velocity coherence (U2).**  On the slab of *any* solution `w` on horizon `S`,
the global `uField` equals `w.velocity`.  The chosen solution and `w` agree on
their common interval by `velocity_unique_core`. -/
theorem uField_eq {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    {S : ℝ} (w : ClassicalSolutionR ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S)
    (x : Space) : uField ν a f (t, x) = w.velocity (t, x) := by
  have hex : SolExists ν a f t := ⟨S, ht.2, ⟨w⟩⟩
  have h1 : uField ν a f (t, x) = (chosenSol hex).velocity (t, x) := dite_eq_left hex
  rw [h1]
  exact velocity_unique_core hν (chosenSol hex) w t
    ⟨ht.1, lt_min hex.choose_spec.1 ht.2⟩ x

/-- **Pressure coherence (U3).**  On the slab of *any* solution `w` on horizon `S`,
the global `pField` equals `w`'s basepoint-normalized pressure.  The chosen
solution and `w` are gauge-equivalent on their common interval
(`pressure_gauge_core`), and the basepoint normalization is gauge-invariant
(`normalizePressure_gauge_invariant`). -/
theorem pField_eq {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    {S : ℝ} (w : ClassicalSolutionR ν a f S) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S)
    (x : Space) :
    pField ν a f (t, x) = w.pressure (t, x) - w.pressure (t, (0 : Space)) := by
  have hex : SolExists ν a f t := ⟨S, ht.2, ⟨w⟩⟩
  have h1 : pField ν a f (t, x)
      = (chosenSol hex).pressure (t, x) - (chosenSol hex).pressure (t, (0 : Space)) :=
    dite_eq_left hex
  rw [h1]
  have hg := pressure_gauge_core hν (chosenSol hex) w
  have hgi := normalizePressure_gauge_invariant hg (0 : Space) t
    ⟨ht.1, lt_min hex.choose_spec.1 ht.2⟩ x
  linarith [hgi]

/-! ## 2. `exists_maximal` -/

/-- **Spec field `MaximalSolutionAPI.exists_maximal`**
(`research/A02/Spec.lean:421-423`), with the A01 existence clause
`⟪A01:LocalTheoryAPI.solution⟫` (`Spec.lean:317-321`) as an explicit hypothesis
`localSolution`, in the same shape as `Order.lean`'s
`horizon_le_lifespan_of_localSolution` and `MaximalPartial`'s
`horizon_le_lifespan`.  Instantiating `localSolution` at A01's
`LocalTheoryAPI.solution` gives the spec field verbatim. -/
theorem exists_maximal_of_localSolution
    (horizon : ℝ → SpatialField → SpaceTimeField → ℝ)
    (localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar), IsMaximalSolution ν a f u p := by
  intro ν a f hν ha hf
  -- A01 gives a local solution, hence a positive lifespan.
  have u₀ := localSolution ν a f hν ha hf
  have hpos : 0 < maximalLifespanR ν a f :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr u₀.horizon_pos) (horizon_le_lifespan u₀)
  refine ⟨uField ν a f, pField ν a f, hpos, ?_⟩
  intro S hS hSlt
  -- A solution on `[0,S)`: enter the supremum from below, then restrict.
  obtain ⟨S', hSS', hne'⟩ := exists_horizon_gt_of_lt_lifespan hS.le hSlt
  have wS : ClassicalSolutionR ν a f S := hne'.some.restrict hS hSS'.le
  -- Present the normalized `wS` with the global fields via the congruence lemma.
  refine exists_eq_fields_of_agree (wS.normalizePressure (0 : Space))
    (uField ν a f) (pField ν a f) ?_ ?_
  · intro t ht x
    show uField ν a f (t, x) = wS.velocity (t, x)
    exact uField_eq hν wS ht x
  · intro t ht x
    show pField ν a f (t, x) = wS.pressure (t, x) - wS.pressure (t, (0 : Space))
    exact pField_eq hν wS ht x

/-! ## 3. `maximal_unique` -/

/-- **Spec field `MaximalSolutionAPI.maximal_unique`**
(`research/A02/Spec.lean:429-434`), verbatim.  No A01 hypothesis is needed: the
`IsMaximalSolution` hypotheses supply the solutions on `[0,S)` directly, and
`exists_horizon_gt_of_lt_lifespan` (U6) produces a horizon between a presingular
`t` and `T^ν_{max,R}`. -/
theorem maximal_unique :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalSolution ν a f u₁ p₁ → IsMaximalSolution ν a f u₂ p₂ →
            (∀ t ∈ presingularTimes ν a f, ∀ x : Space, u₁ (t, x) = u₂ (t, x)) ∧
            PressureGaugeEquivOn (presingularTimes ν a f) p₁ p₂ := by
  intro ν a f hν _ha _hf u₁ u₂ p₁ p₂ hM₁ hM₂
  obtain ⟨_, hsol₁⟩ := hM₁
  obtain ⟨_, hsol₂⟩ := hM₂
  -- A common horizon `S` strictly between a presingular `t` and `T_max`.
  have common : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < maximalLifespanR ν a f →
      ∃ S : ℝ, 0 < S ∧ t < S ∧ ENNReal.ofReal S < maximalLifespanR ν a f := by
    intro t ht0 htlt
    obtain ⟨S', htS', hne'⟩ := exists_horizon_gt_of_lt_lifespan ht0 htlt
    refine ⟨(t + S') / 2, by linarith, by linarith, ?_⟩
    have hmid : (t + S') / 2 < S' := by linarith
    exact lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr hmid)
      (horizon_le_lifespan hne'.some)
  refine ⟨?_, ?_⟩
  · -- Velocity: `velocity_unique_core` on `[0,S)`.
    intro t ht x
    obtain ⟨ht0, htlt⟩ := ht
    obtain ⟨S, hS0, htS, hSlt⟩ := common t ht0 htlt
    obtain ⟨w₁, hw1v, _⟩ := hsol₁ S hS0 hSlt
    obtain ⟨w₂, hw2v, _⟩ := hsol₂ S hS0 hSlt
    have h := velocity_unique_core hν w₁ w₂ t ⟨ht0, lt_min htS htS⟩ x
    rw [hw1v, hw2v] at h
    exact h
  · -- Pressure: one global gauge `c t = p₂(t,0) − p₁(t,0)`, from U3 + normalization.
    refine ⟨fun s => p₂ (s, (0 : Space)) - p₁ (s, (0 : Space)), ?_⟩
    intro t ht x
    obtain ⟨ht0, htlt⟩ := ht
    obtain ⟨S, hS0, htS, hSlt⟩ := common t ht0 htlt
    obtain ⟨w₁, _, hw1p⟩ := hsol₁ S hS0 hSlt
    obtain ⟨w₂, _, hw2p⟩ := hsol₂ S hS0 hSlt
    have hg := pressure_gauge_core hν w₁ w₂
    have hgi := normalizePressure_gauge_invariant hg (0 : Space) t
      ⟨ht0, lt_min htS htS⟩ x
    rw [hw1p, hw2p] at hgi
    show p₂ (t, x) = p₁ (t, x) + (p₂ (t, (0 : Space)) - p₁ (t, (0 : Space)))
    linarith [hgi]

end NSFormalization.Section4.A02
