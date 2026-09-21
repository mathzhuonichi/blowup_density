import NSFormalization.Paper1.PeriodicLifespan

/-!
# Restriction of periodic classical flows

An actual `PeriodicLifespan.Flow` on a horizon `S` restricts to every shorter
positive horizon.  Combining this elementary restriction with the inserted
flow at `T` and the already proved lifespan upper bound gives the precise
positive-horizon existence predicate `Nonempty (Flow ... S) ↔ S ≤ T` for an
inserted field.  No local-existence theorem for arbitrary data is used.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLifespan

open Set
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-- Restrict an actual periodic flow to a shorter positive horizon. -/
def Flow.restrict {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {R : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    Flow ν a f R := by
  refine
    { velocity := W.velocity
      pressure := W.pressure
      horizon_pos := hR
      velocity_smooth := ?_
      pressure_smooth := ?_
      velocity_periodic := ?_
      pressure_periodic := ?_
      initial := W.initial
      divergence := ?_
      equation := ?_ }
  · exact W.velocity_smooth.mono (fun _ hz =>
      ⟨⟨hz.1.1, hz.1.2.trans_le hRS⟩, hz.2⟩)
  · exact W.pressure_smooth.mono (fun _ hz =>
      ⟨⟨hz.1.1, hz.1.2.trans_le hRS⟩, hz.2⟩)
  · intro t ht x i
    exact W.velocity_periodic t ⟨ht.1, ht.2.trans_le hRS⟩ x i
  · intro t ht x i
    exact W.pressure_periodic t ⟨ht.1, ht.2.trans_le hRS⟩ x i
  · intro t ht x
    exact W.divergence t ⟨ht.1, ht.2.trans_le hRS⟩ x
  · intro t ht x
    exact W.equation t ⟨ht.1, lt_of_lt_of_le ht.2 hRS⟩ x

/-- The restriction operation packages a shorter-horizon witness. -/
theorem Flow.nonempty_restrict {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) {R : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    Nonempty (Flow ν a f R) :=
  ⟨W.restrict hR hRS⟩

/-- Exact positive-horizon existence for the actual inserted flow class.

The forward implication uses `insertion_lifespan_le` and the horizon lower
bound, while the reverse implication restricts the inserted flow at `T`.
The statement is about the explicitly defined actual `Flow` class; it does
not identify this class with a separately chosen manuscript maximal solution.
-/
theorem flow_nonempty_iff_le_of_insertion
    {ν r T τ : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ) (hτT : τ < T)
    {a : Space → Space} {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (ha : ∀ x, v (0, x) = a x) :
    ∀ S : ℝ, 0 < S →
      (Nonempty (Flow ν a (fun z => g z + F z) S) ↔ S ≤ T) := by
  have hupper : lifespan ν a (fun z => g z + F z) ≤ ENNReal.ofReal T :=
    insertion_lifespan_le hν hτ hτT h ha
  have hT0 : 0 ≤ T := (hτ.trans_lt hτT).le
  intro S hS
  constructor
  · intro hW
    have hhor : ENNReal.ofReal S ≤ lifespan ν a (fun z => g z + F z) :=
      horizon_le_lifespan hW.some
    exact (ENNReal.ofReal_le_ofReal_iff hT0).mp (hhor.trans hupper)
  · intro hST
    exact Flow.nonempty_restrict (insertionFlow hτ hτT h ha) hS hST

end NSFormalization.Paper1.PeriodicLifespan
