import NSFormalization.Section3.T11.RestartBeyond
import NSFormalization.Section3.T11.HighOrder
import NSFormalization.Section3.T11.Maximal

/-!
# T11 units U14 and U16 — `extendsBeyond` and `lifespanInfiniteOfLocallyFinite`

This module closes the last two fields of `PeriodicContinuationAPI`
(`research/T11/probes/api_on_canonical.lean:136-158`), verbatim.

Both are conditional on exactly two things and nothing else:

* the single named input `PeriodicQuantitativeLocalInput'`
  (`Section3/T11/LocalExistence.lean:24`), consumed only through lane 332's
  `restartBeyond`; and
* the `higherOrderBound` field of the same API, taken here as an explicit
  theorem binder `hHigh` (copied token for token from the probe) because U12
  is still being discharged by lanes 335/336 through
  `HighOrder.higherOrderBound_of_energyInequality`.  It is a hypothesis, not a
  new `def … : Prop`: the peeling rule allows one named input, and that name is
  already spent on `PeriodicQuantitativeLocalInput'`.

## Route

**U14 (`extendsBeyond`).**  `hHigh` at `m = 1` turns the `ℝ≥0∞` continuation
criterion `squaredHTwoIntegralT S u ≠ ⊤` into one *uniform* `H¹` trajectory
bound `K ≠ ⊤` valid on the whole of `[0, S)` — the field's own shape already
puts the existential `∃ M` before `∀ t ∈ Ico 0 S`, so the constant is the
endpoint constant and does not degrade as `b ↑ S`.  That is precisely the
hypothesis of lane 332's `restartBeyond`, whose `δ` is chosen before the datum,
so the resulting `ClassicalSolutionT ν a f (S + δ)` together with its velocity
and pressure agreement on `[0, S)` *is* `ExtendsBeyondT ν a f S u p`
(`Section3/T11/LocalTheory.lean:68`) — strictly stronger than the registered
`A04.extendsBeyond`, whose conclusion is only `ofReal S < maximalLifespanR`.

**U16 (`lifespanInfiniteOfLocallyFinite`).**  Contraposition.  If
`L := maximalLifespanT ν a f ≠ ⊤` then `L` is positive (a maximal solution
exists by hypothesis), so `S := L.toReal` is a positive real with
`ENNReal.ofReal S = L`.  The `≤` in the criterion hypothesis is load-bearing
here (`research/T11/RECONCILIATION.md` §2): it is applied at `S = L.toReal`,
where `ofReal S ≤ L` holds with equality and `ofReal S < L` would fail.  A
maximal solution restricts to every horizon strictly below `L`, giving
`SolvesBelowT ν a f S u p`; U14 then produces a genuine solution on `S + δ`,
whence `ENNReal.ofReal (S + δ) ≤ L = ENNReal.ofReal S` by
`lifespan_ge_of_extends`, i.e. `δ ≤ 0`, contradiction.

## Non-vacuity

A constant divergence-free velocity with zero force and zero pressure is a
classical torus solution on *every* positive horizon
(`constantVelocitySolutionT`).  It simultaneously inhabits all hypotheses of
both targets at a nonzero velocity, unconditionally on the named input.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

/-! ## 1. Realized horizons bound the lifespan from below -/

/-- A realized horizon is one of the terms of the supremum defining
`maximalLifespanT`.  This is the pointwise form of
`Uniqueness.horizon_le_lifespan`, whose `horizon`/`solution` pair is a global
family over all admissible data and therefore cannot be instantiated at the
single datum produced by a continuation argument. -/
theorem lifespan_ge_of_horizon {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ENNReal.ofReal T ≤ maximalLifespanT ν a f :=
  le_iSup_of_le T (le_iSup_of_le ⟨w⟩ le_rfl)

/-- **The lifespan passes every attained strict extension.**  This is the only
consequence of `ExtendsBeyondT` that U16 uses, and it is exported for T18–T21:
a concrete extension past `S` pushes the maximal lifespan strictly past
`ofReal S`. -/
theorem lifespan_ge_of_extends {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {u : SpaceTimeField} {p : SpaceTimeScalar}
    (h : ExtendsBeyondT ν a f S u p) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (S + δ) ≤ maximalLifespanT ν a f := by
  obtain ⟨δ, hδ, v, -, -⟩ := h
  exact ⟨δ, hδ, lifespan_ge_of_horizon v⟩

/-! ## 2. U14 — the `extendsBeyond` field -/

/-- **The `PeriodicContinuationAPI.extendsBeyond` field, verbatim.**

Conditional on the single named input `PeriodicQuantitativeLocalInput'` (used
only through `restartBeyond`) and on the `higherOrderBound` field of the same
structure, supplied here as the explicit binder `hHigh` (copied token for token
from `research/T11/probes/api_on_canonical.lean:112-121`) while U12 is closed
by lanes 335/336.

Only `m = 1` of `hHigh` is used.  Its `∃ M` stands *outside* `∀ t ∈ Ico 0 S`,
so `M` is one constant for the whole trajectory; that is exactly what
`restartBeyond` needs to choose its `δ` uniformly, before the datum. -/
theorem extendsBeyond_of_input (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p := by
  intro ν hν a ha f hf S hS u p hsolve hfin
  obtain ⟨K, hK, hKbound⟩ := hHigh ν hν a ha f hf S hS u p hsolve hfin 1
  obtain ⟨δ, hδ, hrb⟩ := restartBeyond H ν hν f hf S hS K hK
  obtain ⟨v, hvu, hvp⟩ := hrb a ha u p hsolve (by
    intro t ht
    simpa only [Nat.cast_one] using hKbound t ht)
  exact ⟨δ, hδ, v, hvu, hvp⟩

/-! ## 3. The maximal-existence input, discharged by the named local input -/

/-- Lane 323's residual input `PeriodicMaximalExistenceInput` follows from the
single named quantitative local-existence input through lane 321's selected
solution, so U15 and U16 rest on the *same* one name. -/
theorem periodicMaximalExistenceInput_of_input (H : PeriodicQuantitativeLocalInput') :
    PeriodicMaximalExistenceInput := by
  intro ν hν a ha f hf
  obtain ⟨δ, hδ, w, -⟩ := exists_periodicLocalSolution_of_input H ν hν a ha f hf
  exact ⟨δ, hδ, ⟨w⟩⟩

/-- The `PeriodicLocalTheoryAPI.exists_maximal` field, verbatim, now conditional
only on `PeriodicQuantitativeLocalInput'`. -/
theorem exists_maximal_of_input (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
            IsMaximalPeriodicSolution ν a f u p :=
  exists_maximal (periodicMaximalExistenceInput_of_input H)

/-! ## 4. U16 — the `lifespanInfiniteOfLocallyFinite` field -/

/-- **The `PeriodicContinuationAPI.lifespanInfiniteOfLocallyFinite` field,
verbatim.**

Same two conditions as `extendsBeyond_of_input`, and nothing else.  The proof
is the contraposition described in the module docstring; the criterion
hypothesis is used exactly once, at `S = (maximalLifespanT ν a f).toReal`,
where `ENNReal.ofReal S ≤ maximalLifespanT ν a f` holds with equality.  With
`<` in place of `≤` the hypothesis would be unavailable at that single point
and the statement unprovable (`research/T11/RECONCILIATION.md` §2). -/
theorem lifespanInfiniteOfLocallyFinite_of_input (H : PeriodicQuantitativeLocalInput')
    (hHigh : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M) :
    ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤ := by
  intro ν hν a ha f hf u p hmax hcrit
  by_contra hL
  set S : ℝ := (maximalLifespanT ν a f).toReal with hSdef
  have hpos : 0 < maximalLifespanT ν a f := hmax.1
  have hS : 0 < S := ENNReal.toReal_pos hpos.ne' hL
  have hofS : ENNReal.ofReal S = maximalLifespanT ν a f := ENNReal.ofReal_toReal hL
  have hfin : squaredHTwoIntegralT S u ≠ ⊤ := hcrit S hS hofS.le
  have hsolve : SolvesBelowT ν a f S u p := by
    intro b hb0 hbS
    refine hmax.2 b hb0 ?_
    rw [← hofS]
    exact (ENNReal.ofReal_lt_ofReal_iff hS).mpr hbS
  obtain ⟨δ, hδ, hle⟩ := lifespan_ge_of_extends
    (extendsBeyond_of_input H hHigh ν hν a ha f hf S hS u p hsolve hfin)
  have hle' : ENNReal.ofReal (S + δ) ≤ ENNReal.ofReal S := by
    rw [hofS]; exact hle
  have hcontra : S + δ ≤ S := (ENNReal.ofReal_le_ofReal_iff hS.le).mp hle'
  linarith

/-! ## 5. The criterion away from the terminal time, and non-vacuity -/

/-- **The continuation criterion is automatic strictly inside a horizon.**  The
`H²` profile of a classical solution is continuous on `[0, T)`, hence bounded on
the compact `[0, S] ⊆ [0, T)`, so the squared `H²` lintegral over `(0, S)` is
finite whenever `S < T`.  All the content of the criterion sits at the terminal
time, which is exactly why U16 has to apply it at `S = L.toReal`. -/
theorem squaredHTwoIntegralT_ne_top_of_lt {ν T S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (hST : S < T) :
    squaredHTwoIntegralT S w.velocity ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn
    ((continuousOn_torusSobolevNormAt_velocity w 2).mono
      (fun r hr ↦ ⟨hr.1, hr.2.trans_lt hST⟩))
  obtain ⟨G, -, hd⟩ := w.sobolev 2
  have hbound : ∀ r ∈ Ioo (0 : ℝ) S,
      periodicSobolevENorm 2 (fun x ↦ w.velocity (r, x)) ≤ ENNReal.ofReal C := by
    intro r hr
    have hne : periodicSobolevENorm 2 (fun x ↦ w.velocity (r, x)) ≠ ⊤ :=
      periodicSobolevENorm_ne_top_of_datum (hd r ⟨hr.1.le, hr.2.trans hST⟩)
    have heq : periodicSobolevENorm 2 (fun x ↦ w.velocity (r, x)) =
        ENNReal.ofReal (torusSobolevNormAt 2 w.velocity r) := by
      rw [torusSobolevNormAt, ENNReal.ofReal_toReal hne]
    have hCr := hC r ⟨hr.1.le, hr.2.le⟩
    rw [Real.norm_eq_abs] at hCr
    rw [heq]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hCr)
  have hvol : volume (Ioo (0 : ℝ) S) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hle : squaredHTwoIntegralT S w.velocity
      ≤ ENNReal.ofReal C ^ 2 * volume (Ioo (0 : ℝ) S) := by
    rw [← setLIntegral_const (Ioo (0 : ℝ) S) (ENNReal.ofReal C ^ 2)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact pow_le_pow_left' (hbound r hr) 2
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hvol) hle

/-- A constant divergence-free velocity, with zero force and zero pressure, is a
classical torus solution on every positive horizon.  This is the non-vacuity
witness for both targets: it needs no named input, and its velocity is nonzero
whenever `c` is. -/
def constantVelocitySolutionT (c : Space) {T : ℝ} (hT : 0 < T) :
    ClassicalSolutionT 1 (fun _ ↦ c) 0 T where
  velocity := fun _ ↦ c
  pressure := 0
  horizon_pos := hT
  velocity_smooth := contDiff_const.contDiffOn
  pressure_smooth := contDiff_const.contDiffOn
  initial := fun _ ↦ rfl
  divergence := by
    intro t _ht x
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ht x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
      temporalDerivative, advection, spatialDerivative, spatialLaplacian,
      pressureGradient]
  sobolev := by
    intro m
    obtain ⟨A, hA⟩ := exists_periodicDatum_smooth (m : ℝ)
      (z := fun _ ↦ c) contDiff_const (fun _ _ ↦ rfl)
    exact ⟨fun _ ↦ A, continuous_const.continuousOn, fun _ _ ↦ hA⟩
  pressure_gradient := by
    intro t _ht
    have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
      funext x
      simp [pressureGradient]
    rw [he]
    exact memLp_const (0 : Space)
  velocity_periodic := fun _ _ _ _ ↦ rfl
  pressure_periodic := fun _ _ _ _ ↦ rfl
  pressure_gauge := by
    intro t _ht
    simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]

/-- The squared `H²` lintegral of a constant velocity is finite on every
horizon: the integrand does not depend on time and the interval has finite
measure. -/
theorem squaredHTwoIntegralT_constant_ne_top (c : Space) (S : ℝ) :
    squaredHTwoIntegralT S (fun _ ↦ c) ≠ ⊤ := by
  have hC : periodicSobolevENorm 2 (fun _ : Space ↦ c) ≠ ⊤ :=
    periodicSobolevENorm_ne_top_smooth 2 contDiff_const (fun _ _ ↦ rfl)
  have hvol : volume (Ioo (0 : ℝ) S) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have hrw : squaredHTwoIntegralT S (fun _ : SpaceTime ↦ c) =
      periodicSobolevENorm 2 (fun _ : Space ↦ c) ^ 2 * volume (Ioo (0 : ℝ) S) := by
    have hdef : squaredHTwoIntegralT S (fun _ : SpaceTime ↦ c) =
        ∫⁻ _ in Ioo (0 : ℝ) S, periodicSobolevENorm 2 (fun _ : Space ↦ c) ^ 2 := rfl
    rw [hdef, setLIntegral_const]
  rw [hrw]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hC) hvol

/-- **Non-vacuity of both targets.**  Every hypothesis of
`extendsBeyond_of_input` and of `lifespanInfiniteOfLocallyFinite_of_input` is
inhabited simultaneously, at a genuinely nonzero velocity and with no named
input: an admissible datum, an admissible (compactly time-supported) force, a
`SolvesBelowT` pair whose `H²` criterion is finite on every horizon, and a
maximal solution carrying the locally-finite criterion. -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField) (u : SpaceTimeField)
      (p : SpaceTimeScalar),
      a ∈ initialClassT ∧ f ∈ forceClassT ∧ u (0, 0) ≠ 0 ∧
        SolvesBelowT 1 a f 1 u p ∧ squaredHTwoIntegralT 1 u ≠ ⊤ ∧
        IsMaximalPeriodicSolution 1 a f u p ∧
        (∀ S : ℝ, 0 < S → ENNReal.ofReal S ≤ maximalLifespanT 1 a f →
          squaredHTwoIntegralT S u ≠ ⊤) := by
  let c : Space := coordinateVector 0
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h0
  have ha : (fun _ ↦ c) ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [spatialDivergence, spatialDerivative]
  have hf : (0 : SpaceTimeField) ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
    simp
  refine ⟨fun _ ↦ c, 0, fun _ ↦ c, 0, ha, hf, hc, ?_,
    squaredHTwoIntegralT_constant_ne_top c 1, ⟨?_, ?_⟩,
    fun S _ _ ↦ squaredHTwoIntegralT_constant_ne_top c S⟩
  · exact fun b hb0 _ ↦ ⟨constantVelocitySolutionT c hb0, rfl, rfl⟩
  · exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr one_pos)
      (lifespan_ge_of_horizon (constantVelocitySolutionT c one_pos))
  · exact fun S hS _ ↦ ⟨constantVelocitySolutionT c hS, rfl, rfl⟩

end NSFormalization.Section3.T11
