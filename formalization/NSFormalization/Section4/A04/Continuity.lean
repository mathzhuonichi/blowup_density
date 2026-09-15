import NSFormalization.Section4.A04.Forcing

/-!
# A04 unit N1: the continuation integrand is continuous, hence interval integrable

`research/A04/COMPARISON.md` §4 unit **N1**.  The A04 draft
(`research/A04/Spec.lean`) measures the differential and integrated fields on
`sobolevNormAt`, the `.toReal` of the fail-safe `ℝ≥0∞`-valued `sobolevENorm`.
On the slices of a classical solution and of an `F_R` force that `.toReal` is
the honest norm, because the underlying `ℝ≥0∞` value is finite, and the norm
varies continuously in time.  This module proves that bookkeeping and cashes it
where `Spec.lean` needs it: the `IntervalIntegrable` conjunct of
`ContinuationAPI.highContinuationIntegral` (`Spec.lean:494-510`, `REVIEW.md`
finding 6).

* `sobolevENorm_velocity_ne_top` / `sobolevENorm_force_ne_top` — the finiteness
  `ClassicalSolutionR.sobolev` (`SolutionClass.lean:119`, `Data.lean:643`) and
  `MemForceR` (`SolutionClass.lean:88`, `Data.lean:544`) supply at every integer
  order and every admissible time, so `sobolevNormAt` is the datum norm and not a
  `⊤ ↦ 0` artefact.
* `continuousOn_sobolevNormAt_of_datumPath` — the general step: a continuous
  representing datum path makes `t ↦ sobolevNormAt s u t` continuous, via
  `sobolevENorm (s) (u(t,·)) = ‖G t‖ₑ` (`Forcing.sobolevENorm_eq`) and
  `(‖G t‖ₑ).toReal = ‖G t‖`.
* `continuousOn_sobolevNormAt_velocity` / `continuousOn_sobolevNormAt_force` —
  its two instances, from the `ContinuousOn G` conjunct of
  `ClassicalSolutionR.sobolev` and the `ContDiffOn ℝ ∞ G futureTimes` conjunct of
  `MemForceR`.
* `intervalIntegrable_highContinuationIntegrand` — the payoff: on
  `[t₀,t] ⊆ [0,T)` the integrand
  `Cgron m ν · ‖u(s)‖²_{H²} · ‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}` is continuous, hence
  `IntervalIntegrable`, so the conjunct costs the implementer nothing.

`HasSmoothSobolevPath` is **not** used: continuity of the norm comes from the
plain `ContinuousOn` datum path of `ClassicalSolutionR.sobolev`, not from the
`C^∞`-in-time regularity A01 supplies (that is unit D1, for the differential
fields).

See `Forcing.lean` for the restated `def`s and the `rfl` coincidence of the
A02/D01 vocabulary; every statement below is definitionally in the spec's
vocabulary, so `research/A04/axioms_f1n1.lean` discharges the N1 spec statement
by `exact`.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02
  (SpaceTimeField SpatialField SpaceTimeScalar MemForceR IsSobolevPath ClassicalSolutionR
    forceTimeMeasure)
open NSFormalization.Section4.D01
  (sobolevENorm sobolevENorm_le_of_isSobolevDatum isSobolevDatum_unique IsSobolevDatum)

/-! ## 1. Finiteness of the `ℝ≥0∞` norm on the smooth classes -/

/-- The velocity `H^m` norm of a classical solution is finite at every integer
order and every time of `[0,T)`: `ClassicalSolutionR.sobolev` gives a datum
there, and the enorm of a datum is finite. -/
theorem sobolevENorm_velocity_ne_top {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    sobolevENorm (m : ℝ) (fun x : Space => w.velocity (t, x)) ≠ ⊤ := by
  obtain ⟨G, _, hGd⟩ := w.sobolev m
  rw [sobolevENorm_eq (hGd t ht)]
  exact enorm_ne_top

/-- The force `H^m` norm of a member of `F_R` is finite at every integer order
and every nonnegative time: `MemForceR` gives a datum path on `[0,∞)`. -/
theorem sobolevENorm_force_ne_top {f : SpaceTimeField} (hf : MemForceR f) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) : sobolevENorm (m : ℝ) (fun x : Space => f (t, x)) ≠ ⊤ := by
  obtain ⟨G, hpath, _, _, _⟩ := hf.2 m
  rw [sobolevENorm_eq (hpath t ht)]
  exact enorm_ne_top

/-! ## 2. Continuity of `t ↦ sobolevNormAt s u t` -/

/-- The real-valued half of N1 (`REVIEW_F1N1.md` finding 5): where a slice has a
datum `A`, `sobolevNormAt s u t` **is** the datum norm `‖A‖` and not a `⊤ ↦ 0`
artefact — `sobolevENorm = ‖A‖ₑ` (uniqueness), then `(‖A‖ₑ).toReal = ‖A‖`. -/
theorem sobolevNormAt_eq {s : ℝ} {u : SpaceTimeField} {t : ℝ} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s (fun x : Space => u (t, x)) A) : sobolevNormAt s u t = ‖A‖ := by
  show (sobolevENorm s (fun x : Space => u (t, x))).toReal = ‖A‖
  rw [sobolevENorm_eq hA, ← ofReal_norm]
  exact ENNReal.toReal_ofReal (norm_nonneg _)

/-- **The N1 core.**  If a field has a datum path `G` continuous on `Ico 0 T`
and representing its slices there, then `t ↦ sobolevNormAt s u t` is continuous
on `Ico 0 T`: on that set it equals `t ↦ ‖G t‖` (`sobolevNormAt_eq`), which is
continuous. -/
theorem continuousOn_sobolevNormAt_of_datumPath
    {s : ℝ} {u : SpaceTimeField} {T : ℝ} {G : ℝ → RealVectorSobolev s}
    (hGc : ContinuousOn G (Ico (0 : ℝ) T))
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum s (fun x : Space => u (t, x)) (G t)) :
    ContinuousOn (fun t => sobolevNormAt s u t) (Ico (0 : ℝ) T) := by
  refine (hGc.norm).congr ?_
  intro t ht
  exact sobolevNormAt_eq (hGd t ht)

/-- The velocity norm of a classical solution is continuous on `[0,T)` at every
integer order (the `ContinuousOn G` conjunct of `ClassicalSolutionR.sobolev`). -/
theorem continuousOn_sobolevNormAt_velocity {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : ClassicalSolutionR ν a f T) (m : ℕ) :
    ContinuousOn (fun t => sobolevNormAt (m : ℝ) w.velocity t) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hGc, hGd⟩ := w.sobolev m
  exact continuousOn_sobolevNormAt_of_datumPath hGc hGd

/-- The force norm of a member of `F_R` is continuous on `[0,T)` at every integer
order (the `ContDiffOn ℝ ∞ G futureTimes` conjunct of `MemForceR`, restricted to
`Ico 0 T ⊆ Ici 0`). -/
theorem continuousOn_sobolevNormAt_force {f : SpaceTimeField} (hf : MemForceR f) (m : ℕ) (T : ℝ) :
    ContinuousOn (fun t => sobolevNormAt (m : ℝ) f t) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hpath, hc, _, _⟩ := hf.2 m
  refine continuousOn_sobolevNormAt_of_datumPath (G := G) ?_ ?_
  · exact hc.continuousOn.mono (fun t ht => ht.1)
  · intro t ht
    exact hpath t ht.1

/-! ## 3. N1 payoff: the `IntervalIntegrable` conjunct is free -/

/-- **N1.**  The integrand of `ContinuationAPI.highContinuationIntegral`
(`research/A04/Spec.lean:500-503`),
`Cgron m ν · ‖u(s)‖²_{H²} · ‖u(s)‖_{H^m} + ‖f(s)‖_{H^m}`, is `IntervalIntegrable`
on `[t₀,t]` whenever `0 ≤ t₀ ≤ t < T` for a classical solution `w` and a force
`f ∈ F_R`.  On `uIcc t₀ t = [t₀,t] ⊆ [0,T)` each `sobolevNormAt` factor is
continuous (§2), so the integrand is continuous, and a continuous function on a
compact interval is interval integrable.  This is why the draft may **assert**
the conjunct rather than assume integrability (`REVIEW.md` finding 6). -/
theorem intervalIntegrable_highContinuationIntegrand
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hf : MemForceR f) (w : ClassicalSolutionR ν a f T)
    (Cgron : ℕ → ℝ → ℝ) (m : ℕ) {t₀ t : ℝ}
    (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t) (htT : t < T) :
    IntervalIntegrable
      (fun s : ℝ =>
        Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 * sobolevNormAt (m : ℝ) w.velocity s +
          sobolevNormAt (m : ℝ) f s) volume t₀ t := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le htt]
  have hsub : Icc t₀ t ⊆ Ico (0 : ℝ) T := fun x hx => ⟨le_trans ht₀ hx.1, lt_of_le_of_lt hx.2 htT⟩
  -- `((2 : ℕ) : ℝ) = (2 : ℝ)` is `rfl` at this toolchain, so no cast rewrite is needed.
  have hv2 : ContinuousOn (fun s => sobolevNormAt 2 w.velocity s) (Icc t₀ t) :=
    (continuousOn_sobolevNormAt_velocity w 2).mono hsub
  have hvm : ContinuousOn (fun s => sobolevNormAt (m : ℝ) w.velocity s) (Icc t₀ t) :=
    (continuousOn_sobolevNormAt_velocity w m).mono hsub
  have hfm : ContinuousOn (fun s => sobolevNormAt (m : ℝ) f s) (Icc t₀ t) :=
    (continuousOn_sobolevNormAt_force hf m T).mono hsub
  exact ((continuousOn_const.mul (hv2.pow 2)).mul hvm).add hfm

end NSFormalization.Section4.A04
