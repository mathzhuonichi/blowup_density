import NSFormalization.Paper1.PeriodicLocalLifespan
import NSFormalization.Paper1.PeriodicPressureNormalization

/-!
# Finite `H²` energy bridge

This file isolates the elementary measure-theoretic part of the continuation
criterion.  The PDE regularity theorem must still provide continuity (or an
independent integrability certificate) for the actual periodic `H²` profile.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicFiniteH2Bridge

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicLocalLifespan
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicPressureNormalization
open NSFormalization.Paper1.PeriodicForceConvergence
open NavierStokes NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped ENNReal

/-- The logically minimal bridge: an explicit integrability certificate is exactly
`FiniteH2Energy`.  This wrapper lets analytic agents export their own measure
model without imposing continuity. -/
theorem finiteH2Energy_of_integrable_profile
    {ν S : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    FiniteH2Energy W := hprof

/-- A continuous squared-`H²` profile on a finite Flow horizon supplies the
`FiniteH2Energy` predicate.  This is deliberately conditional: continuity of
`periodicVectorSobolevNorm 2` along an arbitrary classical `Flow` remains part
of the analytic local-theory bridge. -/
theorem finiteH2Energy_of_continuousOn_profile
    {ν S : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S)
    (hprof : ContinuousOn (h2SquaredProfile W) (Icc (0 : ℝ) S)) :
    FiniteH2Energy W := by
  unfold FiniteH2Energy
  have hint : IntegrableOn (h2SquaredProfile W) (Icc (0 : ℝ) S) volume :=
    hprof.integrableOn_compact isCompact_Icc
  exact hint.mono_set Ioc_subset_Icc_self

theorem finiteH2Energy_of_continuous_profile
    {ν S : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S)
    (hprof : Continuous (h2SquaredProfile W)) :
    FiniteH2Energy W := by
  unfold FiniteH2Energy
  have hS : IsCompact (Icc (0 : ℝ) S) := isCompact_Icc
  have hcont : ContinuousOn (h2SquaredProfile W) (Icc (0 : ℝ) S) :=
    hprof.continuousOn
  have hint : IntegrableOn (h2SquaredProfile W) (Icc (0 : ℝ) S) volume :=
    hcont.integrableOn_compact hS
  exact hint.mono_set Ioc_subset_Icc_self

/-- The same bridge with continuity supplied directly by a regularity package.
This wrapper is useful for agents proving continuity under a different API. -/
theorem finiteH2Energy_of_profile_regular
    {ν S : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S)
    (hregular : Continuous (h2SquaredProfile W)) :
    FiniteH2Energy W :=
  finiteH2Energy_of_continuous_profile W hregular

/-- Direct continuation wrapper for an analytic integrability certificate.  The
PDE side only has to prove the displayed integral; all lifespan bookkeeping is
delegated to `PeriodicLocalLifespan`. -/
theorem extension_of_integrable_profile
    (H : ClassicalPeriodicLocalTheory)
    {ν S : ℝ} (hν : 0 < ν) {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (hf : IsSmoothPeriodicForce f) (W : Flow ν a f S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    ∃ T : ℝ, S < T ∧ ∃ V : Flow ν a f T, IsNormalized V ∧
      ∀ t ∈ Ico (0 : ℝ) S, ∀ x : NavierStokes.ProblemStatement.Space,
        V.velocity (t, x) = W.velocity (t, x) ∧
        V.pressure (t, x) = normalizedPressure W.pressure (t, x) := by
  exact exists_periodic_extension_of_finite_h2 H hν hf W
    (finiteH2Energy_of_integrable_profile W hprof)

/-- Integrability certificates descend to every shorter positive horizon.  This
set-theoretic restriction is the measure component used before constructing the
corresponding restricted `Flow`. -/
theorem integrable_profile_mono_horizon
    {ν S R : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) R) volume := by
  exact hprof.mono_set (Ioc_subset_Ioc_right hRS)

/-- Combined short-horizon wrapper: an integrability certificate on `S`
produces `FiniteH2Energy` for the profile restricted to any `R ≤ S`. -/
theorem finiteH2Energy_on_short_horizon
    {ν S R : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) R) volume :=
  integrable_profile_mono_horizon W _hR hRS hprof

/-- Restriction-compatible form: because `Flow.restrict` preserves the
velocity field definitionally, a short-horizon profile certificate yields
`FiniteH2Energy` for the restricted Flow itself. -/
theorem finiteH2Energy_restrict
    {ν S R : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) R) volume) :
    FiniteH2Energy (W.restrict _hR hRS) := by
  unfold FiniteH2Energy
  change IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) R) volume
  exact hprof

/-- A full-horizon certificate automatically supplies finite energy for every
restricted Flow. -/
theorem finiteH2Energy_restrict_of_full
    {ν S R : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    FiniteH2Energy (W.restrict _hR hRS) := by
  apply finiteH2Energy_restrict W _hR hRS
  exact integrable_profile_mono_horizon W _hR hRS hprof

/-- Transitive profile monotonicity for two successive horizon cuts. -/
theorem integrable_profile_mono_horizon_trans
    {ν S R Q : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (_hQ : 0 < Q) (hQR : Q ≤ R)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) Q) volume := by
  exact integrable_profile_mono_horizon W _hQ (hQR.trans hRS) hprof

/-- Multi-stage restriction preserves the finite-energy certificate; the nested
restriction is definitionally the direct restriction. -/
theorem finiteH2Energy_restrict_trans
    {ν S R Q : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (_hQ : 0 < Q) (hQR : Q ≤ R)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    FiniteH2Energy ((W.restrict _hR hRS).restrict _hQ hQR) := by
  rw [Flow.restrict_restrict_eq_restrict W _hR hRS _hQ hQR]
  exact finiteH2Energy_restrict_of_full W _hQ (hQR.trans hRS) hprof

/-- Minimal short-profile composition: a certificate on the intermediate
horizon is enough to certify every further restriction. -/
theorem finiteH2Energy_restrict_trans_of_intermediate
    {ν S R Q : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (_hQ : 0 < Q) (hQR : Q ≤ R)
    (hprofR : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) R) volume) :
    FiniteH2Energy ((W.restrict _hR hRS).restrict _hQ hQR) := by
  rw [Flow.restrict_restrict_eq_restrict W _hR hRS _hQ hQR]
  exact finiteH2Energy_restrict W _hQ (hQR.trans hRS)
    (hprofR.mono_set (Ioc_subset_Ioc_right hQR))

/-- Three-stage restriction composition, useful for repeated continuation
restarts. -/
theorem finiteH2Energy_restrict_three
    {ν S R Q P : ℝ} {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
    {f : NavierStokes.ProblemStatement.VelocityField}
    (W : Flow ν a f S) (_hR : 0 < R) (hRS : R ≤ S)
    (_hQ : 0 < Q) (hQR : Q ≤ R) (_hP : 0 < P) (hPQ : P ≤ Q)
    (hprof : IntegrableOn (h2SquaredProfile W) (Ioc (0 : ℝ) S) volume) :
    FiniteH2Energy (((W.restrict _hR hRS).restrict _hQ hQR).restrict _hP hPQ) := by
  rw [Flow.restrict_restrict_eq_restrict, Flow.restrict_restrict_eq_restrict]
  exact finiteH2Energy_restrict_of_full W _hP (hPQ.trans (hQR.trans hRS)) hprof

end NSFormalization.Paper1.PeriodicFiniteH2Bridge
