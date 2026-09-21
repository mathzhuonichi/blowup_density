import NSFormalization.Section3.T11.PairingBound
import NSFormalization.Section3.T11.ExistenceInputH3

/-! Periodic higher-order continuation estimates with only a finite-window
force bound. No global time-integrability or temporal support is used. -/
noncomputable section
namespace NSFormalization.Section3.T11
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

local instance localBoundsNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance localBoundsNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-- The running force integral is bounded on any fixed compact time interval. -/
theorem local_force_profile_cap {f : SpaceTimeField} (hf : ContDiff ℝ ∞ f)
    (hper : IsPeriodicOn univ f) {S : ℝ} (hS : 0 ≤ S) (m : ℕ) :
    Continuous (fun t => torusSobolevNormAt (m : ℝ) f t) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) S,
        (∫ s in (0 : ℝ)..t, torusSobolevNormAt (m : ℝ) f s) ≤ B := by
  obtain ⟨G, hc, hd⟩ := exists_smooth_forceDatumPath hf hper m
  have he : (fun t => torusSobolevNormAt (m : ℝ) f t) = fun t => ‖G t‖ := by
    funext t
    exact torusSobolevNormAt_eq (hd t)
  rw [he]
  refine ⟨hc.continuous.norm, ∫ s in (0 : ℝ)..S, ‖G s‖,
    intervalIntegral.integral_nonneg hS (fun s _ => norm_nonneg _), ?_⟩
  intro t ht
  exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall fun s => norm_nonneg _) (hc.continuous.norm.intervalIntegrable 0 S)

/-- The classical energy inequality only uses smoothness and periodicity of
its actual force, without membership in the density force class. -/
theorem local_force_energy_bound {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) (hper : IsPeriodicOn univ f)
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ d g : ℝ, 0 ≤ g ∧
      HasDerivAt (fun r => torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
      (1 / 2) * d + ν * g ^ 2 ≤
        torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 w.velocity t *
          torusSobolevNormAt (m : ℝ) w.velocity t * g +
        torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t := by
  have htI : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  obtain ⟨Gm, _, hGmd⟩ := w.sobolev m
  have hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) (Gm t) := hGmd t htI
  obtain ⟨Fm, hFm⟩ := exists_force_datum hf hper (m : ℝ) t
  obtain ⟨Nm, hNm⟩ := exists_convection_datum w (m : ℝ) htI
  set g : ℝ := torusGradientNormAt (m : ℝ) w.velocity t with hgdef
  refine ⟨-2 * ν * g ^ 2 + 2 * torusRealPairing (Gm t) Fm - 2 * torusRealPairing (Gm t) Nm,
    g, torusGradientNormAt_nonneg _ _ _,
    energyIdentity_of_classical w hf m ht hGm hFm hNm, ?_⟩
  have hGnorm : torusSobolevNormAt (m : ℝ) w.velocity t = ‖Gm t‖ := torusSobolevNormAt_eq hGm
  have hFnorm : torusSobolevNormAt (m : ℝ) f t = ‖Fm‖ := torusSobolevNormAt_eq hFm
  have hforce : torusRealPairing (Gm t) Fm ≤
      torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t := by
    rw [hGnorm, hFnorm, mul_comm]
    exact torusRealPairing_le (Gm t) Fm
  have hconv : -torusRealPairing (Gm t) Nm ≤
      torusPairingConstant (m : ℝ) * torusSobolevNormAt 2 w.velocity t *
        torusSobolevNormAt (m : ℝ) w.velocity t * g :=
    by
      obtain ⟨G1, _, hG1⟩ := w.sobolev (m + 1)
      have hg1 : IsPeriodicDatum ((m : ℝ) + 1)
          (fun x => w.velocity (t, x)) (G1 t) := by
        have h := hG1 t htI
        have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
        rwa [hcast] at h
      exact (neg_le_abs _).trans (torusPairingBound_slice hm
        (classical_velocity_slice_contDiff w htI) (w.velocity_periodic t htI)
        hGm hg1 hNm)
  linarith

/-- The squared-`H²` criterion bounds all higher norms for a smooth periodic
force using only its norms on `[0,S]`. -/
theorem higherOrderBound_smoothForceT
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (f : SpaceTimeField)
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodicOn univ f)
    (S : ℝ) (hS : 0 < S) (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu : SolvesBelowT ν a f S u p) (hfin : squaredHTwoIntegralT S u ≠ ⊤)
    (m : ℕ) : ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) S,
      periodicSobolevENorm (m : ℝ) (fun x => u (t, x)) ≤ M := by
  set n : ℕ := max m 3 with hnd
  have h3n : 3 ≤ n := le_max_right m 3
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 3
  obtain ⟨hfc, B, _hB0, hBcap⟩ := local_force_profile_cap hf hper hS.le n
  refine ⟨ENNReal.ofReal ((torusSobolevNormAt (n : ℝ) u 0 + B) *
      Real.exp (torusPairingConstant (n : ℝ) ^ 2 / (4 * ν) * (squaredHTwoIntegralT S u).toReal)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  obtain ⟨w, hwv, _⟩ := hu ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
  have htb : t ∈ Ico (0 : ℝ) ((t + S) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hbS : (t + S) / 2 ≤ S := by linarith [ht.2]
  have hchain := torusGronwallChain (T₀ := (t + S) / 2) (C := torusPairingConstant (n : ℝ)) (ν := ν)
    (Kbnd := (squaredHTwoIntegralT S u).toReal) (Bbnd := B)
    (y := fun r ↦ torusSobolevNormAt (n : ℝ) w.velocity r)
    (a := fun r ↦ torusSobolevNormAt 2 w.velocity r)
    (b := fun r ↦ torusSobolevNormAt (n : ℝ) f r)
    hν
    (continuousOn_torusSobolevNormAt_velocity w n)
    (fun r ↦ torusSobolevNormAt_nonneg _ _ _)
    (continuousOn_torusSobolevNormAt_velocity w 2)
    hfc.continuousOn
    (fun r ↦ torusSobolevNormAt_nonneg _ _ _)
    (fun r hr ↦ by
      have hrun := running_hTwo_integral_le w hwv hbS hfin hr
      rw [hwv]
      exact hrun)
    (fun r hr ↦ hBcap r ⟨hr.1, hr.2.le.trans hbS⟩)
    (fun r hr ↦ local_force_energy_bound w hf hper n h3n r hr)
    t htb
  obtain ⟨G, _, hd⟩ := w.sobolev n
  have hdat : IsPeriodicDatum (n : ℝ) (fun x ↦ u (t, x)) (G t) := by
    rw [← hwv]
    exact hd t htb
  calc periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x))
      ≤ periodicSobolevENorm (n : ℝ) (fun x ↦ u (t, x)) :=
        periodicSobolevENorm_mono_order hmn _
    _ = ENNReal.ofReal (torusSobolevNormAt (n : ℝ) u t) := by
        rw [torusSobolevNormAt,
          ENNReal.ofReal_toReal (periodicSobolevENorm_ne_top_of_datum hdat)]
    _ ≤ ENNReal.ofReal ((torusSobolevNormAt (n : ℝ) u 0 + B) *
          Real.exp (torusPairingConstant (n : ℝ) ^ 2 / (4 * ν) * (squaredHTwoIntegralT S u).toReal)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hwv] at hchain
        exact hchain

end NSFormalization.Section3.T11
