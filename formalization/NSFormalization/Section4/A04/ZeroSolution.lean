import NSFormalization.Section4.A04.DerivNorm
import NSFormalization.Section4.A04.LaplacianDatum
import NSFormalization.Section4.A04.PressureDrop
import NSFormalization.Section4.D01.DatumToJets

/-!
# A04 MAINT: the zero classical solution and its witnesses, once

Lane 144 (MAINT).  Half a dozen conformance and non-vacuity files rebuild the
same object inline — the zero velocity/pressure on `[0,T)` as a
`ClassicalSolutionR`, together with the facts that the zero force lies in `F_R`,
the zero datum lies in the initial class `X_R`, and the zero field has vanishing
`H^s`/`\dot H^s` slice norms and a smooth Sobolev datum path.  This module lands
that construction once so the probes can `import` it instead of re-deriving it.

## Sources consolidated (each contributed the copy below verbatim or nearly so)

* `research/A01/axioms_a3_m2.lean` (lane 142): `zeroSol`, `datum_zero`,
  `memForceR_zero`, `zero_mem_initialClassR`, `path_zero`, `sobolevNormAt_zero`.
* `research/D01/REVIEW_SL8_ASSEMBLY.md` appendix A (lane 117 reviewer):
  `zeroSol`, `memForceR_zero`, `const_not_jets`, `jets_zero`.
* `research/A04/REVIEW_ENERGY_HIGH.md` appendix (lane 128 reviewer): the
  `HasSmoothSobolevPath` witness for the zero path.
* `research/A04/REVIEW_CONTRACT{,_V2}.md` probes (contract-level `zeroSol`).

## Layer

This is the **lowest** layer whose imports suffice: the deliverables span
`ClassicalSolutionR`/`initialClassR` (A02), `MemForceR`/`SmoothSquareIntegrableJets`
(D01) and `HasSmoothSobolevPath`/`sobolevNormAt`/`gradientSobolevNormAt`
(A04, in `DerivNorm`/`Forcing`/`LaplacianDatum`), and A04 sits above both A02 and
D01, so it is the first layer that sees all of them.  Nothing here is A04-specific
mathematics; the module only assembles pre-existing D01/A02/A04 facts on the zero
field.

## Reuse, not duplication

`isSobolevDatum_zero` (the "zero datum at every order") already lives one module
down at `A04.PressureDrop:170`; it is used directly here rather than restated.
`memForceR_zero` is proved directly against `D01.MemForceR` (as lane 142 did)
rather than through `memForceR_of_memForceCompact`, because the compact route
would additionally need a `CompactPositiveTimeSupport 0` proof for no gain.
`MemForceR` is taken from `D01` (opened explicitly, not from `A02`) to avoid the
ambiguity between the two byte-identical restatements (`logs/LESSONS.md`, the
`MemForceR` note); `D01.MemForceR` is defeq to `A02.MemForceR`, so consumers that
expect either accept the witness.

`_hν : 0 < ν` is carried in `zeroSol`'s signature to fix the intended viscous
regime and to match every consumer's own hypothesis, but the zero solution exists
for any `ν` (no field constrains its sign), so the binder is genuinely unused and
is named with a leading underscore.
-/

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
  (IsSobolevDatum MemForceR SmoothSquareIntegrableJets sobolevENorm)
open NSFormalization.Section4.A02 (ClassicalSolutionR initialClassR SpaceTimeField SpatialField)
open NSFormalization.Section4.A03 (partialDeriv)
open scoped ContDiff

noncomputable section

namespace NSFormalization.Section4.A04

/-! ## 0. The zero force and the zero initial datum -/

/-- The zero force lies in `F_R` (`02-preliminaries.tex:17-22`, eq:Rclasses): smooth on
`futureDomain` with the identically-zero order-`m` datum path, which is `L¹` and `L²`
in time. -/
theorem memForceR_zero : MemForceR (0 : SpaceTimeField) := by
  refine ⟨contDiffOn_const,
    fun m => ⟨fun _ => 0, fun t _ => isSobolevDatum_zero _, contDiffOn_const, ?_, ?_⟩⟩
  · exact MemLp.zero
  · exact MemLp.zero

/-- The zero field lies in the initial class `X_R = H^∞ ∩ L²_σ`
(`02-preliminaries.tex:12-13`, eq:Rinitial): it is `H^∞` (smooth, with the zero datum
at every order) and solenoidal. -/
theorem zero_mem_initialClassR : (0 : SpatialField) ∈ initialClassR := by
  refine ⟨⟨contDiff_const, fun m => ⟨0, isSobolevDatum_zero (m : ℝ)⟩⟩, ?_⟩
  intro x
  simp [spatialDivergence, spatialDerivative]

/-! ## 1. The zero classical solution -/

/-- **The zero classical solution** on `[0,T)`: zero velocity, zero pressure, zero
initial datum and zero force, at any viscosity `ν`.  The analytic fields (`divergence`,
`momentum`, `pressure_gradient`) unfold by `simp` — the eq:NS residual
(`01-introduction.tex:4`) of the zero pair is `0 = f`; the rest are `contDiffOn_const`,
`rfl`, and the constant-`0` datum path built on the tree's `isSobolevDatum_zero`. -/
def zeroSol (ν T : ℝ) (_hν : 0 < ν) (hT : 0 < T) : ClassicalSolutionR ν 0 0 T where
  velocity := 0
  pressure := 0
  horizon_pos := hT
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial := fun _ => rfl
  divergence := by intro t _ x; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => isSobolevDatum_zero _⟩
  pressure_gradient := by intro t _; simp [pressureGradient]

@[simp] theorem zeroSol_velocity (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    (zeroSol ν T hν hT).velocity = 0 := rfl

@[simp] theorem zeroSol_pressure (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    (zeroSol ν T hν hT).pressure = 0 := rfl

/-! ## 2. The Sobolev slice norms of the zero field vanish -/

/-- `‖0(t)‖_{H^s} = 0`: the zero slice has the zero datum, whose `.toReal` enorm is
`0`. -/
theorem sobolevNormAt_zero (s t : ℝ) : sobolevNormAt s (0 : SpaceTimeField) t = 0 := by
  have hd : IsSobolevDatum s (fun x : Space => (0 : SpaceTimeField) (t, x)) 0 :=
    isSobolevDatum_zero s
  show (sobolevENorm s (fun x : Space => (0 : SpaceTimeField) (t, x))).toReal = 0
  rw [sobolevENorm_eq hd]; simp

/-- `‖∇0(t)‖_{H^s} = 0`: each of the three partial derivatives of the zero field is
the zero field, so every column enorm vanishes and the `ℓ²` assembly is `0`. -/
theorem gradientSobolevNormAt_zero (s t : ℝ) :
    gradientSobolevNormAt s (0 : SpaceTimeField) t = 0 := by
  have hz : ∀ j : Fin 3,
      sobolevENorm s (partialDeriv j (fun x : Space => (0 : SpaceTimeField) (t, x))) = 0 := by
    intro j
    have hpd : partialDeriv j (fun x : Space => (0 : SpaceTimeField) (t, x))
        = fun _ : Space => (0 : Space) := by
      funext x
      simp [partialDeriv, NSFormalization.Section4.A03.lift, spatialDerivative]
    rw [hpd, sobolevENorm_eq (isSobolevDatum_zero s)]; simp
  have hfin : ∀ j : Fin 3,
      sobolevENorm s (partialDeriv j (fun x : Space => (0 : SpaceTimeField) (t, x))) ≠ ⊤ := by
    intro j; rw [hz j]; exact ENNReal.zero_ne_top
  have hsq : gradientSobolevNormAt s (0 : SpaceTimeField) t ^ 2 = 0 := by
    rw [gradientSobolevNormAt_sq_eq_sum hfin]
    apply Finset.sum_eq_zero
    intro j _
    rw [hz j]; simp
  exact pow_eq_zero_iff (by norm_num) |>.mp hsq

/-! ## 3. The smooth Sobolev datum path of the zero field -/

/-- The zero field has a `HasSmoothSobolevPath` on any horizon: the identically-zero
datum path represents every slice and is `C^∞` in time. -/
theorem hasSmoothSobolevPath_zero (T : ℝ) : HasSmoothSobolevPath T (0 : SpaceTimeField) := by
  intro m
  exact ⟨fun _ => 0, fun t _ => isSobolevDatum_zero _, contDiffOn_const⟩

/-- The `zeroSol`-specialised form (lane 142 name `path_zero`): the zero solution's
velocity has a smooth Sobolev path, since its velocity is `0` by `rfl`. -/
theorem path_zero (ν T : ℝ) (hν : 0 < ν) (hT : 0 < T) :
    HasSmoothSobolevPath T (zeroSol ν T hν hT).velocity :=
  hasSmoothSobolevPath_zero T

/-! ## 4. Non-triviality witnesses for the jet class -/

/-- The zero field **is** in the smooth square-integrable jet class: every Fréchet
jet of the constant `0` is the zero function, hence `L²`. -/
theorem jets_zero : SmoothSquareIntegrableJets (fun _ : Space => (0 : Space)) := by
  refine ⟨contDiff_const, fun n => ?_⟩
  have : iteratedFDeriv ℝ n (fun _ : Space => (0 : Space)) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext x m; simp
    · exact iteratedFDeriv_const_of_ne (by omega) _
  rw [this]; exact MemLp.zero

/-- A nonzero **constant** field is `C^∞` but **not** in the jet class: its
order-`0` jet is the nonzero constant `c`, which is not `L²` on `R³`.  The
non-triviality witness the P2 reviews use — the jet class is not satisfied by
every smooth field. -/
theorem const_not_jets {c : Space} (hc : c ≠ 0) :
    ContDiff ℝ ∞ (fun _ : Space => c) ∧ ¬ SmoothSquareIntegrableJets (fun _ : Space => c) := by
  refine ⟨contDiff_const, ?_⟩
  rintro ⟨-, h⟩
  have h0 := h 0
  have hconst : MemLp (fun _ : Space => c) 2 volume := by
    refine ⟨aestronglyMeasurable_const, ?_⟩
    have h2 := h0.2
    rwa [eLpNorm_congr_norm_ae (f := iteratedFDeriv ℝ 0 (fun _ : Space => c))
      (g := fun _ : Space => c)
      (Filter.Eventually.of_forall (fun x => by simp [norm_iteratedFDeriv_zero]))] at h2
  rcases (memLp_const_iff (p := 2) two_ne_zero (by simp)).mp hconst with hz | hv
  · exact hc hz
  · simp at hv

end NSFormalization.Section4.A04
