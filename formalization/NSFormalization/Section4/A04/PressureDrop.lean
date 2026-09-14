import NSFormalization.Section4.A04.MomentumDatum
import NSFormalization.Section4.A04.HighEnergy
import NSFormalization.Section4.D01.PressureJets
import NSFormalization.Section4.D01.RealPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A04 unit G1, sub-lemma SL4: the pressure drop `⟪u, ∇p⟫_{H^m} = 0` (the `hpr` of eq:Rhigh)

`research/A04/G1_SPLIT.md` sub-lemma **SL4** / `research/D01/REVIEW_SL8_ASSEMBLY.md` §7.  The last
missing input of A04's `energyIdentityHigh` assembly is `hpr`, the pressure-drop hypothesis of
`Section4/A04/HighEnergy.lean`'s `inner_energy_assembly` / `inner_energy_Rhigh`:

`hpr : ⟪G, P⟫ = 0`,   `G` the order-`m` datum of `u(t,·)`, `P` the order-`m` datum of `∇p(t,·)`.

This module proves it by the cheap operator-algebra route of `REVIEW_SL8_ASSEMBLY.md` §7 (Leray
self-adjointness + solenoidality), in three recorded steps:

* **(S) Self-adjointness** — `lerayComplement_selfAdjoint`: the Leray-complement multiplier
  `Leray.lerayComplement s : RealVectorSobolev s →L[ℝ] RealVectorSobolev s` is self-adjoint for the
  real datum-carrier inner product, `⟪(I−P) A, B⟫ = ⟪A, (I−P) B⟫`.  Route: `lerayComplement` is the
  restriction of `Leray.lerayComplementAmbient` (`Leray.lerayComplement_toAmbient`), which is the
  `coordinates ∘ lerayComplementL2 ∘ assemble` conjugate of the `L²` multiplier `lerayComplementL2`
  by the `q = 2` `coordinates`/`assemble` isometry.  `lerayComplementL2` is self-adjoint fibrewise
  because its fibre symbol `complementSymbolComplex ξ = (ℂ ∙ ξ_ℂ).starProjection` is an orthogonal
  projection (`isSelfAdjoint_starProjection`), and the carrier↔ambient inner bridge is lane 082's
  `Paper3.real_inner_eq_re_complex` / `Paper3.realSobolev_inner_eq_ambient`.  The consequence
  `inner_lerayComplement_eq_zero_of_eq_zero` gives `⟪G, (I−P) B⟫ = 0` whenever `(I−P) G = 0`.
* **(S–M) Transverse velocity datum** — `velocity_datum_lerayComplement_eq_zero`: for any order-`m`
  datum `G` of the (divergence-free) velocity slice `u(t,·)`, `Leray.lerayComplement m G = 0`.  Route:
  the lane-117 bootstrap — order 0 via `orderZeroDatum_transverse_of_divergence_free` (velocity
  solenoidal) + `Leray.lerayComplement_eq_zero_of_transverse`, lifted to order `m` through
  `lowerVectorL` / `Leray.lerayComplement_lowerVectorL` / `Leray.isSobolevDatum_lower_iff` and datum
  uniqueness.
* **(S) `hpr`** — `pressure_drop`: `⟪G, P⟫ = 0` in the exact binder shape `inner_energy_assembly`'s
  `hpr` and `momentum_datum`'s `hP`/`hGd` use.  `pin_pressureGradient_datum` (lane 117) pins
  `P = (I−P)ₘ Am` for the momentum-residual datum `Am` (from `smoothL2_momentumResidual_slice`
  through `memHInfty_iff_smoothSquareIntegrableJets`), then step (S) + step (S–M) close it.  The
  final `example` feeds `pressure_drop` into `inner_energy_assembly`'s `hpr` slot verbatim.

The four `L²`/ambient lemmas (`coordinates_inner_bilin`, `complementSymbolComplex_inner_left`,
`lerayComplementL2_inner_left`, `lerayComplementAmbient_inner_left`) are D01/Leray facts proved here
without editing the frozen lane-062/073 modules; flagged for MAINT promotion into
`Section4/D01/LerayMultiplier.lean` / `LerayDatum.lean`.

No `sorry`, no `axiom`; axioms standard (`research/A04/axioms_hpr.lean`).
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.A03 (partialDeriv)
open NSFormalization.Paper3 (RealVectorSobolev real_inner_eq_re_complex realSobolev_inner_eq_ambient)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates coord Product)
open scoped ContDiff RealInnerProductSpace ComplexConjugate

namespace NSFormalization.Section4.A04

/-! ## 0. The `L²` / ambient self-adjointness facts (flagged for MAINT promotion into D01) -/

/-- **Bilinear form of `Leray.coordinates_inner_self`.**  The `q = 2` `coordinates` map preserves the
complex `L²` inner product into the `PiLp 2` datum carrier, for two arguments (the diagonal is
`Leray.coordinates_inner_self`).  Proof mirrors it with the second vector carried through
`L2.inner_def` / `integral_finsetSum` / `coordinates_ae`. -/
theorem coordinates_inner_bilin {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (b b' : Lp (Product ι ℂ) 2 μ) :
    (inner ℂ (WithLp.toLp 2 (coordinates 2 μ b) : Product ι (Lp ℂ 2 μ))
      (WithLp.toLp 2 (coordinates 2 μ b')) : ℂ) = inner ℂ b b' := by
  rw [PiLp.inner_apply]
  have key : ∀ i, (inner ℂ (coordinates 2 μ b i) (coordinates 2 μ b' i) : ℂ)
      = ∫ t, (inner ℂ ((coordinates 2 μ b i) t) ((coordinates 2 μ b' i) t) : ℂ) ∂μ :=
    fun i => L2.inner_def _ _
  simp_rw [key]
  rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun i (_ : i ∈ Finset.univ) =>
        L2.integrable_inner (coordinates 2 μ b i) (coordinates 2 μ b' i)),
    L2.inner_def b b']
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 (fun i => coordinates_ae μ b i),
    ae_all_iff.2 (fun i => coordinates_ae μ b' i)] with t ht ht'
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ht i, ht' i])

/-- **The fibre symbol is self-adjoint.**  `complementSymbolComplex ξ = (ℂ ∙ ξ_ℂ).starProjection`
is an orthogonal projection, hence self-adjoint on the complex fibre `R3C`. -/
theorem complementSymbolComplex_inner_left (ξ : MNS2.R3) (v w : MNS2.R3C) :
    (inner ℂ (complementSymbolComplex ξ v) w : ℂ) = inner ℂ v (complementSymbolComplex ξ w) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_starProjection (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ))) v w

/-- **`lerayComplementL2` is self-adjoint** on the complex `L²` inner product.  Fibrewise from
`complementSymbolComplex_inner_left` through the a.e. action `lerayComplementL2_ae` and
`L2.inner_def`. -/
theorem lerayComplementL2_inner_left (x y : MNS2.R3L2Velocity) :
    (inner ℂ (lerayComplementL2 x) y : ℂ) = inner ℂ x (lerayComplementL2 y) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lerayComplementL2_ae x, lerayComplementL2_ae y] with ξ hx hy
  rw [hx, hy]
  exact complementSymbolComplex_inner_left ξ (x ξ) (y ξ)

/-- **`Leray.lerayComplementAmbient` is self-adjoint** on the complex ambient product inner product.
Conjugate `lerayComplementL2` by the `q = 2` isometry `coordinates`/`assemble`
(`coordinates_inner_bilin`, `coordinates_assemble`, `lerayComplementAmbient_apply`) and use
`lerayComplementL2_inner_left`. -/
theorem lerayComplementAmbient_inner_left
    (X Y : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3))) :
    (inner ℂ (lerayComplementAmbient X) Y : ℂ) = inner ℂ X (lerayComplementAmbient Y) := by
  set x := (WithLp.ofLp X : Fin 3 → Lp ℂ 2 (volume : Measure MNS2.R3)) with hx
  set y := (WithLp.ofLp Y : Fin 3 → Lp ℂ 2 (volume : Measure MNS2.R3)) with hy
  have hXeq : X = WithLp.toLp 2 (coordinates 2 volume (assemble 2 volume x)) := by
    rw [funext fun j => coordinates_assemble volume x j]
  have hYeq : Y = WithLp.toLp 2 (coordinates 2 volume (assemble 2 volume y)) := by
    rw [funext fun j => coordinates_assemble volume y j]
  calc (inner ℂ (lerayComplementAmbient X) Y : ℂ)
      = inner ℂ (WithLp.toLp 2 (coordinates 2 volume (lerayComplementL2 (assemble 2 volume x))))
          (WithLp.toLp 2 (coordinates 2 volume (assemble 2 volume y))) := by
        rw [lerayComplementAmbient_apply, ← hx, hYeq]
    _ = inner ℂ (lerayComplementL2 (assemble 2 volume x)) (assemble 2 volume y) :=
        coordinates_inner_bilin volume _ _
    _ = inner ℂ (assemble 2 volume x) (lerayComplementL2 (assemble 2 volume y)) :=
        lerayComplementL2_inner_left _ _
    _ = inner ℂ (WithLp.toLp 2 (coordinates 2 volume (assemble 2 volume x)))
          (WithLp.toLp 2 (coordinates 2 volume (lerayComplementL2 (assemble 2 volume y)))) :=
        (coordinates_inner_bilin volume _ _).symm
    _ = inner ℂ X (lerayComplementAmbient Y) := by
        rw [lerayComplementAmbient_apply, ← hy, ← hXeq]

/-! ## 1. Step (S): self-adjointness of `Leray.lerayComplement` on the real datum carrier -/

/-- **The datum-carrier real inner product is the real part of the ambient complex one.**  The real
inner product of `RealVectorSobolev s` (via `PiLp` over `Paper3.realSobolevInnerProductSpace`) equals
`Re` of the complex ambient inner product `Product (Fin 3) (Lp ℂ 2)` on the componentwise coercions,
by `Paper3.realSobolev_inner_eq_ambient` (submodule) and `Paper3.real_inner_eq_re_complex`
(`Lp ℂ 2` real↔complex). -/
theorem carrier_inner_eq (s : ℝ) (A B : RealVectorSobolev s) :
    (inner ℝ A B : ℝ) = RCLike.re (inner ℂ
      (WithLp.toLp 2 (fun i => ((A i : FourierData)))
        : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)))
      (WithLp.toLp 2 (fun i => ((B i : FourierData))))) := by
  simp only [PiLp.inner_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realSobolev_inner_eq_ambient, real_inner_eq_re_complex]

/-- **Step (S) — self-adjointness of the Leray-complement multiplier.**
`⟪(I−P)ₛ A, B⟫ = ⟪A, (I−P)ₛ B⟫` on the real datum carrier `RealVectorSobolev s`.  `lerayComplement s`
is the restriction of `lerayComplementAmbient` (`lerayComplement_toAmbient`), which is complex
self-adjoint (`lerayComplementAmbient_inner_left`); the carrier real inner product is the real part
of the ambient complex one (`carrier_inner_eq`). -/
theorem lerayComplement_selfAdjoint (s : ℝ) (A B : RealVectorSobolev s) :
    (inner ℝ (lerayComplement s A) B : ℝ) = (inner ℝ A (lerayComplement s B) : ℝ) := by
  rw [carrier_inner_eq s (lerayComplement s A) B, carrier_inner_eq s A (lerayComplement s B),
    lerayComplement_toAmbient, lerayComplement_toAmbient, lerayComplementAmbient_inner_left]

/-- **Step (S), consequence.**  If `(I−P)ₛ G = 0` then `⟪G, (I−P)ₛ B⟫ = 0` for every `B`.  Move the
self-adjoint operator onto `G` and use `(I−P)ₛ G = 0`. -/
theorem inner_lerayComplement_eq_zero_of_eq_zero (s : ℝ) (G B : RealVectorSobolev s)
    (hG : lerayComplement s G = 0) :
    (inner ℝ G (lerayComplement s B) : ℝ) = 0 := by
  rw [← lerayComplement_selfAdjoint s G B, hG, inner_zero_left]

/-! ## 2. Step (S–M): the velocity datum is transverse at every order -/

/-- The zero field has the zero datum at every order. -/
theorem isSobolevDatum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ
  simp

/-- **Step (S–M) — the order-`m` velocity datum is Leray-transverse.**  For a classical solution `u`,
interior time `t`, and any order-`m` datum `G` of the (pointwise divergence-free) velocity slice
`u(t,·)`, `Leray.lerayComplement m G = 0`.  Order 0 is
`orderZeroDatum_transverse_of_divergence_free` (solenoidality of `u`) +
`Leray.lerayComplement_eq_zero_of_transverse`; the lift to order `m` uses `lowerVectorL`, the
commutation `Leray.lerayComplement_lowerVectorL`, datum uniqueness and `Leray.isSobolevDatum_lower_iff`. -/
theorem velocity_datum_lerayComplement_eq_zero
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G : RealVectorSobolev (m : ℝ)}
    (hG : IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) G) :
    lerayComplement (m : ℝ) G = 0 := by
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
  have hsmooth : ContDiff ℝ ∞ (fun x : Space => u.velocity (t, x)) :=
    contDiff_slice u.velocity_smooth ht'
  have hz : MemLp (fun x : Space => u.velocity (t, x)) 2 volume :=
    memLp_of_isSobolevDatum hsmooth hG
  have hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j (fun y : Space => u.velocity (t, y)) x j = 0 :=
    fun x => u.divergence t ht' x
  have h0m : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc0 : lerayComplement 0 (orderZeroDatum hz) = 0 :=
    lerayComplement_eq_zero_of_transverse 0 _
      (orderZeroDatum_transverse_of_divergence_free hz hsmooth hdiv)
  have hlow : lowerVectorL (m : ℝ) 0 h0m G = orderZeroDatum hz :=
    isSobolevDatum_unique (isSobolevDatum_lower h0m hG) (isSobolevDatum_orderZeroDatum hz)
  have hkey : lowerVectorL (m : ℝ) 0 h0m (lerayComplement (m : ℝ) G) = 0 := by
    rw [← lerayComplement_lowerVectorL, hlow, hc0]
  have hzero_m :
      IsSobolevDatum (m : ℝ) (fun _ : Space => (0 : Space)) (lerayComplement (m : ℝ) G) := by
    refine (isSobolevDatum_lower_iff h0m).mp ?_
    rw [hkey]
    exact isSobolevDatum_zero 0
  exact isSobolevDatum_unique hzero_m (isSobolevDatum_zero (m : ℝ))

/-! ## 3. Step (S): the pressure drop `hpr` in the consumer's shape -/

/-- **Step (S) — the pressure drop (the `hpr` of `inner_energy_assembly`).**  For a classical
solution `u`, admissible force `f`, interior time `t`, an order-`m` datum `G` of `u(t,·)` and an
order-`m` datum `P` of `∇p(t,·)`, the pressure pairing vanishes: `⟪G, P⟫ = 0`.  Binder shapes match
`momentum_datum`'s `hGd`/`hP` and `inner_energy_assembly`'s `hpr` (see the `example` below).  Route:
`pin_pressureGradient_datum` (lane 117) pins `P = (I−P)ₘ Am` for the order-`m` momentum-residual
datum `Am`, and steps (S)+(S–M) give `⟪G, (I−P)ₘ Am⟫ = 0`. -/
theorem pressure_drop
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G P : RealVectorSobolev (m : ℝ)}
    (hG : IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) G)
    (hP : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    ⟪G, P⟫ = 0 := by
  obtain ⟨_, hjets⟩ :=
    memHInfty_iff_smoothSquareIntegrableJets.mpr (smoothL2_momentumResidual_slice u hf ht)
  obtain ⟨Am, hAm⟩ := hjets m
  have hPpin : P = lerayComplement (m : ℝ) Am := pin_pressureGradient_datum u hf ht hAm hP
  have hGzero : lerayComplement (m : ℝ) G = 0 := velocity_datum_lerayComplement_eq_zero u ht hG
  rw [hPpin]
  exact inner_lerayComplement_eq_zero_of_eq_zero (m : ℝ) G Am hGzero

/-- **Fit check.**  `pressure_drop` fills the `hpr` slot of `A04.inner_energy_assembly`
(`Section4/A04/HighEnergy.lean`) verbatim at `E = RealVectorSobolev (m:ℝ)`, delivering the eq:Rhigh
energy inequality once the other datum-form inputs (`hd`, `hmom`, `hlap`, `hnl`, `hG`, `hF`) are in
hand. -/
example
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {m : ℕ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {G Gt N P L Fdatum : RealVectorSobolev (m : ℝ)} {grad NLbound uNorm fNorm d : ℝ}
    (hν : 0 ≤ ν) (hd : d = 2 * ⟪G, Gt⟫) (hmom : Gt = ν • L - N - P + Fdatum)
    (hlap : ⟪G, L⟫ ≤ -grad ^ 2) (hnl : -⟪G, N⟫ ≤ NLbound)
    (hGn : ‖G‖ = uNorm) (hFn : ‖Fdatum‖ = fNorm)
    (hGd : IsSobolevDatum (m : ℝ) (fun x : Space => u.velocity (t, x)) G)
    (hPd : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    (1 / 2) * d + ν * grad ^ 2 ≤ NLbound + fNorm * uNorm :=
  inner_energy_assembly hν hd hmom hlap (pressure_drop u hf ht hGd hPd) hnl hGn hFn

end NSFormalization.Section4.A04
