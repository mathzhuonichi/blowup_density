import NSFormalization.Section4.D01.SmoothDatum
import NSFormalization.Section4.I03.Angular
import NSFormalization.Source.FourierPhysicalJets

/-!
# The force class `F_R` is closed under adding a compact smooth force (unit D01)

`research/section4/STATEMENTS.md:270` lists, among the D01 obligations,
"`⟪D01:Cc_infty⟫` on `R³ × (0,∞)` and the fact that `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`".
`paper/sections/04-whole-space.tex:51` is where Theorem 4.2 (`thm:Rinsert`) uses it:
"Both force corrections are globally smooth and spacetime compact, including across `T`,
so their sum preserves membership in `F_R`", the sum being the third display
`g_ε = g + H_ε + F_ε` of `04-whole-space.tex:48`.  `04-whole-space.tex:198`
(`cor:Rclasses`) uses the same closure again.

This module proves it, in the exact spelling of `verification/Contracts/V1/Data.lean`:

* `memForceR_of_memForceCompact` — `F_c ⊆ F_R` (`Data.lean:559` into `Data.lean:544`);
* `memForceR_add` — `F_R` is closed under addition;
* `memForceR_add_compact` — the composite `MemForceR g → MemForceCompact h → MemForceR (g + h)`;
* `memForceR_of_force_formula` and `memForceR_of_compact_difference` — the two shapes in which
  `Contracts.V1.InsertionFamily` hands the inserted force to a consumer (`force_formula` and
  `forceDifference_compact`).

## What was missing, and what is new here

Nothing in the project produced a datum path that is **smooth in time**.
`Section4/I03/Angular.lean` builds `angularPath`, proves `angularPath_pairing` (the pairing
shape of `Data.IsSobolevDatum`, `Data.lean:160`) and `memLp_angularPath`, but stops short of
the `ContDiffOn ℝ ∞ G futureTimes` clause of `Data.MemForceR` (`Data.lean:548`); lane 027
recorded exactly this (`research/R42/COMPARISON.md` §4.3) and lane 018 recorded it as
`research/B01/REVIEW.md` issue 3.  Section 1 below supplies it: `Paper3` already has genuine
Banach-valued smoothness of the *cycles*-convention scalar trajectory
(`Paper3.contDiff_compactSobolevTimeSlice`, `Paper3/CompactSobolevTime.lean:18`), and the two
remaining steps — the real-part projection `Paper3.realProjectionTo`
(`Paper3/RealPositiveDensity.lean:21`) and the convention change
`Paper3.cyclesToAngularRealVector` (`Paper3/AngularRealVectorBochner.lean:15`) — are a
continuous linear map and a continuous linear equivalence, so `ContDiff` transports through
them by composition.  That is the transport `research/B01/COMPARISON.md` unit 5 asks for.

The second missing piece was additivity of `Data.IsSobolevPath` (`Data.lean:174`).  The datum
side is linear, but the physical side of `IsSobolevDatum` is a *Bochner* integral
`∫ x, ψ x * (z x i : ℂ)`, which Mathlib totalizes to `0` on a non-integrable integrand; so
`∫ ψ·(z + w) = ∫ ψ·z + ∫ ψ·w` is **not** formal and needs each pairing to be integrable.  This
is exactly the "totalization caveat" of the `IsSobolevDatum` docstring (`Data.lean:148-155`),
which observes that the `m = 0` clause of `MemForceR` puts the slice in `L²`, "where Schwartz
times `L²` is `L¹`".  Section 4 turns that observation into a proof:
`Source.FourierPhysicalJets.physicalLp_ae` (`:28`) inverts an order-`s` cycles datum of a
*continuous* field into its physical `L²` class, `Paper3.cyclesToAngular`
(`Paper3/AngularTameProduct.lean:11`) converts the manuscript's angular datum into a cycles one
without changing the realized distribution, and the resulting `MemLp _ 2 volume` of each
component, against `SchwartzMap.memLp`, gives the integrability.  So `MemForceR` is closed
under addition with no side hypothesis.

*Attribution.*  The order-zero route of §4 is the `j = 0` specialization of lane 025's
`NSFormalization.Section4.D01.DatumToJets` (`memLp_of_isSobolevDatum`), which was in review in
a separate worktree and could not be imported.  Only the scalar order-zero case is
reconstructed here (`cyclesComponent`, `compactRep_cyclesComponent`,
`memLp_component_of_isSobolevDatum`), through `physicalLp_ae` rather than through the
`physicalJetLp` tensor reassembly that the general jet statement needs.  When `DatumToJets`
lands, §4 can be deleted in favour of its `memLp_of_isSobolevDatum`; the names do not collide.

## Restated predicates

`formalization/` is an upstream Lake package of `verification/` and cannot import
`Contracts.*`.  `IsSobolevPath`, `MemForceR`, `MemForceCompact`, `AgreesOnFuture`,
`futureTimes` and `forceTimeMeasure` below are therefore restated **verbatim** from
`Contracts/V1/Data.lean:174,544,559,128,113,118`, exactly as `SmoothDatum.lean` restates
`IsSobolevDatum` (`Data.lean:160`) and `sobolevENorm` (`Data.lean:189`).  `SpaceTimeField` is an
`abbrev` for `VelocityField` (`Data.lean:104`) and `SpatialField` for `Space → Space`
(`Data.lean:99`), so the types agree on the nose and the agreement of each predicate with its
contract counterpart is `Iff.rfl`.  The checks are recorded in
`research/D01/ATTEMPTS_FORCECLASS.md`.

## Conventions

The Fourier normalization is the manuscript's angular one,
`ẑ(ξ) = (2π)^{-3/2} ∫ e^{-i x·ξ} z(x) dx` (`paper/sections/01-introduction.tex:91,94`), carried
by `Paper3.angularRealization`; reality is the conjugate reflection `F(-ξ) = conj (F ξ)` of
`02-preliminaries.tex:72`; the three components are summed with the Euclidean `PiLp 2` norm of
`01-introduction.tex:103`, i.e. `Paper3.RealVectorSobolev`.  Time-integrability is on
`(0,∞)`, `Paper3.positiveTimeMeasure` (`01-introduction.tex:140`), while smoothness in time is
on the closed half line `Ici 0` (`02-preliminaries.tex:22`, "with one-sided time derivatives at
zero").  No statement below uses a norm, so no `(2π)` constant appears anywhere in this file.
-/

noncomputable section

namespace NSFormalization.Section4.D01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ContDiff

/-! ## 1. Time regularity of the angular datum path

The clause of `Data.MemForceR` that nothing in the project constructed
(`research/R42/COMPARISON.md` §4.3): the order-`m` datum path of a smooth compactly supported
force is `C^∞` **into `H^m`**, not merely `MemLp`.  `Paper3.contDiff_compactSobolevTimeSlice`
(`Paper3/CompactSobolevTime.lean:18`) is the analytic content; everything here is transport
along bounded linear maps. -/

/-- The real-part projection is a continuous linear map
(`Paper3.realProjectionTo`, `Paper3/RealPositiveDensity.lean:21`), so the real-subspace
trajectory of a compact smooth scalar is as smooth in time as the complex one. -/
theorem contDiff_realCompactSobolevTimeSlice (s : ℝ) (F : ℝ × Space → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ContDiff ℝ ∞ (realCompactSobolevTimeSlice s F hF hc) :=
  (realProjectionTo s).contDiff.comp (contDiff_compactSobolevTimeSlice s _ _)

/-- Smoothness into the Euclidean `PiLp 2` product is smoothness of the three components
(`Mathlib.Analysis.Calculus.ContDiff.WithLp.contDiff_piLp`). -/
theorem contDiff_realVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    ContDiff ℝ ∞ (realVectorSlice s F hF hc) :=
  (contDiff_piLp 2).mpr fun i => contDiff_realCompactSobolevTimeSlice s (F i) (hF i) (hc i)

/-- The cycles-to-angular convention change is a continuous linear *equivalence*
(`Paper3.cyclesToAngularRealVector`, `Paper3/AngularRealVectorBochner.lean:15`), so it carries
time regularity both ways; only `→` is used. -/
theorem contDiff_angularRealVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    ContDiff ℝ ∞ (angularRealVectorSlice s F hF hc) :=
  (cyclesToAngularRealVector s).toContinuousLinearMap.contDiff.comp
    (contDiff_realVectorSlice s F hF hc)

/-- **The missing ingredient.**  `Section4.I03.angularPath` — the manuscript-normalized
order-`s` datum path of a smooth compactly supported physical force — is `C^∞` in time, on all
of `ℝ`, hence a fortiori `ContDiffOn ℝ ∞ · futureTimes` as `Data.MemForceR` (`Data.lean:548`)
demands.  `research/B01/COMPARISON.md` unit 5 and `research/B01/REVIEW.md` issue 3 record this
as the transport that was absent. -/
theorem contDiff_angularPath (s : ℝ) (F : VelocityField) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (I03.angularPath s F hF hc) :=
  contDiff_angularRealVectorSlice s _ _ _

/-! ## 2. The contract predicates, restated

Verbatim transcriptions of `verification/Contracts/V1/Data.lean`; see the module docstring. -/

/-- `Contracts.V1.Data.futureTimes` (`Data.lean:113`), restated: the closed half line `[0,∞)` of
`02-preliminaries.tex:22`, on which force smoothness is imposed. -/
abbrev futureTimes : Set ℝ := Ici (0 : ℝ)

/-- `Contracts.V1.Data.forceTimeMeasure` (`Data.lean:118`), restated: `volume.restrict (Ioi 0)`,
the `(0,∞)` of `01-introduction.tex:140`. -/
abbrev forceTimeMeasure : Measure ℝ := positiveTimeMeasure

/-- `Contracts.V1.Data.IsSobolevPath` (`Data.lean:174`), restated: `G` is the order-`s` angular
datum trajectory of `f` at every nonnegative time.  `IsSobolevDatum` is lane 020's restatement
in `SmoothDatum.lean`. -/
def IsSobolevPath (s : ℝ) (f : VelocityField) (G : ℝ → RealVectorSobolev s) : Prop :=
  ∀ t : ℝ, 0 ≤ t → IsSobolevDatum s (fun x => f (t, x)) (G t)

/-- `Contracts.V1.Data.MemForceR` (`Data.lean:544`), restated: `02-preliminaries.tex:17`
eq:Rclasses, `F_R = {f ∈ C^∞([0,∞);H^∞) : ‖f‖_{L¹_tH^m_x} + ‖f‖_{L²_tH^m_x} < ∞` for every
integer `m ≥ 0}`. -/
def MemForceR (f : VelocityField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧
      ContDiffOn ℝ ∞ G futureTimes ∧
      MemLp G 1 forceTimeMeasure ∧
      MemLp G 2 forceTimeMeasure

/-- `Contracts.V1.Data.MemForceCompact` (`Data.lean:559`), restated: `04-whole-space.tex:185`,
`F_c = C_c^∞(R³ × (0,∞);R³)`, as global smoothness plus the pinned upstream
`NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport`. -/
def MemForceCompact (f : VelocityField) : Prop :=
  ContDiff ℝ ∞ f ∧ NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f

/-- `Contracts.V1.Data.AgreesOnFuture` (`Data.lean:128`), restated: two spacetime fields are the
same manuscript force exactly when they agree at nonnegative times
(`02-preliminaries.tex:24`). -/
def AgreesOnFuture (f g : VelocityField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, f (t, x) = g (t, x)

/-! ## 3. Goal 1: `F_c ⊆ F_R`

`04-whole-space.tex:183`, "the following two subclasses of `F_R`".  Everything but the time
regularity was already available in `Section4/I03/Angular.lean`. -/

/-- **`F_c ⊆ F_R`.**  A globally smooth force with compact support in `t > 0` lies in the
manuscript's `F_R`: its order-`m` angular datum path is `I03.angularPath`, which pairs as
`Data.IsSobolevDatum` demands (`I03.angularPath_pairing`), is `C^∞` in time (§1), and is
Bochner `L^q` on `(0,∞)` for every `q` because it is continuous with compact time support
(`I03.memLp_angularPath`).  Smoothness of the physical field on `futureDomain` is the global
`ContDiff` restricted. -/
theorem memForceR_of_memForceCompact {f : VelocityField} (h : MemForceCompact f) :
    MemForceR f := by
  obtain ⟨hf, hcs⟩ := h
  refine ⟨hf.contDiffOn, fun m => ⟨I03.angularPath (m : ℝ) f hf hcs.1, ?_, ?_, ?_, ?_⟩⟩
  · exact fun t _ i ψ => I03.angularPath_pairing (m : ℝ) f hf hcs.1 t i ψ
  · exact (contDiff_angularPath (m : ℝ) f hf hcs.1).contDiffOn
  · exact I03.memLp_angularPath (m : ℝ) f hf hcs.1 1
  · exact I03.memLp_angularPath (m : ℝ) f hf hcs.1 2

/-! ## 4. Schwartz pairability and the order-zero physical `L²` slice

The side condition that makes the *physical* half of `Data.IsSobolevDatum` additive.  See the
module docstring for why it cannot be dispensed with, and for the attribution to lane 025. -/

/-- The physical field of a datum pairs integrably with every Schwartz test, in every
component.  This is precisely what `integral_add` needs in order to split the right-hand side
of `Data.IsSobolevDatum` (`Data.lean:160`) over a sum of fields; the `IsSobolevDatum` docstring
(`Data.lean:148-155`) calls its failure the totalization caveat. -/
def SchwartzPairable (z : Space → Space) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    Integrable (fun x : Space => ψ x * ((z x i : ℝ) : ℂ)) volume

/-- "Schwartz times `L²` is `L¹`" (`Data.lean:153`): Hölder with `1/2 + 1/2 = 1`, on
`SchwartzMap.memLp`. -/
theorem schwartzPairable_of_memLp {z : Space → Space}
    (h : ∀ i : Fin 3, MemLp (fun x : Space => ((z x i : ℝ) : ℂ)) 2 volume) :
    SchwartzPairable z := fun i ψ => MemLp.integrable_mul (ψ.memLp 2 volume) (h i)

/-- One component of the manuscript's angular datum, read in the cycles convention that
`Source.FourierPhysicalJets` inverts.  `Paper3.cyclesToAngular`
(`Paper3/AngularTameProduct.lean:11`) is a linear homeomorphism, so nothing is lost; no norm is
taken here, so the `(2π)^{|s|}` of `cyclesToAngular_symm_norm_le` never appears. -/
def cyclesComponent (s : ℝ) (A : RealVectorSobolev s) (i : Fin 3) : SobolevHilbert s :=
  (cyclesToAngular s).symm ((A i : FourierData))

/-- `Data.IsSobolevDatum` pairs against **every** Schwartz test, which is more than
`FourierPhysicalJets.CompactRep` (`:14`) asks; the two realizations agree by
`Paper3.angularRealization_eq_cycles` (`Paper3/AngularTameProduct.lean:30`). -/
theorem compactRep_cyclesComponent {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) (i : Fin 3) :
    FourierPhysicalJets.CompactRep s (cyclesComponent s A i) (fun x => ((z x i : ℝ) : ℂ)) := by
  intro ψ _
  show sobolevRealization s ((cyclesToAngular s).symm ((A i : FourierData))) ψ = _
  rw [← angularRealization_eq_cycles, hA i ψ]
  simp only [smul_eq_mul]

/-- **Order-zero datum ⟹ physical `L²`.**  A *continuous* field with an angular Sobolev datum
at a nonnegative order has square-integrable components.  This is the `j = 0` case of lane
025's `DatumToJets.memLp_of_isSobolevDatum`, reconstructed through the scalar
`FourierPhysicalJets.physicalLp_ae` (`:28`) rather than through the `physicalJetLp` tensor
reassembly, because only order zero is needed and only continuity — not smoothness — is
available for free from `ContDiffOn ℝ ∞ f futureDomain` at `t = 0`. -/
theorem memLp_component_of_isSobolevDatum {s : ℝ} (hs : 0 ≤ s) {z : Space → Space}
    (hz : Continuous z) {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) (i : Fin 3) :
    MemLp (fun x : Space => ((z x i : ℝ) : ℂ)) 2 volume := by
  have hc : Continuous (fun x : Space => ((z x i : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hz)
  exact (memLp_congr_ae (FourierPhysicalJets.physicalLp_ae hs hc
    (compactRep_cyclesComponent hA i))).mp (Lp.memLp _)

/-- Having *any* datum at a nonnegative order makes a continuous field Schwartz-pairable. -/
theorem schwartzPairable_of_isSobolevDatum {s : ℝ} (hs : 0 ≤ s) {z : Space → Space}
    (hz : Continuous z) {A : RealVectorSobolev s} (hA : IsSobolevDatum s z A) :
    SchwartzPairable z :=
  schwartzPairable_of_memLp fun i => memLp_component_of_isSobolevDatum hs hz hA i

/-! ## 5. Additivity and uniqueness of Sobolev data -/

/-- **The datum of a sum is the sum of the data.**  `Paper3.angularRealization` is a continuous
linear map (`Paper3/AngularFourierDilation.lean:176`), so the distributional side is additive
outright; the physical side is a Bochner integral and splits exactly when both pairings are
integrable, which is the `SchwartzPairable` hypothesis. -/
theorem isSobolevDatum_add {s : ℝ} {z w : Space → Space} {A B : RealVectorSobolev s}
    (hz : SchwartzPairable z) (hw : SchwartzPairable w)
    (hA : IsSobolevDatum s z A) (hB : IsSobolevDatum s w B) :
    IsSobolevDatum s (z + w) (A + B) := by
  intro i ψ
  have hcoe : ((((A + B) i : RealSobolevHilbert s)) : FourierData)
      = ((A i : RealSobolevHilbert s) : FourierData)
        + ((B i : RealSobolevHilbert s) : FourierData) := rfl
  rw [hcoe, map_add]
  show angularRealization s ((A i : FourierData)) ψ
      + angularRealization s ((B i : FourierData)) ψ = _
  rw [hA i ψ, hB i ψ]
  have hsplit : (fun x : Space => ψ x * (((z + w) x i : ℝ) : ℂ))
      = fun x : Space => ψ x * ((z x i : ℝ) : ℂ) + ψ x * ((w x i : ℝ) : ℂ) := by
    funext x
    show ψ x * (((z x + w x) i : ℝ) : ℂ) = _
    rw [PiLp.add_apply]
    push_cast
    ring
  rw [hsplit, integral_add (hz i ψ) (hw i ψ)]

/-- **Uniqueness of the datum**, the lemma the `IsSobolevDatum` docstring (`Data.lean:145`)
promises: "the datum is unique when it exists, because `angularRealization` is injective"
(`Paper3.angularRealization_injective`, `Paper3/AngularFourierDilation.lean:203`).  Hence the
datum of `z + w` really *is* `A + B` and not merely *a* datum of it. -/
theorem isSobolevDatum_unique {s : ℝ} {z : Space → Space} {A B : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) (hB : IsSobolevDatum s z B) : A = B := by
  have h : ∀ i : Fin 3, ((A i : RealSobolevHilbert s) : FourierData)
      = ((B i : RealSobolevHilbert s) : FourierData) := by
    intro i
    refine angularRealization_injective s ?_
    ext ψ
    rw [hA i ψ, hB i ψ]
  exact PiLp.ext fun i => Subtype.ext (h i)

/-! ## 6. Goal 2: `F_R` is closed under addition -/

/-- A spatial slice at a nonnegative time of a field smooth on `futureDomain = Ici 0 ×ˢ univ`
is globally smooth: `x ↦ (t, x)` is smooth with range inside the set.  Needed at `t = 0` too,
where the one-sided time derivative of `02-preliminaries.tex:22` lives. -/
theorem contDiff_futureSlice {f : VelocityField} (hf : ContDiffOn ℝ ∞ f futureDomain)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x : Space => f (t, x)) :=
  hf.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)

/-- Every slice of a force in `F_R` is Schwartz-pairable: the `m = 0` clause of `MemForceR`
gives an order-`0` datum, and `ContDiffOn ℝ ∞ f futureDomain` makes the slice continuous.  This
is the argument the `IsSobolevDatum` totalization caveat (`Data.lean:153`) sketches, made
explicit. -/
theorem schwartzPairable_slice_of_memForceR {f : VelocityField} (hf : MemForceR f)
    {t : ℝ} (ht : 0 ≤ t) : SchwartzPairable (fun x : Space => f (t, x)) := by
  obtain ⟨hsmooth, hdata⟩ := hf
  obtain ⟨G, hpath, -, -, -⟩ := hdata 0
  refine schwartzPairable_of_isSobolevDatum (s := ((0 : ℕ) : ℝ)) (by norm_num)
    (contDiff_futureSlice hsmooth ht).continuous (hpath t ht)

/-- **Additivity of `Data.IsSobolevPath`** (`Data.lean:174`), the lemma
`research/R42/COMPARISON.md` §4.3 reports missing: "not the additivity
`IsSobolevPath m g G₁ → IsSobolevPath m φ G₂ → IsSobolevPath m (g+φ) (G₁+G₂)` needed to add it
to the reference force". -/
theorem isSobolevPath_add {s : ℝ} {f g : VelocityField} {G H : ℝ → RealVectorSobolev s}
    (hf : ∀ t : ℝ, 0 ≤ t → SchwartzPairable (fun x : Space => f (t, x)))
    (hg : ∀ t : ℝ, 0 ≤ t → SchwartzPairable (fun x : Space => g (t, x)))
    (hG : IsSobolevPath s f G) (hH : IsSobolevPath s g H) :
    IsSobolevPath s (f + g) (G + H) := fun t ht =>
  isSobolevDatum_add (hf t ht) (hg t ht) (hG t ht) (hH t ht)

/-- **`F_R` is a subgroup under addition**, the half of `04-whole-space.tex:51` that does not
mention compact support.  No side hypothesis: pairability of each slice comes from the class
itself (`schwartzPairable_slice_of_memForceR`). -/
theorem memForceR_add {f g : VelocityField} (hf : MemForceR f) (hg : MemForceR g) :
    MemForceR (f + g) := by
  refine ⟨hf.1.add hg.1, fun m => ?_⟩
  obtain ⟨G, hGp, hGc, hG1, hG2⟩ := hf.2 m
  obtain ⟨H, hHp, hHc, hH1, hH2⟩ := hg.2 m
  exact ⟨G + H,
    isSobolevPath_add (fun t ht => schwartzPairable_slice_of_memForceR hf ht)
      (fun t ht => schwartzPairable_slice_of_memForceR hg ht) hGp hHp,
    hGc.add hHc, hG1.add hH1, hG2.add hH2⟩

/-- **`F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`**, the D01 obligation of
`research/section4/STATEMENTS.md:270` and the sentence
`04-whole-space.tex:51` "Both force corrections are globally smooth and spacetime compact,
including across `T`, so their sum preserves membership in `F_R`". -/
theorem memForceR_add_compact {g h : VelocityField} (hg : MemForceR g) (hh : MemForceCompact h) :
    MemForceR (g + h) := memForceR_add hg (memForceR_of_memForceCompact hh)

/-! ## 7. `F_c` closure and the `AgreesOnFuture` convention -/

/-- `MemForceCompact` from the three facts `I02`/`I03` actually state about `H_ε` and `F_ε`:
smoothness, compact support, and support in `t > 0`
(`Contracts.V1.Correction.force_smooth`, `force_compactSupport`, `force_positive_time`). -/
theorem memForceCompact_of_smooth_support {f : VelocityField} (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : ∀ z ∈ tsupport f, 0 < z.1) : MemForceCompact f :=
  ⟨hs, hc, fun z hz => ⟨hp z hz, mem_univ _⟩⟩

/-- `F_c` is closed under addition (`04-whole-space.tex:185`): `tsupport (f + g)` is inside
`tsupport f ∪ tsupport g`, both of which are compact and inside `t > 0`. -/
theorem memForceCompact_add {f g : VelocityField} (hf : MemForceCompact f)
    (hg : MemForceCompact g) : MemForceCompact (f + g) := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, ?_⟩
  have hsub : tsupport (f + g) ⊆ tsupport f ∪ tsupport g := by
    refine (closure_mono (Function.support_add f g)).trans ?_
    rw [closure_union]
    exact subset_rfl
  exact hsub.trans (union_subset hf.2.2 hg.2.2)

/-- `F_R` is extensional for `Data.AgreesOnFuture` (`Data.lean:128`), as that docstring intends:
`ContDiffOn` on `futureDomain` and `IsSobolevPath` both read `f` only at `t ≥ 0`. -/
theorem memForceR_congr {f g : VelocityField} (h : AgreesOnFuture f g) (hf : MemForceR f) :
    MemForceR g := by
  refine ⟨hf.1.congr fun z hz => (h z.1 hz.1 z.2).symm, fun m => ?_⟩
  obtain ⟨G, hGp, hGc, hG1, hG2⟩ := hf.2 m
  refine ⟨G, fun t ht => ?_, hGc, hG1, hG2⟩
  have hslice : (fun x : Space => g (t, x)) = fun x : Space => f (t, x) :=
    funext fun x => (h t ht x).symm
  rw [hslice]
  exact hGp t ht

/-- The `AgreesOnFuture` equivalence, in both directions. -/
theorem memForceR_of_agreesOnFuture {f g : VelocityField} (h : AgreesOnFuture f g) :
    MemForceR f ↔ MemForceR g :=
  ⟨memForceR_congr h, memForceR_congr fun t ht x => (h t ht x).symm⟩

/-! ## 8. Goal 3: the inserted force `g_ε = g + H_ε + F_ε` of Theorem 4.2

The two shapes in which `Contracts.V1.InsertionFamily` (the `R42` contract) presents the
inserted force.  Both are stated as lemmas over the contract-level facts, so that the binding
module in `verification/Bindings` can apply them directly without this package seeing
`Contracts.*`. -/

/-- Pointwise equality of forces transports `MemForceR`: a special case of
`memForceR_congr`, convenient when a contract states a *formula* rather than a function
equation. -/
theorem memForceR_of_eq {f g : VelocityField} (hf : MemForceR f) (h : ∀ z : SpaceTime, g z = f z) :
    MemForceR g := memForceR_congr (fun t _ x => (h (t, x)).symm) hf

/-- **`g_ε ∈ F_R` from `forceDifference_compact`.**  `InsertionFamilyAPI.forceDifference_compact`
states `Data.MemForceCompact (fun z => force ε z - g z)` for every `ε ∈ Ioc 0 ε₀`; together with
`hg : MemForceR g` (the reference force of `04-whole-space.tex:32`) this gives
`04-whole-space.tex:33`'s "there are `g_ε ∈ F_R`". -/
theorem memForceR_of_compact_difference {g gε : VelocityField} (hg : MemForceR g)
    (hd : MemForceCompact (fun z => gε z - g z)) : MemForceR gε :=
  memForceR_of_eq (memForceR_add_compact hg hd) fun z => by
    show gε z = g z + (gε z - g z)
    abel

/-- **`g_ε ∈ F_R` from `force_formula`.**  `InsertionFamilyAPI.force_formula` is the third
display of `04-whole-space.tex:48`, `g_ε = g + H_ε + F_ε`, with `H_ε` the correction force of
`I02` (`CorrectionAPI.forceCorrection`) and `F_ε` the rescaled packet force of `I03`
(`ScalingAPI.F`).  Each of the two corrections is in `F_c` — that is
`04-whole-space.tex:51`, "Both force corrections are globally smooth and spacetime compact,
including across `T`".

*Which route R42 can use today.*  `hH` is immediate:
`memForceCompact_of_smooth_support` consumes `CorrectionAPI.force_smooth`,
`force_compactSupport` and `force_positive_time` (`Contracts/V1/Correction.lean:426,429,440`)
character for character.  `hF` is **not** currently available: it asks for
`MemForceCompact (ScalingAPI.F ε)`, and `ScalingAPI.F ε = scaledForce P.force x₀ T ε
= dilateField ((ε⁻¹)^3) ((ε⁻¹)^2) ε⁻¹ (T - ε^2) x₀ P.force`
(`Contracts/V1/Scaling.lean:115,448`), while `PacketAPI.force_smooth` and
`PacketAPI.force_support` (`Contracts/V1/Packet.lean:209,214`) are stated for the **unscaled**
packet force only and nothing in the tree transports them through `dilateField`.  So
`memForceR_of_compact_difference` — fed by the single contract field
`InsertionFamilyAPI.forceDifference_compact`, which needs nothing extra — is the route R42 can
discharge; this one becomes usable once a `MemForceCompact (scaledForce …)` lemma exists (a
small follow-up, since `dilateField` is a diffeomorphic reparametrization with a compact-support
image). -/
theorem memForceR_of_force_formula {g H F gε : VelocityField} (hg : MemForceR g)
    (hH : MemForceCompact H) (hF : MemForceCompact F)
    (hform : ∀ z : SpaceTime, gε z = g z + H z + F z) : MemForceR gε :=
  memForceR_of_eq
    (memForceR_add_compact (memForceR_add_compact hg hH) hF)
    fun z => hform z

end NSFormalization.Section4.D01
