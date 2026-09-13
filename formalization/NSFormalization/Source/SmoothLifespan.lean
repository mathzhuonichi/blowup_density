import NSFormalization.Source.LocalApproximatingInsertion
import NavierStokes.R3.CompactComparisonBounds

/-!
# An existence-based lifespan for actual classical flows

The lifespan is the supremum of actual solution horizons. Its definition and
the elementary alternative below require no local existence theorem. This
module explicitly uses the class of smooth finite-energy flows with bounded
velocity and first spatial derivative on every compact time interval. The
identification with the manuscripts' continuous H-infinity solution class is
a separate analytic obligation, not an implicit premise of these definitions.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Topology
namespace NSFormalization.Source.SmoothLifespan
open NavierStokes.ProblemStatement
open NavierStokesR3.ProblemStatement (UniformFiniteEnergy)

/-- Actual smooth solution fields on a finite horizon. All bounds are local
in time; no existence, uniqueness, or continuation conclusion is a field. -/
structure Flow (ν : ℝ) (a : Space → Space) (f : VelocityField) (S : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  horizon_pos : 0 < S
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ univ)
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) S ×ˢ univ)
  initial : ∀ x, velocity (0, x) = a x
  divergence : ∀ t ∈ Ico (0 : ℝ) S, ∀ x, spatialDivergence velocity t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν velocity pressure t x = f (t, x)
  energy : ∀ b ∈ Ico (0 : ℝ) S, UniformFiniteEnergy (Icc (0 : ℝ) b) velocity
  velocity_bound : ∀ b ∈ Ico (0 : ℝ) S, ∃ B : ℝ, 0 ≤ B ∧
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x, ‖velocity (t, x)‖ ≤ B
  derivative_bound : ∀ b ∈ Ico (0 : ℝ) S, ∃ G : ℝ, 0 ≤ G ∧
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x, ‖spatialDerivative velocity t x‖ ≤ G

/-- Supremum of horizons for which the displayed actual flow exists. The
empty supremum is zero. This is not a chosen maximal solution. -/
def lifespan (ν : ℝ) (a : Space → Space) (f : VelocityField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ (_ : Nonempty (Flow ν a f S)), ENNReal.ofReal S

theorem horizon_le_lifespan {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) : ENNReal.ofReal S ≤ lifespan ν a f :=
  le_iSup_of_le S (le_iSup_of_le ⟨U⟩ le_rfl)

theorem lifespan_le_iff {ν T : ℝ} (hT : 0 ≤ T) (a : Space → Space)
    (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ↔ ∀ S, Nonempty (Flow ν a f S) → S ≤ T := by
  constructor
  · intro h S hS
    exact (ENNReal.ofReal_le_ofReal_iff hT).mp
      ((horizon_le_lifespan hS.some).trans h)
  · intro h
    exact iSup_le (fun S => iSup_le (fun hS => ENNReal.ofReal_le_ofReal (h S hS)))

theorem lifespan_le_iff_no_extension {ν T : ℝ} (hT : 0 ≤ T)
    (a : Space → Space) (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ↔ ∀ S, T < S → IsEmpty (Flow ν a f S) := by
  rw [lifespan_le_iff hT]
  constructor
  · intro h S hTS
    exact ⟨fun U => (not_lt_of_ge (h S ⟨U⟩)) hTS⟩
  · intro h S hS
    by_contra hST
    exact (h S (lt_of_not_ge hST)).false hS.some

/-- The elementary two-case alternative uses actual solution witnesses. -/
theorem bad_or_regular_reference {ν T : ℝ} (hT : 0 ≤ T)
    (a : Space → Space) (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ∨ ∃ S, T < S ∧ Nonempty (Flow ν a f S) := by
  by_cases h : lifespan ν a f ≤ ENNReal.ofReal T
  · exact Or.inl h
  · right
    have hn : ¬ ∀ S, Nonempty (Flow ν a f S) → S ≤ T := by
      simpa only [← lifespan_le_iff hT] using h
    push Not at hn
    obtain ⟨S, hS, hTS⟩ := hn
    exact ⟨S, hTS, hS⟩

/-- Restrict an actual flow to a shorter positive horizon. -/
def Flow.restrict {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) {b : ℝ} (hb : 0 < b) (hbs : b ≤ S) : Flow ν a f b := by
  refine { velocity := U.velocity, pressure := U.pressure, horizon_pos := hb, velocity_smooth := ?_, pressure_smooth := ?_, initial := U.initial, divergence := ?_, equation := ?_, energy := ?_, velocity_bound := ?_, derivative_bound := ?_ }
  · exact U.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_le hbs⟩, hz.2⟩)
  · exact U.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_le hbs⟩, hz.2⟩)
  · intro t ht x; exact U.divergence t ⟨ht.1, ht.2.trans_le hbs⟩ x
  · intro t ht x; exact U.equation t ⟨ht.1, ht.2.trans_le hbs⟩ x
  · intro c hc; exact U.energy c ⟨hc.1, hc.2.trans_le hbs⟩
  · intro c hc; exact U.velocity_bound c ⟨hc.1, hc.2.trans_le hbs⟩
  · intro c hc; exact U.derivative_bound c ⟨hc.1, hc.2.trans_le hbs⟩

theorem Flow.nonempty_restrict {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) {b : ℝ} (hb : 0 < b) (hbs : b ≤ S) : Nonempty (Flow ν a f b) :=
  ⟨U.restrict hb hbs⟩

/-! A lower endpoint estimate obtained solely from restriction-stable
    witnesses.  This is the order-theoretic half of an exact endpoint
    statement; it does not assert local existence at the endpoint. -/
theorem lifespan_ge_of_forall_shorter {ν T : ℝ} (hT : 0 < T)
    (a : Space → Space) (f : VelocityField)
    (hshort : ∀ b, 0 < b → b < T → Nonempty (Flow ν a f b)) :
    ENNReal.ofReal T ≤ lifespan ν a f := by
  apply le_of_forall_lt
  intro c hc
  have hc_top : c ≠ (∞ : ℝ≥0∞) := hc.ne_top
  have hcT : c.toReal < T := ENNReal.toReal_lt_of_lt_ofReal hc
  let b : ℝ := (c.toReal + T) / 2
  have hb0 : 0 < b := by
    dsimp [b]
    have : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    linarith
  have hbT : b < T := by
    dsimp [b]
    linarith
  obtain ⟨U⟩ := hshort b hb0 hbT
  have hcb : c < ENNReal.ofReal b := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hc_top]
    dsimp [b]
    linarith
  exact hcb.trans_le (horizon_le_lifespan U)

theorem lifespan_eq_of_forall_shorter_of_upper_bound {ν T : ℝ}
    (hT : 0 < T) (a : Space → Space) (f : VelocityField)
    (hshort : ∀ b, 0 < b → b < T → Nonempty (Flow ν a f b))
    (hupper : lifespan ν a f ≤ ENNReal.ofReal T) :
    lifespan ν a f = ENNReal.ofReal T :=
  le_antisymm hupper (lifespan_ge_of_forall_shorter hT a f hshort)

theorem Flow.velocity_smooth_slab {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) {b : ℝ} (hb : b < S) :
    ContDiffOn ℝ ∞ U.velocity (NavierStokesR3.Comparison.slab 0 b) :=
  U.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hb⟩, hz.2⟩)

theorem Flow.pressure_smooth_slab {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) {b : ℝ} (hb : b < S) :
    ContDiffOn ℝ ∞ U.pressure (NavierStokesR3.Comparison.slab 0 b) :=
  U.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hb⟩, hz.2⟩)

/-- Compact spatial perturbations preserve finite energy on a closed
presingular slab. The integrability assertions are genuine, not totalized
integral identities. -/
theorem insertion_energy_on_slab {ν r T τ b : ℝ} {x₀ : Space}
    {v g V G : VelocityField} {q Q : PressureField}
    (hb : b < T)
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ))
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) b) v)
    (h : InsertionFamily.InsertionProperties ν v q g x₀ r T τ V Q G) :
    UniformFiniteEnergy (Icc (0 : ℝ) b) V := by
  have hsub : Icc (0 : ℝ) b ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) T ×ˢ univ :=
    fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hb⟩, hz.2⟩
  have hvs := hv.mono hsub
  have hVs := h.1.mono hsub
  obtain ⟨L, hLc, _, hLs⟩ := h.2.2.2.2.2.1
  have hd : UniformFiniteEnergy (Icc (0 : ℝ) b) (fun z => v z - V z) := by
    apply NavierStokesR3.CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab
      (hvs.sub hVs) hLc
    intro t ht
    have hh := (hLs t ⟨ht.1, ht.2.trans_lt hb⟩).1
    have he : (fun x => v (t, x) - V (t, x)) = -(fun x => V (t, x) - v (t, x)) := by
      funext x
      simp only [Pi.neg_apply, neg_sub]
    rw [he, tsupport_neg]
    exact hh
  have he := NavierStokesR3.Comparison.uniformFiniteEnergy_sub_of_continuousOn
    hvs.continuousOn (hvs.sub hVs).continuousOn hev hd
  simpa only [sub_sub_cancel] using he

/-- Compact spatial insertion transfers both classical bounds from the reference.
The strictly larger slab also handles the requested endpoint `b = 0`. -/
theorem insertion_bounds_on_slab {ν r T τ R b : ℝ} {x₀ : Space}
    {a : Space → Space} {g V G : VelocityField} {Q : PressureField}
    (hb : b ∈ Ico (0 : ℝ) T) (hTR : T < R) (U : Flow ν a g R)
    (h : InsertionFamily.InsertionProperties
      ν U.velocity U.pressure g x₀ r T τ V Q G) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x, ‖V (t, x)‖ ≤ B) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x,
      ‖spatialDerivative V t x‖ ≤ D) := by
  let c := (b + T) / 2
  have hc0 : 0 < c := by dsimp [c]; linarith [hb.1, hb.2]
  have hcT : c < T := by dsimp [c]; linarith [hb.2]
  have hbc : b ≤ c := by dsimp [c]; linarith [hb.2]
  have hVs : ContDiffOn ℝ ∞ V (NavierStokesR3.Comparison.slab 0 c) :=
    h.1.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans_lt hcT⟩, hz.2⟩)
  obtain ⟨L, hLc, _, hLs⟩ := h.2.2.2.2.2.1
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hLc).exists_bound_of_continuousOn
    (hVs.continuousOn.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩))
  obtain ⟨D, _, hD⟩ := NavierStokes.PeriodicUniqueness.exists_gradient_bound hc0 hVs hLc
  obtain ⟨B, hB0, hB⟩ := U.velocity_bound c ⟨hc0.le, hcT.trans hTR⟩
  obtain ⟨E, hE0, hE⟩ := U.derivative_bound c ⟨hc0.le, hcT.trans hTR⟩
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) c) (x : Space) (hx : x ∉ L) :
      (fun y => V (t, y)) =ᶠ[𝓝 x] (fun y => U.velocity (t, y)) := by
    filter_upwards [hLc.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun z => V (t, z) - U.velocity (t, z))
      (fun hz => hy ((hLs t ⟨ht.1, ht.2.trans_lt hcT⟩).1 hz)))
  constructor
  · refine ⟨max B C, hB0.trans (le_max_left _ _), ?_⟩
    intro t ht x
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.trans hbc⟩
    by_cases hx : x ∈ L
    · exact (hC (t, x) ⟨htc, hx⟩).trans (le_max_right _ _)
    · rw [(heq t htc x hx).eq_of_nhds]
      exact (hB t htc x).trans (le_max_left _ _)
  · refine ⟨max E D, hE0.trans (le_max_left _ _), ?_⟩
    intro t ht x
    have htc : t ∈ Icc (0 : ℝ) c := ⟨ht.1, ht.2.trans hbc⟩
    by_cases hx : x ∈ L
    · exact (hD t htc x hx).trans (le_max_right _ _)
    · have hd : spatialDerivative V t x = spatialDerivative U.velocity t x :=
        (heq t htc x hx).fderiv_eq
      rw [hd]
      exact (hE t htc x).trans (le_max_left _ _)

/-- The inserted fields themselves form an actual classical flow on the full
half-open horizon, without any additional energy or derivative premise. -/
def insertionFlow {ν r T τ R : ℝ} {x₀ : Space}
    {a : Space → Space} {g V G : VelocityField} {Q : PressureField}
    (hT : 0 < T) (hτ : 0 ≤ τ) (hTR : T < R)
    (U : Flow ν a g R)
    (h : InsertionFamily.InsertionProperties
      ν U.velocity U.pressure g x₀ r T τ V Q G) : Flow ν a (g + G) T := by
  have hvT : ContDiffOn ℝ ∞ U.velocity (Ico (0 : ℝ) T ×ˢ univ) :=
    U.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, hz.1.2.trans hTR⟩, hz.2⟩)
  refine { velocity := V, pressure := Q, horizon_pos := hT, velocity_smooth := h.1, pressure_smooth := h.2.1, initial := ?_, divergence := h.2.2.2.2.2.2.1, equation := ?_, energy := ?_, velocity_bound := ?_, derivative_bound := ?_ }
  · intro x
    exact (h.2.2.2.2.2.2.2.2.2.2 0 hτ x).1.trans (U.initial x)
  · exact h.2.2.2.2.2.2.2.1
  · intro b hb
    exact insertion_energy_on_slab hb.2 hvT (U.energy b ⟨hb.1, hb.2.trans hTR⟩) h
  · intro b hb
    exact (insertion_bounds_on_slab hb hTR U h).1
  · intro b hb
    exact (insertion_bounds_on_slab hb hTR U h).2

end NSFormalization.Source.SmoothLifespan
