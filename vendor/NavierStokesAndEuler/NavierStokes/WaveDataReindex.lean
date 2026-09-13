import NavierStokes.PhysicalStageBounds

/-!
# Injective source reindexing for actual physical wave data

Only the discrete native source index is enlarged.  The source and its weight
are extended by zero outside the embedding's image.  Physical copies, support
cells, chart maps, frequencies and all physical fields remain unchanged.
-/

noncomputable section

namespace NavierStokes.WaveDataReindex

open Set Function Filter ProblemStatement
open PhysicalStageBounds
open scoped Topology ContDiff BigOperators

variable {I I' : Type*}

/-- An injective extension with a specified zero value off the image. -/
noncomputable def zeroExtend {V : Type*} [Zero V] (e : I ↪ I') (f : I → V) : I' → V :=
  Function.extend e f 0

@[simp] theorem zeroExtend_apply {V : Type*} [Zero V] (e : I ↪ I') (f : I → V) (i : I) :
    zeroExtend e f (e i) = f i :=
  e.injective.extend_apply f 0 i

theorem zeroExtend_of_not_mem_range {V : Type*} [Zero V] (e : I ↪ I') (f : I → V)
    {i : I'} (hi : i ∉ Set.range e) : zeroExtend e f i = 0 :=
  Function.extend_apply' (f := (e : I → I')) f (0 : I' → V) i hi

section Bounds

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : WeightedClasses.StripData D} {h α : ℝ}
  {weight : I → ℕ → D → ℝ} {source : I → ℕ → D → E}

/-- Every supplied finite-jet constant and degree works unchanged after
extension.  At the added indices both sides of the estimate are zero. -/
theorem zeroExtend_bounds (e : I ↪ I') {m p : ℕ} {C : ℝ}
    (hb : ∀ i n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (source i n) x‖ ≤ WeightedClasses.majorant s (weight i) α C p n x) :
    ∀ i n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (zeroExtend e source i n) x‖ ≤
        WeightedClasses.majorant s (zeroExtend e weight i) α C p n x := by
  intro i n x hx j hj
  by_cases hi : i ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hi
    simpa only [zeroExtend_apply] using hb l n x hx j hj
  · rw [zeroExtend_of_not_mem_range e source hi, zeroExtend_of_not_mem_range e weight hi]
    change ‖iteratedFDeriv ℝ j (fun _ : D => (0 : E)) x‖ ≤
      WeightedClasses.majorant s (fun _ _ => 0) α C p n x
    rw [iteratedFDeriv_fun_zero]
    simp [WeightedClasses.majorant]

theorem uniformClass_zeroExtend (e : I ↪ I')
    (hf : LabelSumBounds.UniformClass s weight α source) :
    LabelSumBounds.UniformClass s (zeroExtend e weight) α (zeroExtend e source) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i n x hx
    by_cases hi : i ∈ Set.range e
    · obtain ⟨l, rfl⟩ := hi
      simpa only [zeroExtend_apply] using hf.weight_nonneg l n x hx
    · rw [zeroExtend_of_not_mem_range e weight hi]
      exact le_rfl
  · intro i n
    by_cases hi : i ∈ Set.range e
    · obtain ⟨l, rfl⟩ := hi
      simpa only [zeroExtend_apply] using hf.smooth l n
    · rw [zeroExtend_of_not_mem_range e source hi]
      exact contDiffOn_const
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.bounds m
    exact ⟨C, hC, p, zeroExtend_bounds e hb⟩

/-- All geometric and band constants are retained; no global extension in the
continuous variables is involved. -/
theorem localSourceBounds_zeroExtend (e : I ↪ I')
    (hf : LocalPhysicalCopyBounds.LocalSourceBounds (E := E) s h α weight source) :
    LocalPhysicalCopyBounds.LocalSourceBounds (E := E) s h α
      (zeroExtend e weight) (zeroExtend e source) := by
  refine ⟨uniformClass_zeroExtend e hf.uniform, hf.flat_geometry, ?_, hf.epsilon_eq, hf.slow_le⟩
  obtain ⟨c, hc, hb⟩ := hf.weight_le
  refine ⟨c, hc, ?_⟩
  intro i n x hx
  by_cases hi : i ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hi
    simpa only [zeroExtend_apply] using hb l n x hx
  · rw [zeroExtend_of_not_mem_range e weight hi]
    exact Real.rpow_nonneg (s.zeta_nonneg x hx) c

end Bounds

section WaveData

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {K J : Type*}

/-- Reindex the native reference used by each unchanged physical copy. -/
noncomputable def reindexChart {N : ℕ} {f : PhysicalCopyBounds.CopyFamily N K}
    {cells : PhysicalCopyBounds.SupportCells f} {a b r σ : ℝ}
    {source : I → ℕ → D → ℂ} (e : I ↪ I')
    (c : LocalPhysicalCopyBounds.CommonChart f cells a b h r σ source) :
    LocalPhysicalCopyBounds.CommonChart f cells a b h r σ (zeroExtend e source) where
  sourceIndex k L := e (c.sourceIndex k L)
  map := c.map
  domain := c.domain
  open_domain := c.open_domain
  smooth := c.smooth
  positive_jets := c.positive_jets
  amplitude_eq := by
    intro k L x hx
    simpa only [zeroExtend_apply] using c.amplitude_eq k L hx
  contains := c.contains

/-- Enlarge only the source type. Every copy, carrier, support cell and chart
map is literally the original one. -/
noncomputable def reindexSource (e : I ↪ I') (W : WaveData h D I K J) : WaveData h D I' K J where
  lowerRadius := W.lowerRadius
  upperRadius := W.upperRadius
  nativeWidth := W.nativeWidth
  slowBound := W.slowBound
  frequencyBound := W.frequencyBound
  alpha := W.alpha
  shift := W.shift
  harmonics := W.harmonics
  gapBound := W.gapBound
  lower_pos := W.lower_pos
  width_nonneg := W.width_nonneg
  slow_nonneg := W.slow_nonneg
  frequency_one_le := W.frequency_one_le
  strip := W.strip
  weight := zeroExtend e W.weight
  source := zeroExtend e W.source
  source_bounds := localSourceBounds_zeroExtend e W.source_bounds
  copies := W.copies
  cells := W.cells
  chart i := reindexChart e (W.chart i)
  chart_maps := W.chart_maps
  carrier := W.carrier
  support := W.support
  smooth := W.smooth
  frequencies := W.frequencies

@[simp] theorem reindexSource_alpha (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).alpha = W.alpha := rfl

@[simp] theorem reindexSource_shift (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).shift = W.shift := rfl

@[simp] theorem reindexSource_harmonics (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).harmonics = W.harmonics := rfl

@[simp] theorem reindexSource_lowerRadius (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).lowerRadius = W.lowerRadius := rfl

@[simp] theorem reindexSource_upperRadius (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).upperRadius = W.upperRadius := rfl

@[simp] theorem reindexSource_nativeWidth (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).nativeWidth = W.nativeWidth := rfl

@[simp] theorem reindexSource_slowBound (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).slowBound = W.slowBound := rfl

@[simp] theorem reindexSource_frequencyBound (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).frequencyBound = W.frequencyBound := rfl

@[simp] theorem reindexSource_gapBound (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).gapBound = W.gapBound := rfl

@[simp] theorem reindexSource_strip (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).strip = W.strip := rfl

@[simp] theorem reindexSource_source (e : I ↪ I') (W : WaveData h D I K J) (i : I) :
    (reindexSource e W).source (e i) = W.source i := zeroExtend_apply e W.source i

@[simp] theorem reindexSource_weight (e : I ↪ I') (W : WaveData h D I K J) (i : I) :
    (reindexSource e W).weight (e i) = W.weight i := zeroExtend_apply e W.weight i

theorem reindexSource_source_zero (e : I ↪ I') (W : WaveData h D I K J) {i : I'}
    (hi : i ∉ Set.range e) : (reindexSource e W).source i = 0 :=
  zeroExtend_of_not_mem_range e W.source hi

theorem reindexSource_weight_zero (e : I ↪ I') (W : WaveData h D I K J) {i : I'}
    (hi : i ∉ Set.range e) : (reindexSource e W).weight i = 0 :=
  zeroExtend_of_not_mem_range e W.weight hi

@[simp] theorem reindexSource_copies (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).copies = W.copies := rfl

@[simp] theorem reindexSource_cells (e : I ↪ I') (W : WaveData h D I K J) :
    (reindexSource e W).cells = W.cells := rfl

@[simp] theorem reindexSource_chart_map (e : I ↪ I') (W : WaveData h D I K J) (i : J) :
    ((reindexSource e W).chart i).map = (W.chart i).map := rfl

@[simp] theorem reindexSource_chart_domain (e : I ↪ I') (W : WaveData h D I K J) (i : J) :
    ((reindexSource e W).chart i).domain = (W.chart i).domain := rfl

@[simp] theorem reindexSource_chart_index (e : I ↪ I') (W : WaveData h D I K J)
    (i : J) (k : K) (L : PhysicalWaveSum.WaveIndex W.harmonics) :
    ((reindexSource e W).chart i).sourceIndex k L = e ((W.chart i).sourceIndex k L) := rfl

@[simp] theorem reindexSource_scalar (e : I ↪ I') (W : WaveData h D I K J) (i : J) :
    (reindexSource e W).scalar i = W.scalar i := rfl

@[simp] theorem reindexSource_vector (e : I ↪ I') (W : WaveData h D I K (Fin 3)) :
    (reindexSource e W).vector = W.vector := rfl

@[simp] theorem reindexSource_pressure (e : I ↪ I') (W : WaveData h D I K Unit) :
    (reindexSource e W).pressure = W.pressure := rfl

/-- The original locally finite representation and its precise overlap
bound are retained; the enlarged source type contributes no new summands. -/
theorem reindexSource_locally_finite (e : I ↪ I') (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) {w : SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal) :
    ∃ s : Finset (PhysicalWaveSum.WaveIndex W.harmonics),
      s.card ≤ 2250 * (2 * W.harmonics + 1) ∧
      (reindexSource e W).scalar i =ᶠ[𝓝 w] fun y =>
        ∑ L ∈ s, (W.copies i).periodized W.lowerRadius h W.nativeWidth L y :=
  (W.support i).sum_locally_finite hh hh1 hw

end WaveData

section FixedSourceType

variable {T : Type*} {S : Type*} {family : S → Type*}
  {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {K J : Type*}

/-- A varying source type is embedded in one fixed disjoint union. -/
noncomputable def toSigma (s : S) (W : WaveData h D (family s) K J) :
    WaveData h D (Sigma family) K J :=
  reindexSource (Function.Embedding.sigmaMk s) W

/-- The potential component tag stays outside the same fixed source type
used by pressure data. In applications `T = Fin 3`. -/
noncomputable def toSigmaComponents (s : S) (W : WaveData h D (T × family s) K J) :
    WaveData h D (T × Sigma family) K J :=
  reindexSource ((Function.Embedding.refl T).prodMap (Function.Embedding.sigmaMk s)) W

@[simp] theorem toSigma_source (s : S) (W : WaveData h D (family s) K J) (i : family s) :
    (toSigma s W).source ⟨s, i⟩ = W.source i :=
  zeroExtend_apply (Function.Embedding.sigmaMk s) W.source i

theorem toSigma_source_of_ne {s t : S} (hst : s ≠ t) (W : WaveData h D (family s) K J)
    (i : family t) : (toSigma s W).source ⟨t, i⟩ = 0 := by
  apply reindexSource_source_zero
  rintro ⟨j, hj⟩
  exact hst (congrArg Sigma.fst hj)

@[simp] theorem toSigma_pressure (s : S) (W : WaveData h D (family s) K Unit) :
    (toSigma s W).pressure = W.pressure := rfl

@[simp] theorem toSigmaComponents_source (s : S) (W : WaveData h D (T × family s) K J)
    (t : T) (i : family s) :
    (toSigmaComponents s W).source (t, ⟨s, i⟩) = W.source (t, i) :=
  zeroExtend_apply ((Function.Embedding.refl T).prodMap (Function.Embedding.sigmaMk s))
    W.source (t, i)

@[simp] theorem toSigmaComponents_vector (s : S) (W : WaveData h D (T × family s) K (Fin 3)) :
    (toSigmaComponents s W).vector = W.vector := rfl

end FixedSourceType

end NavierStokes.WaveDataReindex
