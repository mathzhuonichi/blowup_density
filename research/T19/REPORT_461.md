# Lane 461 — T19 U0 reference threading

## 1. Theorems and exact statements

Completed all five requested steps. With canonical T10 types and arguments
```lean
{ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
(ha : a ∈ initialClassT) (hg : g ∈ forceClassT) {T δ : ℝ}
(hT : 0 < T) (hδ : 0 < δ)
(reference : ClassicalSolutionT ν a g (T + δ))
```
`insertionData hν ha hg hT hδ reference : T18.InsertionData` selects the
registered packet and threads all raw clauses into T15. Its radius is `1/4`,
inside the fixed `3/8` chart; `place.T = T` definitionally. T17's existential
supplies the cutoff and correction through classical choice.

```lean
theorem insertionData_rawPremises :
  T18.RawPremises (insertionData hν ha hg hT hδ reference)

noncomputable def insertion :
  T18.PeriodicInsertionAPI (insertionData hν ha hg hT hδ reference)
```

The stored reference is the full classical solution `extendByZero reference`,
with velocity and pressure zero outside its `Ico` lifespan. Smoothness is
transported within the closed slab; momentum uses local equality on the open
slab. The following exports hold for arbitrary horizon `S`:
```lean
extendByZero (reference : ClassicalSolutionT ν a g S) : ClassicalSolutionT ν a g S

extendByZero_velocity_eqOn (reference : ClassicalSolutionT ν a g S) :
  EqOn (extendByZero reference).velocity reference.velocity (Ico (0 : ℝ) S ×ˢ univ)

extendByZero_periodic (reference : ClassicalSolutionT ν a g S) :
  IsPeriodicOn univ (extendByZero reference).velocity

extendByZero_smooth (reference : ClassicalSolutionT ν a g S) :
  ContDiffOn ℝ ∞ (extendByZero reference).velocity (Ioo (0 : ℝ) S ×ˢ univ)
```

For `ins := insertion hν ha hg hT hδ reference`, the exported statements are:
```lean
theorem insertion_eps_pos : 0 < (ins).ε₀

theorem force_mem : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀, (ins).force ε ∈ forceClassT

theorem forceDifference_mem : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    (fun z => (ins).force ε z - g z) ∈ forceClassT

theorem lifespan : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    maximalLifespanT ν a ((ins).force ε) = ENNReal.ofReal T

theorem solution : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ∃ w : ClassicalSolutionT ν a ((ins).force ε) T,
      w.velocity = (ins).velocity ε ∧ w.pressure = (ins).pressure ε

theorem blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    NSFormalization.Section4.A02.limsupLeft T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => (ins).velocity ε (t, x))) = ⊤

theorem energyRate : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    energyENormT T (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) ≤
      ENNReal.ofReal (((BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
        (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        (insertionData hν ha hg hT hδ reference).correction.energyConst * ε ^ ((3 : ℝ) / 2))

theorem forceDiffMixedConst_nonneg : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ (ins).forceDiffMixedConst p q

theorem forceDifference_mixed_memLp : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemMixedLebesgueT q p (fun z => (ins).force ε z - g z)

theorem forceDifference_mixed_bound : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      mixedLebesgueENormT q p (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffMixedConst p q *
          (ε ^ (alphaT p q) +
            ε ^ (alphaT p q + 1)))

theorem forceDiffSobolevConst_pos : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < (ins).forceDiffSobolevConst s

theorem forceDifference_sobolev_memLp : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z)

theorem forceDifference_sobolev_bound : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      forceSobolevENormT 1 s (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))

theorem forceDifference_negativeSobolev_tendsto : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

theorem negative_s_memLp : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z)

theorem forceDifference_sobolev_tendsto (s : ℝ) (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))
```

The completed strict-closeness packaging has **no reference or margin input**:
```lean
theorem exists_force_close
    {ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
    (ha : a ∈ initialClassT) (hg : g ∈ forceClassT)
    {T : ℝ} (hT : 0 < T) (hreg : RegularThroughT ν a g T)
    (s : ℝ) (hs : s < 1 / 2) (r' : ℝ) (hr' : 0 < r') :
    ∃ f ∈ forceClassT, maximalLifespanT ν a f = ENNReal.ofReal T ∧
      forceSobolevENormT 1 s (fun z => f z - g z) < ENNReal.ofReal r'
```
For nonnegative orders the bound is squeezed by the existing
`Paper1.sobolev_error_tendsto_zero`; negative orders use T18's limit directly.
`Ioc_mem_nhdsGT` supplies an admissible scale satisfying the strict inequality.

## 2. Files

- New `formalization/NSFormalization/Section3/T19/Threading.lean`: 25 declarations.
- New `research/T19/probes/threading_closes.lean`: literal export statements,
  each proved with `exact`, plus constructor and zero-extension checks.
- New `research/T19/axioms_u0.lean`: all 25 declarations print exactly
  `[propext, Classical.choice, Quot.sound]`.
- New `research/T19/ATTEMPTS_U0.md`: all failed approaches and exact diagnostics.
- Updated `research/T19/T19_SPLIT.md`: U0 completion and U7/U8/U9/U13 route,
  build `ins` = `T19.insertion`.
- This report. No existing Lean module, contract, binding or test was edited.

## 3. Gaps and error text

No remaining gap, including the optional final theorem. No placeholder,
named analytic input, extra hypothesis, admission, added axiom, or heartbeat
setting. Resolved errors are recorded in full in `ATTEMPTS_U0.md`:
pressure-gauge unfolding, record layout, notation projection parsing,
filter inference, section-variable inclusion, and docstring placement.
The original `correctionStatementSlab` is refuted upstream; this module uses
`SlabBridge2.correctionStatementSlab'_holds` exactly as the G5 addendum directs.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, ran from `verification/`,
and used `LEAN_NUM_THREADS=6`.

- Required closure: `lake build NSFormalization.Section3.T18.Assembly NSFormalization.Section3.T15.Assembly NSFormalization.Section3.T17.SlabBridge`: exit 0, 10645 jobs.
- Updated bridge and packet: `lake build NSFormalization.Section3.T17.SlabBridge2 Bindings.PacketImport`: exit 0.
- `lake build NSFormalization.Section3.T19.Threading`: exit 0, 10655 jobs; dependency warnings replayed, new module clean.
- `lake env lean ../formalization/NSFormalization/Section3/T19/Threading.lean`: exit 0, zero output.
- `lake env lean ../research/T19/probes/threading_closes.lean`: exit 0, zero output.
- `lake env lean ../research/T19/axioms_u0.lean`: exit 0; exactly the standard three axioms for all 25 declarations.
- `make check`: exit 0; 50 contracts, 13 policy tests, 45 consistent work items. Existing informational source-manifest/copy diagnostics remain.
- `lake test` (the `make test` target, invoked from `verification/`): exit 0, 10978 jobs.
- `make test-mutations`: exit 0; implementation refactor accepted, admission/extra-axiom/weakened-hypothesis mutations rejected as required.
- `git diff --check`: exit 0. Forbidden-token scan of the new implementation and probe: no matches.

Committed on `erenup/461-T19-U0-insertion-from-reference`; no push, merge or rebase.
