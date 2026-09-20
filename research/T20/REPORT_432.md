# REPORT_432 — T20 U10b `hOneEnergy` (Opus; transcribed by lead from the agent message, report-file guard)

Lane 432 is complete. U10b closed with no residual.

## 1. What was proved

`eq:H1energy` (`paper/sections/03-torus.tex:467-484`) — the `H¹` energy inequality of `prop:critical` — as the `hOneEnergy` field of `CriticalRegularityTAPI` **verbatim**:

```lean
theorem hOneEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x))
```

**The constants.** `def CH1 : ℝ := 2` (`CH1_pos`). Both absorbed halves are `ν/4`-sized, so the surviving right-hand coefficient is exactly `2`.

`def criticalSmallnessH1 : ℝ := min criticalSmallness (1 / (8 * h1TrilinearConst))` — smaller than U9's `criticalSmallness`, because the `H¹` absorption needs `c ≤ 1/(8·C₁)` with `C₁ = h1TrilinearConst` (lane 429). Five facts are exported for U13: `criticalSmallnessH1_pos`; `criticalSmallnessH1_le_half` (`c ≤ 1/(2C₀)`, so U9's `yBound_of_le` applies verbatim at this `c` — U13 must use `yBound_of_le criticalSmallnessH1_le_half`, not `yBound`, which is stated at the larger `criticalSmallness`); `criticalSmallnessH1_lt_quarter_C₀` and `criticalSmallnessH1_lt_quarter_C₁` (the structure's two **strict** shrinking fields `c_lt_C₀`, `c_lt_C₁`); and `criticalSmallnessH1_le_eighth_C₁`.

No named input, no placeholder, no goal repackaging, no `maxHeartbeats` override, no edits to existing modules. All 31 declarations print exactly `[propext, Classical.choice, Quot.sound]`.

The arithmetic in full: `E' = −2ν‖Δv‖₂² + 2·P_force + 2·Q_conv`, with `P_force ≤ ‖Δv‖₂‖h‖₂` and `Q_conv ≤ C₁·y·‖Δv‖₂²`. U9 gives `y ≤ ρ < cν`, and `c ≤ 1/(8C₁)` turns `2Q_conv` into `(ν/4)‖Δv‖₂²`; Young gives `2‖Δv‖₂‖h‖₂ ≤ (ν/2)‖Δv‖₂² + (2/ν)‖h‖₂²`. Hence `E' + ν‖Δv‖₂² ≤ −(ν/4)‖Δv‖₂² + 2ν⁻¹‖h‖₂² ≤ 2ν⁻¹‖h‖₂²`.

**Two findings worth the lead's attention.**

- **U10b does not depend on U6** (`meanFreeEquation`), nor on `torusYoungAbsorb`, nor on `HighOrder.lean:312,345,367`. As with U8 and U5, everything runs frequency-by-frequency through U8's `rawEnergyDeriv_split` (T11's `freqEnergyDerivT_split` at order 0, where the pressure has already dropped) and U8's `re_sum_conj_fderiv_dir_zero` (weight-independent, so it transplants unchanged to the order-one weight). The physical mean-free equation is never formed. `T20_SPLIT.md` listed "Deps: U6, U9, U10a"; the real set is U8 (through `YBound`), U9, U10a. `torusYoungAbsorb`'s shape is cross-term absorption (`½d + νg² ≤ C·a·n·g + F·n`), not `2ab ≤ (ν/2)a² + (2/ν)b²`, so the Young step is three lines inline.
- **The one genuinely missing analytic input** was the order-2 Parseval identity `‖Δz‖_{L²(T³)} = ‖z − ∫z‖_{Ḣ²(T³)}`; T10 had only the order-1 `gradient_eq_homogeneousENorm`. It is proved in ~30 lines by observing that the order-0 datum of `Δz` is the *negative* of the order-2 homogeneous datum of `meanZeroPartT z`, frequency by frequency.
- Lane 429's blocker is gone: lane 427's `T12/DirDeriv.lean` dedupe lets `YBound` (the `GradientLambdaL3` side) and `H1Trilinear` (the `GradientLSix` side) co-import. Verified before writing the module.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/formalization/NSFormalization/Section3/T20/H1Energy.lean` (678 lines, 31 declarations). Reusable beyond U10b, and U11 will want most of it: `periodicLpENorm_two_laplacian_eq_homogeneous` (the order-2 Parseval); `h1FreqEnergy`, `h1FreqEnergyDeriv`, `hasDerivAt_h1FreqEnergy`, `summable_h1FreqEnergy`, `hasDerivAt_tsum_h1FreqEnergy` (the order-1 homogeneous energy differentiated under the sum); `gradientSqT_meanFreeVelocity_eq_tsum`, `laplacianSqT_meanFreeVelocity_eq_tsum`, `summable_laplacianSq_tsum`; `hasSum_angularPairing` (`∑ₖ|2πk|²Re∑ᵢconj(v̂ᵢ)ẑᵢ = −⟪Δv,z⟫_{L²(T³)}`); `periodicPairing_comm`; `dirDeriv_sub_const`, `gradientTensor_sub_const`, `laplacian_sub_const`, `gradientTensor_meanFreeVelocity`, `laplacian_meanFreeVelocity`; `homogeneousDatumWeight_one_sq`, `homogeneousDatumWeight_two_eq`, `angularFrequencySq_le_periodicFrequencyWeight`; `CH1`, `criticalSmallnessH1` and their API.
- `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/research/T20/probes/h1_energy_closes.lean` — checks `example (API : CriticalRegularityTAPI) : hOneEnergyFieldType API.c API.CH1 := API.hOneEnergy` (so the spelling is the structure field, not a paraphrase), `example : hOneEnergyFieldType criticalSmallnessH1 CH1 := hOneEnergy`, `CH1 = 2` by `rfl`, both strict shrinkings, and non-vacuity at lanes 415/428's zero-force zero-solution instance (`ν = 1`, `T = 1`, `t = 1/2`) including a proof that the smallness hypothesis itself is satisfiable (`ρ = 0 < c·ν`), producing an actual real derivative witness.
- `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/research/T20/axioms_u10b.lean`, `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/research/T20/ATTEMPTS_U10B.md`, the U10b status block in `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/research/T20/T20_SPLIT.md`, one line at the top of `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy/logs/LESSONS.md`.
- Committed as `f4e0f721` on `erenup/432-T20-U10b-h1-energy`; working tree clean; nothing pushed, merged or rebased.

## 3. Gaps

**No mathematical gap** — the field is closed outright. Three notes for U13:

- Non-vacuity is again the zero force with the zero solution (lanes 415/428's sanctioned fallback). A nonzero-force instance still needs a compactly-time-supported bump in `forceClassT` plus T11 local existence; neither is assembled anywhere in the tree.
- U13 must install `c := criticalSmallnessH1`, `C₀ := criticalTrilinearConst`, `C₁ := h1TrilinearConst`, `CH1 := 2`, and reach U9 through `yBound_of_le criticalSmallnessH1_le_half` (U9's own `yBound` is stated at the larger `criticalSmallness`). U8's `criticalEnergy` carries no smallness hypothesis, so it is usable unchanged.
- The four failed approaches, each one compile round, are in `ATTEMPTS_U10B.md`: (1) `rw [Real.rpow_one]` on `homogeneousDatumWeight 2 k` — `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern ?x ^ 1 in the target expression (periodicAngularFrequencySq k).rpow 1 = periodicAngularFrequencySq k` (the def is in `Real.rpow` application form; fix is `exact Real.rpow_one _`); (2) `Complex.real_smul` on the homogeneous datum clause — `Did not find an occurrence of the pattern ?m • ?m'`, it is already a **ℂ**-smul, `smul_eq_mul` is the lemma (U8's recorded trap, hit again); (3) the sign of the convection term — `hasSum_angularPairing` targets `−periodicPairing (Δv) N` and the combination subtracts `2·` that, so the bound needed is `le_abs_self`, not U8's `neg_le_abs`; using `neg_le_abs` gave `error: NSFormalization/Section3/T20/H1Energy.lean:682:2: linarith failed to find a contradiction` with everything else already proved; (4) Young by `rw`-surgery (`div_mul_eq_mul_div`, `← sub_nonneg`, `div_add_div … at *`, `nlinarith`) gave `error: NSFormalization/Section3/T20/H1Energy.lean:677:4: linarith failed to find a contradiction` — replaced by the explicit identity `ν/2·a² + 2/ν·b² − 2ab = (νa − 2b)²/(2ν)` plus `div_nonneg`, closed with plain `linarith`. The final module contains no `nlinarith` at all.

I did not write `research/T20/REPORT_432.md` — my standing instruction forbids writing report/summary `.md` files; the full report is this message, as the brief's fallback allows.

## 4. Commands run and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/432-T20-U10b-h1-energy`, after `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section3.T20.YBound NSFormalization.Section3.T20.H1Trilinear` | `Build completed successfully (10653 jobs)` — confirms the lane-427 dedupe lets both sides co-import |
| `lake env lean ../research/T20/scratch/probe0.lean` (signature probe, deleted) | co-import OK; one expected `unknownIdentifier` for a mis-namespaced `#check` |
| `lake build NSFormalization.Section3.T20.H1Energy` (attempt 1) | **failed**, exactly 2 errors: `H1Energy.lean:677:4: linarith failed to find a contradiction` (Young) and `H1Energy.lean:682:2: linarith failed to find a contradiction` (final assembly, the `neg_le_abs`/`le_abs_self` sign) |
| `lake build NSFormalization.Section3.T20.H1Energy` (final) | `Build completed successfully (10654 jobs)`, **0 errors**; only pre-existing upstream warnings replayed from `NSFormalization/Source/*`, `NSFormalization/Paper1/*`, `vendor/HeliCorgi/Formal/*` |
| `lake env lean ../formalization/NSFormalization/Section3/T20/H1Energy.lean` | exit 0, **0 bytes of output** |
| `lake env lean ../research/T20/probes/h1_energy_closes.lean` | exit 0, **0 bytes of output** |
| `lake env lean ../research/T20/axioms_u10b.lean` | exit 0; **31/31** declarations `depends on axioms: [propext, Classical.choice, Quot.sound]`, `bad: []` |
| `grep -nE "sorry\|admit\|native_decide\|maxHeartbeats\|^axiom "` over the new files | one hit, the module docstring line "No `sorry`, no `admit`, no `axiom`, …" |
| `make check` | exit 0 (`OK`, `check_contracts.py`, `test_contract_policy.py` 13 tests `OK`, `check_work_queue.py` "45 work items … consistent") |
| `make test` | exit 0, 0 errors; every registered contract "checked; standard logical axioms only" |
| `git status --short` before commit | only the 4 new files plus `logs/LESSONS.md` and `research/T20/T20_SPLIT.md` — **no existing Lean module touched** |
| `git commit` | `f4e0f721 [432-T20] U10b hOneEnergy: eq:H1energy verbatim at CH1 = 2`; tree clean; no push/merge/rebase |
