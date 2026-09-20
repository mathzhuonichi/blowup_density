# T13 (lem:localization, `03-torus.tex:22-29`) — reconciliation of the double-blind drafts A (lane 265, gpt-5.6-sol) and B (lane 266, gpt-6-astra)

Lead: erenup, 2026-09-17 (UTC 19:20). Drafts: `.claude/worktrees/265-SPEC-t13-draft-a/research/T13/DraftA.lean`, `.claude/worktrees/266-SPEC-t13-draft-b/research/T13/DraftB.lean` (both elaborate).

## 1. Agreement
Both state, for `0 < s < 1`: (i) the Gagliardo double integral on ℝ³ equals `c_s · ‖·‖²_{Ḣ^s(ℝ³)}` (registered `dotHomogeneousENorm`), (ii) the torus double integral equals `c_s · ‖·‖²_{Ḣ^s(T³)}` (coefficient-side homogeneous norm; B subtracts the mean explicitly, A works with the mean-zero part implicitly), (iii) `eq:localization`: for smooth `f` supported in a coordinate ball whose closure lies inside a fundamental cube, `‖periodization‖_{H^s(T³)} ≤ C_{s,B} (‖f‖₂ + ‖f‖_{Ḣ^s(ℝ³)})` with `C` chosen **before** `f` (uniform as the support shrinks), (iv) the endpoints `s = 0` (`L²` equality) and `s = 1` (gradient `L²` equality). Both define the kernel `K_s`, the lattice tail sum and the constant `c_s` as `ℝ≥0∞`-valued defs.

## 2. Rulings
| point | A | B | ruling |
|---|---|---|---|
| fundamental cube | fixed `openFundamentalCube` | arbitrary translate `Q a` | **fixed fundamental cube** (the torus's; matches T10's `torusRepresentative`); ball `B = ball c r` with `closure B ⊆ interior cube` (A's `IsCoordinateBall` ≡ B's `AdmissibleBall` at `a = 0`). |
| periodization | relation `IsSpatialPeriodization zR zT` | function `periodize f` | **`periodize` as a `def`** (B) + the lemma that it is the unique periodic field agreeing with the zero extension on the cube (A's relation becomes a lemma, not a field). |
| tail lemmas (`:80-89`) | absent | fields `lattice_summable`, `tail_bound` | **not API fields** (they are steps of the proof); listed in "needs a lemma" for the proof lane. `constant_pos_finite` (B) **kept** as a field (the lemma's constant is a genuine positive finite number). |
| endpoints | one combined field | `endpoint_zero`, `endpoint_one` | **B's two fields**. |
| norm vocabulary | own local periodic data | own local periodic data | **use T10's reconciled vocabulary** (`research/T10/Spec.lean`, lane 267): `periodicSobolevENorm`, `periodicHomogeneousENorm`, `IsPeriodicDatum`; ℝ³ side: registered `dotHomogeneousENorm`, `eLpNorm f 2 volume`. T13's spec lane therefore runs **after** T10's spec lane and imports it. |
| `s` range | `0 < s < 1` | `0 < s < 1` | keep; the paper's lemma is stated for this range (the `s = 0, 1` endpoints separately). |
| scalar vs vector | vector (`Space → Space`) | vector | vector fields (the paper applies it to velocity/force differences). |

## 3. Decisions
`structure LocalizationAPI : Prop` with fields `constant_pos_finite`, `wholeSpace_identity`, `torus_identity`, `localization`, `endpoint_zero`, `endpoint_one` (B's names), hypotheses `ContDiff ℝ ∞ f ∧ SupportedInBall c r f` with `closure (ball c r) ⊆ interior fundamentalCube`; docstrings merge A's line citations.

## 4. Proof dependencies (lane split later)
Gagliardo identities via Fourier/Parseval (ℝ³: D01's `HomogeneousWitness`; T³: T10's Parseval bridge `TorusCube`), the kernel periodization `K_s(h) = Σ_n |h + n|^{-3-2s}` and its tail bound (`lattice_summable`, `tail_bound`), the comparison of the two double integrals on the ball (the geometric separation `d`), endpoints by direct computation. The vendor's `PeriodicLocalization`/`PeriodicBridge` (see `SECTION3_PLAN.md` T13 row) may supply pieces — the proof lane checks.

## 5. Next
Lane 268 (after 267 = T10 reconciled spec): `research/T13/Spec.lean` importing T10's names + merged `COMPARISON.md`; then the proof lanes (astra; L).
