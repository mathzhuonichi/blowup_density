# A01 units A2 / A2b / A3 — propagation-and-continuation spine split (lane 122)

Task **A01** ("Whole-space local solution adapter"), the L-units A01_SPLIT.md §b
marks `gap`: **A2** high-order propagation (eq:Rhigh), **A2b** order-`m`
continuation + cross-order agreement, **A3** the order-independent `T₀`, plus
**T1**'s dependence on them.

> **Revised after lane-122 review** (`REVIEW_A3.md`, ACCEPT-WITH-NOTES).  The
> Lean (`Section4/A01/Propagation.lean`) is accepted; this table's revision-1
> claim in §3b that the OpenAI/local layer has *no* forced-path continuation was
> **false** (finding F5) — the vendored package has
> `EulerBoundedMildContinuation.exists_global_mild_of_bound` on exactly
> `exists_local`'s carrier and `Coefficients` bundle.  A2b is therefore **not** an
> L and **not** blocked on C1c; A3-L2 collapses; and two more rows are
> re-attributed (F6, F7) and two added (F8, F9).  The composability is verified in
> `research/A01/probes/a2b_continuation_probe.lean` (compiles, standard 3 axioms).

Recommended route (COMPARISON.md §4, unchanged): **OpenAI/local forced Duhamel**
spine (`Source/OrdinaryForcedLocal.exists_local`), HeliCorgi for the pressure
edge only.  Lowest propagated order `m₀ = q+1 = 7` (`hq : 6 ≤ q`).  The
manuscript's **driver order is the fixed order 2** (eq:criterion,
`02-preliminaries.tex:111`), which is *below* `m₀`; do not conflate them (F6).

Size key: **S** ≤ ~100 lines; **M** self-contained known-proof lemma; **L**
multi-file campaign.  Status: **DONE** this lane / **★ next lane** (probe compiles)
/ **open** / **blocked**.

---

## 0. The reduction chain (what A3 actually is)

A3 is the assembly turning A04's per-order energy identity into a single horizon
carrying every order.  Top to bottom:

1. **eq:Rhigh** (A2, shared with A04), `E := ‖u‖²_{H^m}`, `m ≥ 3`
   (`appendix-a:129,132-137`): `½ E' + ν‖∇u‖²_{H^m} ≤ C‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}
   + ‖f‖_{H^m}‖u‖_{H^m}`.  = `A04.inner_energy_Rhigh` (`HighEnergy.lean:136`) once
   its `hpr` lands (A04 `energyIdentityHigh`, `research/A04/Spec.lean:424`).
   **A01 consumes, does not reprove.**
2. **Young** (A3-M1): absorb `‖∇u‖_{H^m}` into dissipation ⟹
   `E' ≤ 2(K·E + b·√E)`, `K = (C²/4ν)‖u‖²_{H²}`, `b = ‖f‖_{H^m}`.
3. **ζ↓0 device** (A3-M2): `A04.sqrt_le_primitive_linear` (`Regularized.lean:134`)
   ⟹ integral step for `y := √E = ‖u‖_{H^m}`: `y t ≤ y 0 + ∫₀ᵗ(C_gron·k·y + b)`,
   `k = ‖u‖²_{H²}`, `C_gron = C²/4ν`.
4. **Uniform bound on `[0,T₀)`** (A3-S1, **DONE**): `gronwall_bddAbove_Ico` reuses
   `A04.gronwall_integral_mul` (`Gronwall.lean:202`) and caps to
   `(y 0 + Bbnd)·exp(C_gron·Kbnd)`.
5. **Same `T₀`, every order** (A3-S2, **DONE**): `higherOrder_bddAbove`.

`Propagation.lean` proves steps 4–5.  The Grönwall consequence is
`appendix-a:146-147` (F10); `:148-152` is the *restart* passage = A2b.

---

## 1. Sub-lemma table

| # | unit | Lean-ready statement | size | inputs (file:line, only `#check`ed) | status / blocker |
|---|---|---|---|---|---|
| **A3-U common horizon** | one ordinary `U` on `[0,S]` realizes canonical mild solutions at every `q ≥ 6` | M | per-order bounds + `hfs` + explicit `MildUniqueness` | **Conditional reduction (186)**: lowering/commutation proved; unrestricted order-six mild uniqueness remains. `CommonHorizon.lean`, `ATTEMPTS_A3_COMMON_HORIZON.md` |
| **A3-U common horizon** | one ordinary `U` on `[0,S]` realizes canonical mild solutions at every `q ≥ 6` | M | per-order bounds + canonical `MemForceR` force | **WIRED (lane 192), conditional only on A3-M2's all-order `hb` family**: `cylinderPair_of_bounds` combines 188 uniqueness, 187 canonical-force smoothness, 186 common carriers, 178 all-order datum paths, and the existing mild divergence lemma. It returns the same `U` with every-order `hU`/`hdiv`/angle/Duhamel data and every `C^j_t H^m_x` datum path. The `HasAprioriBoundInv` variant is wired too. `CylinderWiring.lean`, `ATTEMPTS_WIRING_HSOB.md` |
| **A3-S1** | per-order uniform bound | `gronwall_bddAbove_Ico` (§2) | **S** | `A04.gronwall_integral_mul` (`Gronwall.lean:202`) | **DONE this lane** |
| **A3-S2** | same-`T₀` packaging | `higherOrder_bddAbove` (§2): shared `k`,`Kbnd`,`T₀` ⟹ `∀ m≥m₀, BddAbove (y m '' Ico 0 T₀)` | **S** | A3-S1 | **DONE this lane** |
| **A3-S2′** | fixed-driver coupling | `higherOrder_bddAbove_fixedDriverSq`: `k := (y m_drive)²`, `m_drive` **independent of** `m₀` (paper: `m_drive=2`, `k=‖u‖²_{H²}`, eq:criterion `02-prelim:111`) | **S** | A3-S2 | **DONE this lane**. (`higherOrder_bddAbove_lowestOrderSq` also kept, but its `k=(y m₀)²` is the WRONG driver — F6 — a docstring caveat says so) |
| **A2** | eq:Rhigh propagation | consume `A04.energyIdentityHigh`; **do not reprove** | M (=A04 G1) | `A04.inner_energy_Rhigh` (`HighEnergy.lean:136`) | **blocked on A04 `hpr`** (D01 L9(c)/P2); lane 121 concurrent |
| **P4 pressure regularity** | construct a joint smooth Leray-complement representative, equal to `pressureGradientOfVelocity` on `Ioo 0 S` | M | `A01/PressureRegularity.lean`, lanes 169/178/190/192 | **OPEN (lane 189 review fix incomplete)**. Accepted Helmholtz converse retained; rejected `htime`, `ProjectedMomentumDatumOn`, and `hpg_of_slab` removed. Unprojected cylinder residual smoothness and complement-representative regularity are proved. The compatible complement datum paths and interior projected-momentum identification still need to be derived from the cylinder pair. No end-to-end 192 → 190 → 189 → 180 closure is claimed. |
| **A3-M1** | Young reduction | `C·u₂·uₘ·g ≤ ν·g² + (C²/4ν)·u₂²·uₘ²` ⟹ `E' ≤ 2(K·E+b·√E)` | **S** | — | **DONE in A04 = G2 (lane 135)**: `A04.young_high_real` / `A04.young_absorption_high` (`HighContinuation.lean:91,111`), and it *fixes* `Cgron m ν = (Chigh m)²/(4ν)` (`:73`, `Cgron_pos` `:77`). No longer an A01 row — A01 consumes |
| **A3-M2** | derivative → integral step, glued into Grönwall | A3-M1 + ζ↓0 ⟹ the `hstep` A3-S1 consumes; then instantiate `gronwall_bddAbove_Ico`/`higherOrder_bddAbove_fixedDriverSq` on a `ClassicalSolutionR` | **S glue** | `A04.highContinuationIntegral` (lane 138, `HighContinuationIntegral.lean:85`) | **DONE (lane 142)**, module `Section4/A01/GronwallInstance.lean`: `highOrder_bddAbove_of_kbnd` (one order, explicit bound `(‖u(0)‖_{H^m}+‖f‖_{L¹_tH^m})·exp(Cgron m ν·Kbnd)`) and `highOrder_bddAbove_all_orders_of_kbnd` (all orders `m≥3`, one `T₀`, one `Kbnd`, via fixed order-2 driver). `hstep ← highContinuationIntegral` at `t₀:=0` **verbatim** (integrands agree up to β + left-assoc of `*`, **no** `integral_congr`/`ring_nf` — confirms the "same parse, no adapter" prediction); forcing data ← `forceCap_L1`; the single remaining hypothesis is the order-2 cap `hkbnd` (row A3-L1·k). Non-vacuity on `zeroSol` with `Kbnd:=0` (`research/A01/axioms_a3_m2.lean`, 4 decls, 3-axiom); records `research/A01/ATTEMPTS_A3_M2.md`  **Lane 193:** base-order radius route now proved in `AprioriFamily.lean` (base bound, subwindow lowering/uniqueness, H²-cap transfer, explicit `hb_of_base` and Inv). The all-order family remains conditional on the single finite-order energy-envelope input `MildGronwall`; scalar Grönwall is discharged. See `ATTEMPTS_A3_M2_193.md`, `axioms_a3_m2_193.lean`, `REPORT_193.md`.  **Lane 196:** full-word Euclidean norm comparison and regularized metric limit, quadratic regularized word PDE, tame/Young arithmetic, and conditional `mildGronwall`/base-family corollaries in `MildGronwall.lean`. The sole new analytic premise is `FiniteMildEnergy`; its supply and general-data constants remain open. This is not unconditional A3-M2 closure. See `REPORT_196.md` and `ATTEMPTS_MILD_GRONWALL.md`.  **Lane 207 closure:** `finiteMildEnergy'` and `hb_of_base''` discharge the remaining analytic input with explicit cylinder constants. See `REPORT_207.md`; earlier conditional status is historical. |
| **A3-M2** | derivative → integral step, glued into Grönwall | A3-M1 + ζ↓0 ⟹ the `hstep` A3-S1 consumes; then instantiate `gronwall_bddAbove_Ico`/`higherOrder_bddAbove_fixedDriverSq` on a `ClassicalSolutionR` | **S glue** | `A04.highContinuationIntegral` (lane 138, `HighContinuationIntegral.lean:85`) | **DONE (lane 142)**, module `Section4/A01/GronwallInstance.lean`: `highOrder_bddAbove_of_kbnd` (one order, explicit bound `(‖u(0)‖_{H^m}+‖f‖_{L¹_tH^m})·exp(Cgron m ν·Kbnd)`) and `highOrder_bddAbove_all_orders_of_kbnd` (all orders `m≥3`, one `T₀`, one `Kbnd`, via fixed order-2 driver). `hstep ← highContinuationIntegral` at `t₀:=0` **verbatim** (integrands agree up to β + left-assoc of `*`, **no** `integral_congr`/`ring_nf` — confirms the "same parse, no adapter" prediction); forcing data ← `forceCap_L1`; the single remaining hypothesis is the order-2 cap `hkbnd` (row A3-L1·k). Non-vacuity on `zeroSol` with `Kbnd:=0` (`research/A01/axioms_a3_m2.lean`, 4 decls, 3-axiom); records `research/A01/ATTEMPTS_A3_M2.md`  **Lane 193:** base-order radius route now proved in `AprioriFamily.lean` (base bound, subwindow lowering/uniqueness, H²-cap transfer, explicit `hb_of_base` and Inv). The all-order family remains conditional on the single finite-order energy-envelope input `MildGronwall`; scalar Grönwall is discharged. See `ATTEMPTS_A3_M2_193.md`, `axioms_a3_m2_193.lean`, `REPORT_193.md`.  **Lane 196:** full-word Euclidean norm comparison and regularized metric limit, quadratic regularized word PDE, tame/Young arithmetic, and conditional `mildGronwall`/base-family corollaries in `MildGronwall.lean`. The sole new analytic premise is `FiniteMildEnergy`; its supply and general-data constants remain open. This is not unconditional A3-M2 closure. See `REPORT_196.md` and `ATTEMPTS_MILD_GRONWALL.md`.  **Lane 198:** vendor premises and identity/full-word integrated estimate are constructed without an extra analytic input; `finiteMildEnergy_of_estimate` leaves exactly `ForcingFamilyBound` and `EnvelopeConversion` to lane 199. See `REPORT_198.md`.  **Lane 207 closure:** `finiteMildEnergy'` and `hb_of_base''` discharge the remaining analytic input with explicit cylinder constants. See `REPORT_207.md`; earlier conditional status is historical. |
| A3-M2 · premises | Navier–Stokes cylinder mild competitors | full word family through q+1; same window | proved, lane 198 | `MildEnergyPremises.lean` | Solenoidal velocity/transport, Leray-complement pressure, maximal approximation limit, source/pressure restrictions, and integrated root estimate with explicit Z. |
| A3-M2 · forcing bound | quantitative limiting word forcing | Z identification (200); coordinate assembly (202); smooth Leibniz expansion and compatible smooth-to-finite transfer (205) | OPEN: smooth cylinder coordinate tame estimate and uniform constant | `SmoothCylinderCoordinateTame q hq C` → `CylinderCoordinateTame q hq C` → forcing bound with `max (A q) (C/4)` | Conditional only; no unconditional C. Finite-order limit passage proved. See `REPORT_205.md`, `ATTEMPTS_COORDINATE_TAME.md`. **Lane 206 (partial):** genuine Fin 4 log-convex word interpolation, exact low-order-seven times gradient comparison (constant one), and left-oriented mixed-product bound proved in `SmoothTame.lean`. Full smooth coordinate tame estimate and its constant remain OPEN; no invariant transfer or unconditional constructor. This checkout lacks lane 204 SignedPassage. See `REPORT_206.md`, `ATTEMPTS_SMOOTH_TAME.md`. |
| A3-M2 · envelope | everywhere-interior differentiable squared-energy majorant | signed limit and scalar comparison | CONDITIONAL, lanes 199/201 | `MildEnergyEnvelope.lean`, `RootComparison.lean` | Lane 199: exact regularized full-word dissipative identity and explicit scalar ODE envelope. Lane 201 (`RootComparison.lean`): closed-endpoint scalar integral comparison, ODE uniqueness, positive-root Young absorption, zero-root regularization limit, and conditional forcing-bound → root-comparison → finite-energy assembly. ONE solenoidal analytic `CylinderSignedRootLimit` remains: the substantive signed absorbed integrated root inequality for the same maximal-approximation limit and forcing family; this is lane 203's target, not a generic continuity lemma. Assembly additionally needs the explicit algebraic normalization `mildNormConstant q ≤ E`, absent from `ForcingFamilyBound`. No unconditional closure or general-data A. See `REPORT_199.md`, `REPORT_201.md`. |
| A3-M2 · forcing bound | quantitative limiting word forcing | commutator family-norm estimate and word identification | OPEN after lane 199 | `ForcingFamilyBound` | No general-data constants or family-norm bound proved; a signed tensor pairing estimate does not suffice. See `ATTEMPTS_ENVELOPE.md`. |
| A3-M2 · envelope/limit | everywhere-interior differentiable squared-energy majorant | proved signed passage and scalar comparison; forcing bound still required | SIGNED PASSAGE CLOSED, lane 204; finite energy conditional on hFB | `MildEnergyEnvelope.lean`, `RootComparison.lean`, `SignedLimit.lean`, `SignedPassage.lean` | Lane 204 proves the exact imported `CylinderSignedEnergyPassage` without an extra analytic input: finite-level pressure/transport cancellation, the full negative gradient square, closed-interval FTC, uniform roots, strong forcing, and the varying inverse-root weighted dissipation limit for the same U. `cylinderSignedRootLimit_of_forcingBound'` retains the scalar sign condition; `finiteMildEnergy_of_forcingBound''` retains `mildNormConstant q ≤ E` and only hFB. No unconditional forcing-family estimate is claimed. See `REPORT_204.md`, `ATTEMPTS_SIGNED_PASSAGE.md`. |
| A3-M2 · signed regularization | actual finite-order mild competitor | clamped word derivative plus identity-metric integration by parts | PROVED, lane 199 | `regularized_full_energy_hasDerivAt` | Exact coefficient −2ν times the full gradient-square sum in the energy derivative; passage to the signed limit is still open. |
| A3-M2 · forcing bound | quantitative limiting word forcing | Fin 4 mixed products, exact smooth-word identification, Leibniz multiplicities and density | **DONE, lane 207** | `TameAssembly.lean`: `smoothCylinderCoordinateTame`, `cylinderCoordinateTame_unconditional`, `forcingFamilyBound_unconditional` | Explicit C(q) = card(SobolevWord(q+1)) × 2^(q+1) × sobolevEmbeddingConstant 1 3; forcing normalization max(A q, C(q)/4). Both orientations and angular words included; no analytic premise. See `REPORT_207.md`, `ATTEMPTS_TAME_ASSEMBLY.md`. |
| A3-M2 · envelope | everywhere-interior differentiable squared-energy majorant | signed limit and scalar comparison | **DONE, lanes 203/204/207** | `SignedLimit.lean`, `SignedPassage.lean`, `TameAssembly.lean` | `finiteMildEnergy'` and `hb_of_base''` have no analytic input. E(q)=mildNormConstant q; A is the certified enlarged forcing constant. All orders live on the base solution's local horizon. The unconditional local constructor probe chooses that positive horizon, not an arbitrary prescribed time. See `REPORT_207.md`. |
| A3-M2 · signed regularization | actual finite-order mild competitor | clamped word derivative plus identity-metric integration by parts | **DONE, lanes 199/204** | `regularized_full_energy_hasDerivAt` | Exact coefficient −2ν times the full gradient-square sum in the energy derivative; the signed limit with dissipation retained is supplied by `SignedPassage.lean` (restored verbatim in lane 207). |
| A3-M2 · scalar envelope | explicit variation of constants | continuous driver, nonnegative scalar data | PROVED, lane 199 | `comparison_envelope` | x=y², d=2yy′, g=A(16 low)y/(2ν); the target dissipative inequality holds as equality. |
| **A2b-a′** ★ | forced global mild from a-priori bound | `forced_global_mild_of_bound` (see §3): a uniform `‖u‖≤R` on all windows ⟹ the forced `quadraticDuhamel` solution exists on **all** `[0,S]`; **one-line proof term** | **S** | `EulerBoundedMildContinuation.exists_global_mild_of_bound` (`BoundedMildContinuation.lean:39`), `ForcedCylinderLocal.coefficients` (`ForcedCylinderLocal.lean:52`) — both `#check`ed, probe compiles | **DONE (lane 126)**, module `Section4/A01/Continuation.lean` (`forced_global_mild_of_bound`) |
| **A2b-a** = reviewer §3 **A2b-b** | full `exists_local`-shaped continuation | A2b-a′ **+** restore the div-free and angle-invariance clauses across the glue **+** `ordinaryValue` descent to `U : C(Icc 0 S, EulerMeanSolenoidal.L2)` | **M** (was L) | `EulerCorrectionContinuation.correction_mild_divergenceFree` (`CorrectionContinuation.lean:17`), `ForcedCylinderInvariant.exists_local_forced_mild_invariant` (`ForcedCylinderInvariant.lean:30`), `OrdinaryCylinderDescent.{ordinaryValue,ordinaryValue_lift}` (`:56`,`:60`) | **DONE (lane 134)**, module `Section4/A01/ContinuationInvariant.lean`: `restart_window_invariance` (per-window, reviewer probe promoted, `maxHeartbeats 600000`), `exists_uniform_restart_time_invariant`, `gluePath_invariant`, `forced_global_mild_of_bound_invariant` (forked induction), `forced_global_of_bound_unconditional` (= `forced_global_of_bound'`, `hinv` discharged). No global uniqueness; not blocked on C1c; HeliCorgi/`FormalPatched` not needed |
| **A2b-c** (was A2b-b) | cross-order agreement | order-`(q+1)`/`(q′+1)` solutions coincide where both exist | S–M | `A02.uniqueness` (registered; not re-`#check`ed) | open once both orders share a carrier. **Renamed A2b-b→A2b-c** so "A2b-b" matches the reviewer's §3 name for the invariance lane (A2b-a above, done lane 134) |
| **A3-Tm** | order-`m` solution exists on `T₀` | for the shared `T₀`, every order `m` has a solution on `Ico 0 T₀` (so `higherOrder_bddAbove`'s `∀ m` hypothesis can even be stated); `exists_local`'s `T` depends on `q` — no cross-order handle | M | A2b-a′ (bounded ⟹ extends to prescribed `S` at each fixed `q`) | **gap**; `appendix-a:66-67` ("same local interval for every order"); F8. The Grönwall bound is the *tool*, not this statement |
| **A3-L1** | uniform integral caps | `∃ Kbnd, ∀ t∈Ico 0 T₀, ∫₀ᵗ‖u‖²_{H²}≤Kbnd` and `∃ Bbnd, ∀ t, ∫₀ᵗ‖f‖_{H^m}≤Bbnd` | see split rows below | — | see split rows |
| A3-L1·k | order-2 norm comparison | `sobolevNormAt 2 (⇑(U t)) ≤ c · ‖u t‖_{SobolevSpace 1 (q+1)}`, `c` `t`-free, turning `‖u‖≤‖u₀‖+1` into `Kbnd := c²·(‖u₀‖+1)²·T₀` | **M** | `A04.sobolevNormAt` (`Forcing.lean:74`), `A04.intervalIntegrable_highContinuationIntegrand` (`Continuity.lean:132`) | **still M, still blocked — gate only half-lifted.** C1b-m-D is now **closed on the D01 side** (`D01.exists_isSobolevDatum_of_memLp_derivs`, `FiniteOrderConstructor.lean:269`, lane 132/#137). Residual blocker = **row `D-euler-pairing`**: the Euler side must give `HasWeakDerivsL2 (⇑(U t)) 2` (`MemLp 2` + order-≤2 Schwartz-pairing IBP). Until it lands the cap is **vacuous** (`sobolevENorm=⊤⇒sobolevNormAt=0`). `orderZeroDatumCLM` (`DatumPathContinuity.lean:103`) does **not** generalize — raising by `(1+‖ξ‖²)^{1/2}` is unbounded on `L²`, so `c` at order 2 must be a hand-made Plancherel-with-constants bound, not a CLM norm. Last blocker on the A3 chain. **Consumer's exact expected shape (lane 142):** the Grönwall instantiation `GronwallInstance.highOrder_bddAbove_of_kbnd` takes A3-L1·k as the single explicit hypothesis `hkbnd : ∀ t ∈ Ico (0:ℝ) T₀, (∫ s in (0:ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd` (literal order `2:ℝ`, `w.velocity` the classical solution's velocity). A3-L1·k must produce a real `Kbnd` making this hold; the norm comparison + `‖u‖≤‖u₀‖+1` gives `Kbnd := c²·(‖u₀‖+1)²·T₀`. **Lane 145 (`D-quant`) supplies the norm-comparison half.** `D01.norm_isSobolevDatum_le_two` (`FiniteOrderNorm.lean`) proves `‖A‖² ≤ 256·M` for *any* order-2 datum `A` of `⇑(U t)` under the tracked-`L²` hypothesis `HasWeakDerivsL2Bound (⇑(U t)) M 2` (`c₀=1` order-0 + `×16` per raising order; `isSobolevDatum_unique` makes it hold for the specific `A`). With the datum bridge `sobolevNormAt 2 (⇑(U t)) = (sobolevENorm 2 _).toReal = ‖A‖` (this file §"norm cap for t>0"), that reads `sobolevNormAt 2 (⇑(U t)) ≤ 16·√M`. **Residual to close A3-L1·k:** (i) row `D-euler-pairing` to build `HasWeakDerivsL2Bound (⇑(U t)) M 2` with `M` controlled by `‖u t‖²_{SobolevSpace 1 (q+1)}` (making `c := 16·√(M / ‖u t‖²)` the `t`-free constant); (ii) the `sobolevNormAt 2 = ‖A‖` identification for the constructed datum. The unbounded-raising obstruction of `orderZeroDatumCLM` is now moot for the *bound* (raising is controlled by `coord_smul_deriv_ae`, not by a CLM) **Review 145 (F6/F7)**: step (i) needs no new lane — the A04 norm bridge already exists (`A04.Forcing.sobolevENorm_eq`, `Forcing.lean:126`; probe `research/D01/probes/rev145_a3l1k_glue.lean` derives `sobolevNormAt 2 u t ≤ 16·√M` from it plus lane 145). The only residual is the quantitative twin of `EulerPairing.hasWeakDerivsL2_of_cylinder` (lane 140) with `M := ‖u t‖²_{SobolevSpace 1 (q+1)}` and constant 1 (`‖word 1 u hn w‖ ≤ ‖u‖` since the Sobolev space is a submodule of the word-indexed product with the sup norm, and `ordinaryLift` is a linear isometry), giving `c = 16` (m = 2 needs `q ≥ 4`). **CLOSED (lane 147)** — `Section4/A01/OrderTwoCap.lean`. `hasWeakDerivsL2Bound_of_cylinder` re-runs lane 140's descent induction with the tracked bound `M := ‖u‖²` (constant 1); `sobolevENorm_two_toReal_le` gives `(sobolevENorm 2 (⇑U)).toReal ≤ 16·‖u‖` (via `norm_isSobolevDatum_le_two` + `A04.Forcing.sobolevENorm_eq`); `kbnd_of_sup_bound` turns `‖u‖ ≤ R` into `hkbnd` with **`Kbnd := 256·R²·T₀`** — the exact `GronwallInstance.highOrder_bddAbove_of_kbnd` shape (plug-in verified `research/A01/probes/otc_plugin.lean`; integrability free from `continuousOn_sobolevNormAt_velocity` once `v = w.velocity`). `D-euler-pairing` is subsumed (the qualitative pairing already lived in `EulerPairing.lean`; the bound rides its induction). 8 decls 3-axiom (`research/A01/axioms_order_two_cap.lean`), `research/A01/ATTEMPTS_ORDER_TWO_CAP.md`. |
| A3-L1·f | force cap `Bbnd` | `∫₀ᵗ‖f‖_{H^m} ≤ ‖f‖_{L¹_tH^m}` | **S** | `A04.forceSobolevENormL1` (`Forcing.lean:105`), `A04.continuousOn_sobolevNormAt_force` (`Continuity.lean:115`) | **DONE (lane 137)**, module `Section4/A01/ForceCap.lean`: `forceCap` (route-robust cap `∫₀^{T₀}`, feeds Grönwall), `intervalIntegral_le_forceSobolevENormL1` (the row's literal inequality, conditional on `≠⊤`) + `_of_memForceR` (finiteness free via `A04.memL1Hm_of_memForceR`), `forceCap_L1` (bundle with `Bbnd:=‖f‖_{L¹_tH^m}.toReal`), `sobolevNormAt_nonneg`, and an `example` plugging into `gronwall_bddAbove_Ico`. `hfin` in the conditional lemma is **derivable from `hf`** (`memL1Hm_of_memForceR`, review Finding 2), kept only to make the argument visible; the `⊤↦0`-false remark applies to a version that also drops `hf` (counterexample = nonzero *time-independent* `g ∉ F_R`). Non-vacuity now includes the reviewer's **nonzero** bump witness (`research/A01/probes/memForceR_bump_witness.lean`, first nonzero closed `F_R` term). `research/A01/ATTEMPTS_A3_FORCE.md`, axioms `research/A01/axioms_a3_force.lean` (13 decls, 3-axiom) |
| **A3-L2** | choose `T₀`, define `horizon` | with the a-priori bound, `exists_global_mild_of_bound` hands the *whole* prescribed `[0,S]`, so `horizon := S`; no choice over `exists_local`'s `∃ T` | S | A2b-a′ | **DONE (lane 139)**, module `Section4/A01/Horizon.lean`: `HasAprioriBound` (named `hbound`), `horizonOf` (`:= S`) + `horizonOf_eq`, `localTheory_on_prescribed_horizon` (= `forced_global_of_bound_unconditional`, `hbound` named, `T` fixed to `S`, no `∃ T`), `exists_local_shape_of_aprioriBound` (the `∃ T` shape with witness `T := S`, bound `‖u‖ ≤ R`). Supplying `HasAprioriBound` remains A3's job (A3-M2 + A3-L1·k). `research/A01/axioms_a3_l2.lean`: 5 decls, standard 3 axioms |
| **H1** | `horizon_lower_bound` | `∀ ν>0, ∀ K≠⊤, ∃ δ>0, ∀ a f, a∈X_R→f∈F_R→‖a‖_{H¹}≤K→‖f‖_{L¹H¹}≤K→ δ≤horizon ν a f` (quantifier order: `δ` before `(a,f)` — A02 `restart`'s "whole point") | M | **lead:** `EulerUniformHeatLocal.exists_uniform_restart_time` (`UniformHeatLocal.lean:29`) — `δ` depends only on `R` and the `Coefficients`, uniform over restart points | **gap**; `appendix-a:148-152`. The tree lead uses order-`q+1` cylinder `‖u₀‖≤R`, not `‖a‖_{H¹}` — a **candidate, not literally H1** |
| **T1** | `C^j_tH^k_x` all `j,k` | `∂ₜu = νΔu + P(f−∇·(u⊗u)) ∈ C_tH^k`, induct; one-sided at 0 | M | A3 (all-order `T₀`), E1 (`ConvectionDivergence.lean`, DONE) | **gap**; `appendix-a:71-76` |

**Proved in Lean now:** A3-S1, A3-S2, A3-S2′ (lane 122; four theorems).  **A3-M2 DONE
(lane 142)** in `Section4/A01/GronwallInstance.lean` (`highOrder_bddAbove_of_kbnd`,
`highOrder_bddAbove_all_orders_of_kbnd`): the Grönwall skeleton instantiated slot-by-slot on a
`ClassicalSolutionR` (`hstep ← highContinuationIntegral` at `t₀:=0`, no adapter), leaving the
order-2 cap `hkbnd` (A3-L1·k) as the single hole.  **A3-L1·f DONE
(lane 137)** in `Section4/A01/ForceCap.lean` (the forcing cap `Bbnd`, both the route-robust and
the manuscript-literal L¹ forms).  A2b-a′
**DONE (lane 126)** in `Section4/A01/Continuation.lean`; A2b-a (= reviewer §3 A2b-b,
the full `exists_local`-shaped continuation with div-free/invariance/descent restored)
**DONE (lane 134)** in `Section4/A01/ContinuationInvariant.lean` —
`forced_global_of_bound_unconditional` gives the full local shape on `[0,S]` from `hbound`
alone (`hinv` discharged).  **A3-L2 DONE (lane 139)** in `Section4/A01/Horizon.lean`:
`HasAprioriBound` names the `hbound` predicate and `localTheory_on_prescribed_horizon` /
`exists_local_shape_of_aprioriBound` package the `horizon := S` content; supplying
`HasAprioriBound` is still A3's job (A3-M2 + A3-L1·k).

---

## 2. The Lean-ready statements proved this lane (`Section4/A01/Propagation.lean`)

Four theorems, `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all
(`research/A01/axioms_a3.lean`):

* `gronwall_bddAbove_Ico` — per-order uniform bound on `[0,T₀)` (§0 step 4).
* `higherOrder_bddAbove` — `∀ m ≥ m₀, BddAbove (y m '' Ico 0 T₀)`, one shared `T₀`.
* `higherOrder_bddAbove_fixedDriverSq` — coupling `k := (y m_drive)²`, `m_drive`
  independent of `m₀` (the manuscript's fixed-order-2 driver; F6).
* `higherOrder_bddAbove_lowestOrderSq` — coupling `k := (y m₀)²` (kept, but the
  wrong driver for this route; docstring caveat).

---

## 3. The four questions the brief asks (revised after F5–F9)

### (a) `exists_local` output ⇄ A04 Grönwall machinery — interface and orders

`exists_local` (`OrdinaryForcedLocal.lean:32`, `#check`ed): for `q ≥ 6` produces
`T>0`, `T≤S`, `u : C(Icc 0 T, SobolevSpace 1 (q+1))`, ordinary
`U : C(Icc 0 T, EulerMeanSolenoidal.L2)`, `U 0 = a.toLp`, forced mild eq,
div-free, angle-invariant, with the single quantitative clause `‖u‖ ≤ ‖u₀‖+1` in
the **fixed-order** `q+1` cylinder sup-norm.  A04's Grönwall lives on the D01
datum carrier (`sobolevNormAt`, `Forcing.lean:74`).  The bridges:

* **Initial datum, all orders — ready, not C1b-blocked.**  119's row
  **C1b-c5-all** (per lane-122 review F7; 119's `C1B_SPLIT.md` merged into
  integration but is *absent from this worktree*, base `6801945`) is *ready*: from
  `a : SmoothL2Field`, `D01/SmoothDatum.lean:278 smoothAngularDatum_isSobolevDatum`
  gives the order-`m` initial datum at **every** order.  And `hy0 : 0 ≤ y_m 0`
  needs **no bridge at all**: `sobolevNormAt s u t = (sobolevENorm s _).toReal`
  (`Forcing.lean:74`), so it is `ENNReal.toReal_nonneg` (revision-1 §3a wrongly
  said this needs the order-0 bridge — F7).
* **Order-2 norm cap for `t>0`.**  What A3-L1·k needs is a *one-directional norm
  comparison* `sobolevNormAt 2 (⇑(U t)) ≤ c·‖u t‖_{SobolevSpace 1 (q+1)}`, to turn
  `‖u‖≤‖u₀‖+1` into `Kbnd`.  **This is NOT a C1b row** — 119 explicitly disclaims
  the Euler-`SobolevSpace`↔D01-datum norm *identity* (they are equivalent with
  `m`-dependent constants, and `ClassicalSolutionR.sobolev` asks for datum
  existence + continuity, not a norm identity, F7).  A04 already supplies the
  *continuity* (`continuousOn_sobolevNormAt_velocity`, `:105`) and
  *interval-integrability* (`intervalIntegrable_highContinuationIntegrand`,
  `:132`) of these norms; only the cap *value* is missing, and it is additionally
  gated by 119's **C1b-m-D** (the missing D01 finite-order datum constructor,
  which 119's reviewer flags as C1b's real blocker).
  **Lane 145 (`D-quant`) now proves the norm-comparison inequality on the datum
  side:** `D01.norm_isSobolevDatum_le_two` gives `‖A‖² ≤ 256·M` for the order-2
  datum `A` of `⇑(U t)` under `HasWeakDerivsL2Bound (⇑(U t)) M 2`, i.e. exactly the
  `sobolevNormAt 2 (⇑(U t)) = ‖A‖ ≤ 16·√M` half of the cap.  The **one remaining
  input** is `M ≲ ‖u t‖²_{SobolevSpace 1 (q+1)}` with a `t`-free constant, which is
  where the Euler side (row `D-euler-pairing`, an order-≤2 Schwartz-pairing / `H^{q+1}`
  bound on `⇑(U t)`) must land — this is the last blocker, C1b-m-D itself being
  closed (lane 132) and now made quantitative (lane 145).

So A04's Grönwall runs entirely on `ClassicalSolutionR`; A01's work is producing
that structure from `U` (B1/B2) and the order-2 cap (A3-L1·k), **not** a C1b norm
identity.

### (b) The continuation argument A2b in Lean terms — **corrected (F5)**

The revision-1 claim "OpenAI/local layer has no forced-path continuation" was
**false**.  The vendored package has, on exactly `exists_local`'s carrier and
`Coefficients` bundle:

| declaration | file:line | content |
|---|---|---|
| `EulerBoundedMildContinuation.exists_global_mild_of_bound` | `BoundedMildContinuation.lean:39` | a uniform `‖u‖≤R` on every window ⟹ the forced `quadraticDuhamel` solution exists on **all** `[0,S]` with `‖u‖≤R` |
| `EulerCorrectionContinuation.exists_global_correction_of_bound` | `CorrectionContinuation.lean:32` | same, zero-initial correction, **plus** the div-free clause (`correction_mild_divergenceFree`, `:17`) |
| `EulerUniformHeatLocal.exists_uniform_restart_time` | `UniformHeatLocal.lean:29` | `∃ δ>0, δ≤S` depending only on `R` and the `Coefficients`, restart from any `‖u₀‖≤R` |

Composability with `ForcedCylinderLocal.coefficients 1 hq (sobolevPath F hF q)` —
the same bundle `exists_local` feeds to `quadraticDuhamel` — is a **one-line proof
term**, verified this round: `research/A01/probes/a2b_continuation_probe.lean`
(`probe_forced_global_mild_of_bound`, compiles, standard 3 axioms).

Consequences: A2b-a is **S–M, not L, not blocked on C1c**; HeliCorgi /
`FormalPatched.R3MildContinuation` is **not needed**.  A3-L2 collapses
(`horizon := S`).  `exists_uniform_restart_time` is the **first real lead for
H1** (its `δ` is uniform over restarts) — but it is stated with `‖u₀‖≤R` in the
order-`q+1` cylinder norm, whereas H1 wants dependence on `‖a‖_{H¹}`,
`‖f‖_{L¹H¹}` only, so it is a candidate, not a solution.

The `hbound` hypothesis (all windows, all solutions bounded) is genuine — it is
exactly what A3-S1 (the Grönwall bound) plus the order-2 norm comparison (A3-L1·k)
supply.  So A2b-a is "apply an existing theorem", not "build an L".

Everything else in the revision-1 §3b holds: `ElapsedTimePathGluing.join_extend`
(path concatenation), `LocalizedBlowup.no_continuous_continuation` (Section-3,
opposite direction), the inviscid Theorem-1.1 maximal stack are all irrelevant to
forced continuation.  The revision-1 error was one of omission of the one file
that mattered.

**Cross-order agreement** (A2b-c): `A02.uniqueness` pins the two orders where both
exist — S–M bookkeeping.

### (c) The constant `C_{m,ν}` and its `T₀`-independence — **with §3c overstatement removed (F9)**

`C_{m,ν} = C_m²/(4ν)` after Young, `C_m = A03.outerTameConst m` (the tame-product
constant, order + embedding only).  **At the type level** it cannot depend on `T₀`:
`A03.outerTameConst : ℕ → ℝ`, A04's `Chigh : ℕ → ℝ`, `Cgron : ℕ → ℝ → ℝ` (`m`, `ν`)
— no interval argument (F12).  In `Propagation.lean`, `Cgron`/`C m` appear only
multiplied by `k` and inside `exp`, never as a function of `T₀`/`t`, so the bound
`(y_m 0 + Bbnd)·exp(C m·Kbnd)` is a genuine order-`m` constant on the half-open
interval.

**Correction (F9):** the revision-1 closing claim that this "is what makes H1
readable off the same bound" is **too strong** and is withdrawn.  Grönwall
produces an **upper bound on the norms given a horizon**, never a **lower bound
`δ` on the horizon**.  The `δ` of H1 must come from a quantitative lifespan
(manuscript: Tao 5.4(ii) eq. (46) rescaled; in tree:
`exists_uniform_restart_time`), not from the propagation constant.

### (d) Pure-bookkeeping rows

* **A3-S2′ / lowestOrderSq** — specializations of A3-S2; DONE.
* **A3-L2** — **DONE (lane 139)**, `Section4/A01/Horizon.lean`: `HasAprioriBound` names the
  `hbound` predicate; `horizonOf`/`horizonOf_eq` fix the horizon at the prescribed `S`;
  `localTheory_on_prescribed_horizon` (`T` fixed to `S`, no `∃ T`) and
  `exists_local_shape_of_aprioriBound` (the `∃ T` shape, witness `T := S`) package it.  Naming +
  fixing `T := S` only, no new analysis — supplying `HasAprioriBound` remains A3-M2 + A3-L1·k.
* **A2b-c** — an `A02.uniqueness` application.
* **A3-L1·f** — `∫₀ᵗ‖f‖_{H^m} ≤ ‖f‖_{L¹_tH^m}` from `MemForceR`.
* **A2** for A01 — not work: A01 consumes A04's `energyIdentityHigh`.

---

## 3.5 The `gronwall_bddAbove_Ico` instantiation lane (recommended next A01 lane, S)

**DONE (lane 142)** as module `Section4/A01/GronwallInstance.lean` (the brief renamed the
planned `Horizon.lean`).  Its hypothesis list is discharged slot-by-slot, leaving **one** hole:

| Grönwall slot | supplied by | status |
|---|---|---|
| `hCgron : 0 ≤ Cgron` | `A04.Cgron_pos m ν hν |>.le` (135) | **used** |
| `hy0 : 0 ≤ y 0` | `A01.sobolevNormAt_nonneg` (**137**) | **used** |
| `hy`, `hk` continuity | `A04.continuousOn_sobolevNormAt_velocity` (`Continuity.lean:105`), `.pow 2` for `k` | **used** |
| `hknn` | `sq_nonneg` | **used** |
| `hb`, `hbnn`, `hbbnd` | `A01.forceCap_L1` (**137**), `Bbnd := (forceSobolevENormL1 m f).toReal` | **used** |
| `hstep` | `A04.highContinuationIntegral` at `t₀=0` (138) | **used verbatim, no adapter** |
| `hkbnd : ∫₀ᵗ‖u‖²_{H²} ≤ Kbnd` | **A3-L1·k** | **the only hole** (`Kbnd`) — remains |

Exports: `highOrder_bddAbove_of_kbnd` (one order) and `highOrder_bddAbove_all_orders_of_kbnd`
(all `m≥3`, one `T₀`/`Kbnd`).  **`Kbnd` (row A3-L1·k) is the single missing input** to the
per-order uniform bound; its consumer's exact expected shape is the `hkbnd` signature recorded
in the §1 A3-L1·k row.  Remaining order (review §5): **`D-euler-pairing`** (the Euler-side
order-≤2 Schwartz pairing, M — it unblocks A3-L1·k and hence the whole A3 chain) → **A3-L1·k**.

---

## 4. Notes for the lead

* `research/A01/C1B_SPLIT.md` (lane 119) was genuinely **absent at this lane's
  merge-base `6801945`** (the lane-122 review verified this).  119 has since
  merged into integration (`0415366`, PR #121); its rows **C1b-c5-all** (ready),
  **C1b-0**, **C1b-m-D** (the real blocker: missing D01 finite-order datum
  constructor) are cited above via the lane-122 review, not from this worktree.
  Reconcile the A3-L1·k "order-2 norm comparison" row — which is **not** in either
  119's or this table — when both are on one branch.
* `Propagation.lean` is imported by no `Contracts/`/`Bindings/` module, so
  `make test`'s closure does not compile it (only `lake build` does) — not
  CI-covered until a consumer imports it (lane-122 review F1).
* **Superseded by §3.5 (lane-137 review §5).**  A3-M1/M2 gates are **lifted** (M1 = A04 G2,
  done 135; M2 = A04 `highContinuationIntegral`, 138 in review), so the earlier "do not start
  A3-M1/M2" caution is stale.  Recommended order now: **A3-L2** (S, ready) → the
  `gronwall_bddAbove_Ico` instantiation lane §3.5 (S, ready modulo `Kbnd`) → **`D-euler-pairing`**
  (M, unblocks A3-L1·k) → **A3-L1·k** (M).  A3-L1·k is still blocked (C1b-m-D closed D01-side by
  132, but `D-euler-pairing` remains).

> Note (142 review): for `T₀ < T` a `Kbnd` always exists (continuity ⇒ compact-interval bound); row A3-L1·k's real content is the endpoint `T₀ = T` (eq:criterion). Rows still to add before `HasAprioriBound` can be built: converse norm comparison (cylinder ≤ R³), `Ico → Icc` widening, mild ⇒ energy bridge.
>
> **Update (lane 147):** the *arithmetic* of A3-L1·k is now closed (`kbnd_of_sup_bound`, `Kbnd := 256·R²·T₀`). This closes the only gap between an **assumed** sup-bound `‖u‖ ≤ R` and the Grönwall high-order bound; **`HasAprioriBound` additionally needs A2b-a′ / A3-Tm / H1** (`Kbnd` is a function of the very `R` one must establish, and the Grönwall output grows like `exp(Cgron·256R²T₀)`, so this is the *conditional* implication `‖u‖ ≤ R ⇒ explicit R-dependent bound`, not the a-priori bound whose `R` is fixed **before** `T ≤ S` and before `u`). Residual rows to build `HasAprioriBound`, with a.e. slices (F1): (i) carrier bridge / `hslice` — `∀ t : Icc 0 T, (fun x => v (↑t,x)) =ᵐ[volume] ⇑(U t)` from the cylinder pair `(u,U)`, **plus** matching the `ClassicalSolutionR` horizon `T` to the cylinder path's `Icc 0 T` (`exists_local` chooses `T`, a matching obligation); (ii) converse norm comparison `‖u t‖_{H¹_{q+1}} ≤ C·sobolevNormAt (q+1) (⇑(U t))` (`C` `t`-free, order `q+1` not 2); (iii) `Ico 0 T₀ → Icc 0 T` endpoint widening — **splits: `T₀ < T` is cheap (S)** (`continuousOn_sobolevNormAt_velocity` is available at `T₀ ∈ Ico 0 T`), `T₀ = T` is the hard endpoint (142 note's "real content"); **(iv) angle invariance `hinv`** — `HasAprioriBound` (`Horizon.lean:106`) constrains `u` only by the Duhamel equation, but both `exists_local` and this lane need `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t` (unit A2b's `hinv`, tracked elsewhere in this table; once in hand `U` is free via `Continuation.forced_ordinary_descent`). **Cheapest next: (iii) for `T₀ < T`.** Exact statements in `research/A01/ATTEMPTS_ORDER_TWO_CAP.md`.
>
> **Update (lane 149):** rows **(iii)** (`T₀ < T` case) and **(ii)** (converse) are addressed in `Section4/A01/AprioriRows.lean` (`research/A01/ATTEMPTS_APRIORI_ROWS.md`). **(iii) DONE for `T₀ < T`:** `kbnd_of_sup_bound_Icc` widens the cap to the closed window `Icc 0 T₀` (same constant `256·R²·T₀`); `highOrder_bddAbove_of_kbnd_Icc` / `highOrder_bddAbove_all_orders_of_kbnd_Icc` widen the Grönwall conclusion to `Icc 0 T₀` keeping `exp(Cgron·Kbnd)` (input `hkbnd` on the full `Ico 0 T`, restricted along `Icc 0 T₀ ⊆ Ico 0 T`). `T₀ = T` deliberately not attempted (eq:criterion endpoint). **(ii) proved up to one named gap:** the backbone `sobolevSpace_norm_le_of_forall_word` (`‖u‖` = sup over words, `pi_norm_le_iff_of_nonneg`) and the reverse embedding `eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal` (for a smooth `H^{q+1}` slice, `(eLpNorm(iteratedFDeriv n z)).toReal ≤ jetSobolevConst (q+1)·(sobolevENorm (q+1) z).toReal`, via `DatumToJets.jetSobolevENorm_le_sobolevENorm`, explicit `t`-free constant `jetSobolevConst (q+1)`) are **fully proved**; `sobolevSpace_norm_le_sobolevENorm` / `sobolevSpace_norm_le_sobolevNormAt` assemble `‖u‖ ≤ jetSobolevConst (q+1)·sobolevNormAt (q+1) v ↑t` modulo the **single** hypothesis `hword_jet : ∀ n (hn : n ≤ q+1) w, ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal` — the descent-to-classical-jet identity (carrier bridge, row (i)/B1-B2; `SmoothDatum.lean:388` U1b(ii) untouched; also covers the top-order words beyond the descent's 3-order jet reach). **Correction to the naive (ii) statement above:** the converse routes through the smooth velocity **slice** `z = v(t,·)` (`ContDiff`+`H^{q+1}`, free for a `ClassicalSolutionR`), **not** the a.e. representative `⇑(U t)` whose datum the descent reaches only to order `q−2` (`m+3 ≤ q+1`) and for which the `DatumToJets` reverse bound (which needs `ContDiff ℝ ∞`) does not apply; the constant is `jetSobolevConst (q+1)`. **Still needed after 149:** (i) the carrier bridge itself (now also asked to supply `hword_jet`), (iv) `hinv` (untouched — the converse is invariance-free), the `T₀ = T` endpoint of (iii), and the restart spine (A2b-a′/A3-Tm/H1). Exact statements in `research/A01/ATTEMPTS_APRIORI_ROWS.md`.
>
> **Update (lane 149, post-review corrections — `research/A01/REVIEW_APRIORI_ROWS.md` ACCEPT-WITH-NOTES):** applied N1–N5. **N1:** the two Grönwall widenings now take `hkbnd` on an *intermediate* horizon `Ico 0 T₁` (`T₀ < T₁ ≤ T`), so a caller keeps `Kbnd = 256·R²·T₁` (the exponential does not degrade to `256·R²·T`); `T₁ := T` recovers the earlier full-horizon form. Without N1 the two halves of (iii) did not chain (cap on `Icc 0 T₀`, Grönwall consumed `Ico 0 T`). **N3 (endpoint split):** the `T₀ = T` *cap* is now provided (`kbnd_of_sup_bound_Icc_endpoint`, S, same constant `256·R²·T`); only the **Grönwall output** at `t = T` is the hard eq:criterion endpoint (L); and the endpoint the a-priori sup-bound really needs (`‖u‖ ≤ R` on the closed `Icc 0 T`) is **free at the cylinder level** (`u` is a `ContinuousMap`; `rev149_cylinder_endpoint.lean`) — not an energy-side obligation. **N2 (correction of the previous note's "(iv) invariance-free"):** discharging (ii)'s `hword_jet` **does need `hu`** — the words range over `Fin 4`, direction 0 is angular (`standardDirection 0 = (0,1)`), and angular words vanish only under angle invariance (proved, `rev149_angular_words.lean`); only the *proved* part of (ii) is invariance-free. So (iv) is required by (ii) as well. **N5:** `sobolevENorm_congr_ae` + `sobolevSpace_norm_le_sobolevENorm_ordinary` restate the converse on `⇑(U t)` verbatim (energy norm is an a.e. invariant), keeping the smooth-slice proof route. **New residual row (v) — datum/forcing bridge (M–L):** `HasAprioriBound` speaks `a : SmoothL2Field`, `F : Icc 0 S → SmoothL2Field`, while the energy route needs `initialClassR` / `MemForceR f` / `MemL1Hm f` / `HasSmoothSobolevPath`; no A01 module connects `F` to `f`. Row (i) now carries the reviewer's four-part carrier-bridge statement (a.e. descent identity; jet-component bound; angular-words-vanish (proved); L²-level descent of the invariant lift by Fubini). 15 conformance decls, 3-axiom. Exact statements in `research/A01/ATTEMPTS_APRIORI_ROWS.md`.
>

> **Update (lane 151, post-review — `research/A01/REVIEW_CARRIER_WORDS.md` ACCEPT-WITH-NOTES, N1 applied):** row **(i)**'s four-part carrier bridge is closed except piece (d), in `Section4/A01/CarrierWords.lean` (`research/A01/ATTEMPTS_CARRIER_WORDS.md`), 11 decls 3-axiom. **(b) DONE** `eLpNorm_jet_component_le` (jet component at unit vectors `≤ ‖iteratedFDeriv ℝ n z‖`, `ContinuousMultilinearMap.le_opNorm`, `eLpNorm_mono`). **(c) DONE** `word_angular_eq_zero` (port of `rev149_angular_words.lean`; `standardDirection 0 = (0,1)` is `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:6529`) **and generalized** to `word_eq_zero_of_mem_zero` (angular slot in *any* position ⇒ `0`). **(a) DONE** `word_descent_ae_partial` — the descent-to-classical-jet a.e. identity, **PROVED** (review N1: it is *not* an L-level open problem). The descent's complex-Schwartz pairing (`weakDeriv_pairing_of_lift_hasDerivAt`, lane 140) and the smooth field's own pairing (`D01.smoothField_weakDeriv_pairing`, `FiniteOrderConstructor.lean:306`) are cancelled through the tree lemma **`A03.ae_eq_of_schwartz_pairing`** (`Section4/A03/ScalarTameProduct.lean:136`, which takes *complex Schwartz* test functions and does the complex→real / Schwartz→compact conversions internally); `descent_step_ae` (step) + `wordField`/`wordField_field` (`iteratedFDeriv_succ_apply_left`) + induction on the word length (base = `⇑U =ᵐ Z.field`). Smooth slice carried as `Z : SmoothL2Field Space` (free downstream via `D01.exists_smoothL2Field_of_memHInfty`, `DatumToJets.lean:306`). **Assembly `hword_jet_of_descent` now UNCONDITIONAL** for every `w : Fin n → Fin 4` with `n + 3 ≤ q + 1` (`n ≤ q − 2`): from `(u, hu, U, hU, Z, hUz)` — angular words `0` (`word_eq_zero_of_mem_zero`), spatial words by (a)+(b) through `ordinaryLift.norm_map`/`Lp.norm_def`/`eLpNorm_congr_ae`; `.toReal` finiteness free from `Z.integrable` (no `hfin` needed). **Only (d) OPEN (L): the top three orders `n ∈ {q−1, q, q+1}`** — an `L²`-level descent of the invariant lift with no jet loss (`probe151_descent_L2.lean`; route: `AddCircle` Fourier Hilbert basis `Mathlib/Analysis/Fourier/AddCircle.lean:411/:261` killing nonzero modes, `liftMeasure 1 = volume.prod volume` `EulerProof.lean:1092`, then `ordinaryLift_ae`/`ordinaryProjection_measurePreserving`). Net: discharging `hword_jet` for all `n ≤ q − 2` is unconditional; only (d) remains. *(superseded by lane 153 below: (d) is now closed as well.)*
> **Update (lane 153 — piece (d) CLOSED, `Section4/A01/L2Descent.lean`, 4 decls 3-axiom, `research/A01/ATTEMPTS_L2_DESCENT.md`):** row **(i)**'s carrier bridge is now **complete** — the last open piece **(d)** is proved, and `hword_jet` is discharged for **all** `n ≤ q+1` (the top three orders `n ∈ {q−1, q, q+1}` no longer excluded). **(d) DONE** `exists_ordinaryLift_of_invariant : ∀ g : LiftL2 1, (∀ θ, translation 1 (0,θ) g = g) → ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g` — the `L²`-level descent, no jet loss, exactly `DescentL2` of `probe151_descent_L2.lean`. **Route was the averaging / Fubini one, NOT the Fourier one the 151 review sketched:** take the strongly-measurable representative `g₀`, average `G₀ x := ∫ θ, g₀ (x,θ) ∂volume` (`AddCircle 1` mass 1); a.e. angular invariance of `g` transports to `g₀` (`translation_ae` + `measurePreserving_translation`), the quantifier swap `∀ θ, ∀ᵐ x` → `∀ᵐ x, ∀ᵐ θ` is `Measure.ae_ae_comm` (graph measurable by `measurableSet_eq_fun`, `g₀` strongly measurable), and for a.e. `pt` the chain `g₀ pt = ∫ g₀ pt = ∫ g₀(pt+(0,θ)) = ∫ g₀(pt.1, pt.2+θ) = ∫ g₀(pt.1,·) = G₀ pt.1` (`integral_const` prob-measure, `integral_congr_ae`, Haar `integral_add_left_eq_self`) gives `g₀ pt = G₀ pt.1`. Then `⇑g =ᵐ G₀∘fst`; `G₀ ∈ L²(volume)` via `memLp_map_measure_iff` through `ordinaryProjection_measurePreserving` (`map fst (liftMeasure 1) = volume`) + `AEStronglyMeasurable.integral_prod_right'`; `ordinaryLift (toLp G₀) = g` by `ordinaryLift_ae` + `Lp.ext`. **This folds the “angle-invariant `L²` ⇒ a.e. constant” fact into the product argument, so no standalone `AddCircle` Fourier lemma was needed** (the reviewer's `fourierBasis` route is a viable alternative; the averaging route is shorter and Fourier-free). **Word consequence (item 2):** `word_descent_ae_top` (every spatial word of an angle-invariant `u` descends for all `n ≤ q+1` — the word is angle-invariant by the same `congrArg` against `hu` as `exists_descend`'s `hinv`, `sobolevTranslation` acting componentwise by `liftOperator_apply`), `word_descent_ae_full` (the descent-to-jet a.e. identity of `CarrierWords.word_descent_ae` with the `n+3 ≤ q+1` restriction removed — the bound entered only through `exists_descend`, which `word_descent_ae_top` replaces; `descent_step_ae`/`word_hasDerivAt` carry no order bound), and **`hword_jet_full`** — the `hword_jet` bound for **all** `n ≤ q+1`, unconditional. Net: row (i) fully closes lane 149's `hword_jet` (all orders); the remaining A01 residuals are the non-carrier rows ((iv) `hinv`, `T₀=T` endpoint, restart spine (v)), not the carrier bridge.
> **Update (lane 157 — `Section4/A01/SliceWiring.lean`, 6 decls 3-axiom, `research/A01/ATTEMPTS_SLICE_WIRING.md`):** rows **(i)** and **(ii)** are now wired to a genuine `ClassicalSolutionR`, reducing row (i) to a single named constructor. **#1 `Z` (S):** `velocitySliceSmoothL2 w t hST := C01.velocityField w hST t` — **reuse, not duplication**: `C01.velocityField` (`Evolution.lean:115`) already IS the velocity-slice `SmoothL2Field` with `field = fun x => w.velocity (↑t,x)` (unit U1 `velocity_slice_smoothL2`), so only the `_field` rfl is new (LESSONS: do not rebuild a `SmoothL2Field`). **#2 `hfin` (S):** `sobolevENorm_slice_ne_top` — `sobolevENorm (q+1) (w(t,·)) ≠ ⊤` straight from `w.sobolev (q+1)`'s datum (`sobolevENorm_le_of_isSobolevDatum`, no `⊤`-vacuity). **(ii) converse on the real solution:** `sobolevSpace_norm_le_sobolevNormAt_of_solution` — `‖u t‖ ≤ jetSobolevConst (q+1)·sobolevNormAt (q+1) w.velocity ↑t`, i.e. `AprioriRows.sobolevSpace_norm_le_sobolevNormAt` with **all three** remaining hypotheses discharged from `w`: `hz` by `D01.contDiff_slice w.velocity_smooth`, `hfin` by `sobolevENorm_slice_ne_top`, `hword_jet` (all `n ≤ q+1`) by `L2Descent.hword_jet_full` fed `velocitySliceSmoothL2 w t hST` and `(hslice t).symm`. **No named hypothesis left except the carrier hand-off `hslice`.** **#3 (M–L, reduction delivered — no constructor exists):** `grep ClassicalSolutionR Section4/A01` confirms **no A01 module builds a `ClassicalSolutionR` from the cylinder pair** (structure appears only as input), so instead: `isSobolevDatum_ordinary_of_hslice` (hslice carries `w`'s order-`m` datum onto `⇑(U t)`, mirror of lane 140's `exists_isSobolevDatum_m_of_ae`) and **`apriori_rows_of_hslice`** — from `w, (u,U), hslice` **both** rows at once: forward `sobolevNormAt 2 w.velocity ↑t ≤ 16·‖u t‖` (`OrderTwoCap.sobolevNormAt_two_le_of_cylinder`) **and** the converse. So the whole row (i)/(ii) hand-off reduces to the single existence (carrier constructor B1/B2), stated with the `ClassicalSolutionR` horizon `T` **strictly above** the cylinder horizon `S`: `∃ a' f' T (hST : S < T) (w : ClassicalSolutionR ν a' f' T), ∀ t : Icc 0 S, (fun x => w.velocity (↑t,x)) =ᵐ ⇑(U t)` for the `(u,U)` of `exists_local_shape_of_aprioriBound` — "`U` is a.e. the velocity slice of an actual classical solution on a strictly longer horizon". **Still needed after 157:** that single mild ⇒ classical constructor (row (i)/B1-B2), the datum/forcing bridge (v), (iv) `hinv` (carried by the pair; both rows need it via `hword_jet`'s angular words), and the `t = T` Grönwall endpoint (iii-b). *Review 157 corrections: the pair is the output of `localTheory_on_prescribed_horizon` (`Horizon.lean:137`), not `exists_local_shape_of_aprioriBound`; `hinv`/`U`/`hslice` are still owed on the supply side (A3-M2), since the `u` that `HasAprioriBound` quantifies over carries only the Duhamel constraint; the constructor is B1 (L) + B2 (S) over C1b/C1c plus row (v) — L, multi-lane.*
> **Update (lane 167 rework — row (v), `Section4/A01/ForceBridge.lean`, 5 declarations, all standard 3-axiom):** row (v) is now oriented in the direction used by the constructor.  Start with the paper's global `f` and `hf : MemForceR f`; take the canonical carrier `F := C01.forcePath hf`, obtain its required `hF` from `C01.forcePath_jetLp_continuous hf`, retain `f' := f` and the original `hf`, and obtain `A04.MemL1Hm f` from `A04.memL1Hm_of_memForceR hf`.  `forcePath_of_memForceR` packages exactly that canonical `F`, `hF`, and `MemL1Hm` evidence; `forceOfPath_forcePath_eq_on_horizon` proves pointwise agreement with `f` on `Icc 0 S`.  The old carrier-to-global theorems and `ForcePathSmoothness` were deleted: zero extension jumps at `S` for a generic nonzero endpoint and therefore is not even continuous, so it cannot be the constructor's global force.  No dead `hF` premise remains.  The datum half now imports lane 162: `initialClassR_of_smoothL2` consumes the angular-invariance, ordinary-lift, cylinder-divergence, and a.e.-representative hypotheses of `divergence_ae_of_cylinder`, then uses smoothness to upgrade the resulting a.e. coordinate divergence to `A02.IsSolenoidal`.  The conformance file exercises the force bridge with a concrete nonzero compact bump and the datum bridge with an inhabited zero cylinder slice.

> **Update (lane 162 — constructor row c6, `Section4/A01/ConstructorDivergence.lean`, 2 declarations, 3-axiom):** the divergence carrier handoff is now isolated in two layers. **A.e. layer DONE:** `divergence_ae_of_cylinder` takes one cylinder slice `(u,U)`, angle invariance `hu`, descent `ordinaryLift U = value 1 u`, the clause `value 1 u ∈ divergenceFreeSpace 1 1 0`, and a smooth representative `Z.field =ᵐ ⇑U`; it descends the three length-one spatial words with `word_descent_ae_top`, identifies them with the classical coordinate derivatives by `word_descent_ae_full`, and sums the diagonal components to obtain `(∀ᵐ x) ∑ i, (fderiv ℝ Z.field x (coordinateVector i)) i = 0`. The cylinder `divergenceFreeSpace` is the orthogonal complement of the lifted gradient space, so the weak-to-classical zero input is the vendor theorem `EulerClassicalDivergence.divergenceFree_classical_divergence_zero` (HeliCorgi's `r3DecodedFrequency_incompressible_ae_decoder` is the analogous theorem for its separate frequency carrier). **Pointwise c3 handoff DONE conditionally:** `divergence_of_cylinder_pointwise_of_contDiff` takes a family `Z t`, candidate `velocity`, `hslice`, and named per-slice `ContDiff ℝ ∞`; continuity + a.e. equality identifies the slice with `Z t` everywhere and upgrades a.e. divergence zero, yielding verbatim `∀ t ∈ Ico 0 T, ∀ x, spatialDivergence velocity t x = 0`. **Residual:** c6 no longer owes analysis; the constructor must supply the `Z` family/`hslice` and c3 smoothness hypotheses.
> **Update (lane 168 — row (i), unit P3/c4/c9):** `Section4/A01/ConstructorPressure.lean`
> now defines the candidate gradient `G = f - (u·∇)u + νΔu - ∂ₜu` and the fixed-gauge
> radial pressure `pressureOfVelocity`, proves `∇p = G` pointwise from spatial smoothness
> plus `HasSymmetricJacobian G`, proves the order-zero identity
> `datum(∇p) = Leray.lerayComplement 0 (datum(residual))` from the datum-form projected
> equation, supplies the full c9 `MemLp` row, derives c4 from the named joint hypothesis
> `ContDiff ℝ ∞ G`, and derives momentum through `navierStokesResidual_eq_iff_projected`.
> The pointwise identity used for momentum is algebraic from `G = R - ∂ₜu` and
> incompressibility; the genuine mild/Leray projected input is the datum equality above.
> The joint hypothesis is additional global, endpoint-compatible regularity, not implied by
> c3 plus `MemForceR`; B1/T1 must still prove an endpoint-compatible version.
> Remaining supply-side work is B1/T1: transport those named slice/datum/joint hypotheses
> from the mild cylinder pair; no `ClassicalSolutionR` is assumed by the pressure construction.
> **Contract closure:** `ConstructorPressure` is currently in no registered contract closure,
> so `make test` does not compile it; it must join the next registered A01 contract closure.


> **Update (lane 173, P9a): row (iv) closed by route β.**
> `HasAprioriBoundInv` in `AprioriInvariance.lean` (namespace `NSFormalization.Section4.A01`)
> restricts the a-priori-bound quantifier to angle-invariant Duhamel solutions.
> `HasAprioriBound.toInv` proves the old predicate implies the new one;
> `forced_global_mild_core_of_boundInv` re-runs the invariance-carrying continuation
> induction, supplying its existing invariance witness at both uses of the bound.
> `forced_global_of_boundInv` exports the full seven-clause continuation, with a conclusion
> token-identical to `forced_global_of_bound_unconditional`; the thin alias
> `localTheory_on_prescribed_horizon_of_boundInv` has a conclusion token-identical to
> `localTheory_on_prescribed_horizon`. Both include the ordinary L² path, its initial value,
> descent, and divergence freedom. A3 supply can now target the
> restricted predicate and receive `hinv` as a premise. No assertion that every solution
> in the old `HasAprioriBound` scope is invariant; route α was inspected, not proved.
> Other residual rows and the uniform-bound supply remain open as before.
> See `ATTEMPTS_HINV.md`, `axioms_hinv.lean`, and `REPORT_173.md`.
> **Update (lane 179, P9b — row (iii-b)):** `Section4/A01/GronwallEndpoint.lean` closes the **uniform bound on all of `Ico 0 T`**, with the endpoint constant `256·R²·T`, by applying `highOrder_bddAbove_of_kbnd` directly at its horizon `T₀ := T` to `kbnd_of_sup_bound_Icc_endpoint`. It also packages every `m ≥ 3` as `BddAbove` and supplies the finite-`ENNReal` H¹ velocity-bound premise of A04's `restartBeyond` by lowering order three. No bound for the field's value at `T` or energy identity limit is needed for this interpretation. This is conditional on the cylinder sup-bound and carrier/path hypotheses: the `Kbnd(R)` circularity in `HasAprioriBound`, force bounds with a common restart `K`, and A02's uniform restart/constructor supply remain separate. Exact statements, diagnostics and gates: `REPORT_179.md`, `ATTEMPTS_GRONWALL_ENDPOINT.md`.

| 新分项 | 状态 | 交付与范围 |
|---|---|---|
| P4a complement path | 已证（lane 194） | `ComplementPath.lean`：固定物理余项路径，所有 j/m 的闭区间 datum 光滑性，每时刻零阶余项恒等式，任意光滑速度代表元的物理残差 a.e. 桥，以及 190 联合代表元；输入仅 192 cylinder-pair 供给、标准外力和正性。见 `REPORT_194.md`。 |
| P4b interior identity | DONE (195 + assembly 189) | Bounded-evaluation time derivative and datum subtraction on `Ioo 0 S`; lane 197 discharges the projected identity in `pressureSupply_of_pieces`. No endpoint ambient derivative assertion. |
| P4c canonical Leray bridge | DONE (197) | `hprojected_of_cylinder''` and `residualDatum_jointRepresentative` remove projector and residual-agreement hypotheses. |
| P4d Helmholtz converse and assembly | DONE (189) | `pressureSupply_of_pieces`, slice equality transport, L² and symmetric Jacobian on `Ico`; pipeline and zero-pair probes. Lane 180's canonical `PressureSupply` is consumed directly. |

## Lane 180 note — B2 assembly boundary

`ConstructorAssembly.lean` now constructs `ClassicalSolutionR … S` from the
*smooth representative selected by lane 190*, not from the raw pointwise
coercion of `U`. Its representative inputs are
`velocity : SpaceTimeField`, the closed-horizon a.e. identity
`hslice : velocity(t,·) =ᵐ ⇑(U t)`, and
`hc3 : ContDiffOn ℝ ∞ velocity (Ico 0 S ×ˢ univ)`. The pressure is the
radial potential of a separate supplier field `G`, with `G` smooth on the slab
and equal to `pressureGradientOfVelocity ν f velocity` only on `Ioo 0 S`.
This corrects the first three rejected satisfiability attempts: extending a clamped
carrier through `S` is nonsmooth for a non-stationary endpoint; the arbitrary
`Lp` coercion representative need not be continuous; and the ambient
two-sided `fderiv` in `temporalDerivative` gives a generically discontinuous
raw pressure-gradient field at `t=0`.

The fourth rejected attempt quantified suppliers without their production
context.  Lane 190 cannot supply `∀ U, ∃ velocity, ...`: its landed theorem
requires the selected carrier's all-order paths.  The proposed lane-189
supplier for every smooth velocity is actually false, as the nondecaying
constant gradient generated by `velocity(t,x)=t e₀` shows.

The fifth rejected attempt retained only one order-`q` cylinder realization.
That cannot feed lane 194, which specializes the same carrier's family at
order seven and at `max 6 m + 2 + 2*j`, and it also loses the required angular
invariance.  The constructor boundary therefore carries the full `hpairs`
family and specializes at `q` only inside lane 180.

Supplier wiring is now family-preserving.  Lane 192's
`cylinderPair_of_bounds ... hb` selects one `U`, its same-carrier all-order
`hpairs` family, and `hpaths`.  Lane 190 is then called as
`exists_joint_smooth_representative hS U hpaths` to select
`velocity/hslice/hc3`.  Only after both selections does the downstream
194/195/197 pressure pipeline owe the named `PressureSupply`, whose body is
exactly

```lean
∃ G : SpaceTimeField,
  (∀ t ∈ Ioo 0 S, ∀ x,
    G (t,x) = pressureGradientOfVelocity ν f velocity (t,x)) ∧
  ContDiffOn ℝ ∞ G (Ico 0 S ×ˢ univ) ∧
  ∀ t ∈ Ico 0 S,
    MemLp (fun x => G (t,x)) 2 volume ∧
    RadialPotential.HasSymmetricJacobian (fun x => G (t,x))
```

Its arguments expose the full
`hpairs : ∀ p ≥ 6, ∃ u, hU ∧ hdiv ∧ hinv ∧ hduh`, `hpaths`, canonical `a/ha`
and `f/hf`, and `velocity/hslice/hc3`.  `CarrierConstructorFull` specializes
`hpairs q hq` internally; it does not truncate the upstream interface.  The
real cross-lane probe is
`probes/rev180_194_195_197_pressure_supply.lean`, and the former mismatch probe
is now a positive same-family handoff check.  All `ClassicalSolutionR` fields
close without any endpoint use of `pressureGradientOfVelocity`.

The two comparison rows still reach the closed endpoint through continuity of
the cylinder norm and closed-interval datum norm
(`apriori_rows_of_hslice_same_horizon`), without asking for classical
smoothness at `S`. The historical strictly-longer-horizon proposition remains
only as `CarrierConstructorFullClamped` for negative documentation.

## Contract registration

| Lane | Obligation | Status / handoff |
|---|---|---|
| 208 | Identify the actual datum; bridge initialClassR to the smooth solenoidal carrier; total horizon and solution data | DONE: `A01/LocalSolution.lean`, `localHorizon`, `localSolution`; canonical structure conversion checked in `axioms_local_solution.lean` |
| 209 | ManuscriptLocalRegularity, including pressure recovery at zero and gauge, for the same selected solution | Pending; consume lane 208's definitions rather than independently choosing a solution |
| 210 | H¹-uniform horizon_lower_bound | Pending; the chosen H⁷-based existential horizon has no proved H¹-uniform bound; any replacement must coordinate horizon, solution, and regularity |
| 211 | Canonical contract, bindings, tests and registry | Pending 209/210; reuse the existing field-by-field A02-to-contract conversion |

Lane 208 adds no analytic premise and does not claim an inhabitant of the complete
`LocalTheoryAPI`. See `ATTEMPTS_LOCAL_SOLUTION.md` and `REPORT_208.md`.
