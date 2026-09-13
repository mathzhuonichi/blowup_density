# I02 review — `research/I02/Spec.lean` + `COMPARISON.md`

## Verdict: **ACCEPT-WITH-NOTES**

`Spec.lean` typechecks clean, is hygiene-clean, and every field of `CorrectionAPI`
transcribes a claim I located verbatim in Lemma 3.4 (`03-torus.tex:176-216`),
Lemma 3.5 (`:218-243`), or the first two paragraphs of Theorem 4.2's proof
(`04-whole-space.tex:45-51`). **No field is stronger than the paper** in a way not
derivable from the record's own other fields, and **no I02-side fact that `R42`
consumes is missing** (checked against `STATEMENTS.md:270-274` and the two extra
exports of `section4/REVIEW.md:77-88`). The four flagged deviations are all sound;
the residual notes are cosmetic or one-line weakenings and none blocks R42 or R47.

Key positive findings:
* `corrected_background` (`Spec.lean:486-489`) carries the **unchanged** `π`, which
  is exactly the I02 half of the "compact pressure representative"
  (`04:51`, `section4/REVIEW.md:83-86`, `STATEMENTS.md:319` `pressureCompact`).
* `x₀ + εK_* ⊂ B` (`03:105`, clarification C2) is *derivable* from the record:
  `carrier ⊆ plateau`, `θ = 1` on `plateau` ⟹ `carrier ⊆ tsupport θ ⊆ ball 0 R_*`,
  plus `eps_space`. It need not be a separate field.
* The `α(p,q)` endpoint convention is right: `alpha ⊤ ⊤ = -3` (machine-checked).
## Ranked issues

| # | Sev | Field / location | Paper / ledger | What differs | One-line fix |
|---|---|---|---|---|---|
| 1 | Low | `perturbation_divergence_free`, `Spec.lean:494-497` | `03:332` "each summand … divergence free"; `STATEMENTS.md:316` `velDivFree : ∀ t, t < T` | Stated on `Ioo 0 T`; R42's export and the available `LI.inserted_divergence` (`LocalizedInsertion.lean:132`) both use `Ico 0 T`, so `t = 0` is gratuitously dropped | `Ioo (0:ℝ) T` → `Ico (0:ℝ) T` |
| 2 | Low | `correctionStatement`, `Spec.lean:507-524` | — | The closing paren puts `∃ A, …` **inside** the `∀ τ` binder. Logically equivalent (`∀τ,Pτ→Q ↔ (∃τ,Pτ)→Q`), but the indentation reads as if it were top level; the statement also never ties `A.packetQuietTime` to `τ` | Reflow as `(∃ τ > 0, …) → ∃ A, …`, or add `A.packetQuietTime = τ` |
| 3 | Low | citations in several docstrings | `04:08`, `04:32`, `04:51`, `03:332` | Off-by-one / wrong-theorem line refs: `ν,T > 0` is `04:08` (thm:Rmain) not `04:32-33`; `δ > 0` and "any nonempty open ball" are `04:32` not `:33`; the `b_ε` expansion is `04:51` not `:50`; "each summand … divergence free" is `03:332` not `:333` | Renumber the five refs |
| 4 | Low | `COMPARISON.md` `energyConst` row | `InsertionEnergy.lean:88,107,317` | `IE.energyNorm_le_of_squared_bounds` (`:107`) yields only the `L^∞`-`MemLp`; the `gradientL2 ∈ L²` half is `IE.gradientNorm_eq_timeL2` (`:88`), combined at `:317`. Row's "turns the pair into `MemLp … ∧ …`" is imprecise | Name `gradientNorm_eq_timeL2` in that row and in split unit 8 |
| 5 | Low | `COMPARISON.md` split unit 6 | `PhysicalRemoval.lean:77` | `PR.physical_removes` covers only `t ∈ Icc (T−ε²) (T+ε²)`; for `t < t_ε` `correction_cancels` needs the vacuity step (`tsupport U_ε(t) = ∅`, take `O = ∅`). Unit 6 mentions only the openness of `spaceMap ε x₀ '' O` | Add the vacuity step to unit 6 |
| 6 | Trivial | `COMPARISON.md` cites `LI:20` | `LocalizedInsertion.lean:21` | Header at `:20`, hypothesis `hv` at `:21` | — |

## The flagged choices

* **`B := Metric.ball x₀ r`** — consistent, harmless. Every nonempty open ball in
  `ℝ³` *is* `Metric.ball x₀ r`, so `B` is not restricted; the only content is that
  the scaling centre coincides with the ball centre, which the paper leaves free
  (`x₀ ∈ B`, `03:102`). It makes `eps_space` literally C2's
  `εR_* < dist(x₀,∂B)` (`STATEMENTS.md:342-344`). Does not block R42/4.7: `04:306`
  only needs *a* ball with closure inside one cell, and a concentric sub-ball works.
* **`mixedNorm` over all `t ∈ ℝ`** — consistent and strictly stronger. This is
  `CMN.mixedNorm` (`CorrectionMixedNorms.lean:13`, `eLpNorm … q volume` with no
  restriction), verified by `rfl`. It equals the paper's `(0,∞)` norm because of
  `force_positive_time`. R42 wants `(0,∞)`; dominated, so no block.
* **Directional iterated Fréchet derivatives** — faithful. `∂_x^β` is the case
  `u i = coordinateVector (β i)` (norm 1), and this is the exact shape of the two
  existing bounds `CP:291-322` / `CFP:270-296`. Section 4 only ever uses the `m = 0`
  amplitude (`04:68`), so no block.
* **`packet_smooth` / `packet_quiet` (+ `packetQuietTime`, `packet_quiet_pos`)** —
  legitimate, not over-assumption. All four are paper facts
  (`01-introduction.tex:18-19`, `02-preliminaries.tex:152`) and they are exactly the
  hypotheses of `PS.zeroPastField_smoothOn` (`PacketScaling.lean:373`), which is
  what makes `scaledPacket` smooth for `perturbation_divergence_free`.
* **Slab `Ioo 0 (T+δ) ×ˢ univ` vs `Icc`** — consistent; a *weaker* hypothesis than
  "smooth on `[0,T+δ]`" (`03:164`), so a stronger contract. Everything I02 needs sits
  in `(T−2ε², T+2ε²) ⊂ (0,T+δ)` via `eps_time`. No block.

(Read-only pass: `Spec.lean` and `COMPARISON.md` untouched, no git writes.)

## Reuse spot-check (16 rows opened at the cited file:line)

All line numbers **exact**; all domains `Space = EuclideanSpace ℝ (Fin 3)` (`PST:30`),
all measures Lebesgue `volume`; **no declaration below mentions `UnitSpatialPeriodsOn`**
(`PST:47`) or any torus type.

| Cited | Found | Statement as claimed? |
|---|---|---|
| `RP:15` `cross` | yes | yes — coordinate cross product |
| `RP:177` `centeredPotential_eq_integral` | yes | yes, `:= rfl`, `∫ r in 0..1, r • cross (v (x₀+r•(x−x₀))) (x−x₀)` |
| `RP:202` `timePotential` | yes | yes, time-slicewise `centeredPotential` |
| `RP:218` `spatialCurl_timePotential` | yes | yes; hyps `ContDiff ℝ ∞ v` (**global**) + global `hdiv` |
| `CP:135/138/141` `spatialCutoff`/`temporalCutoff`/`physicalCorrection` | yes | yes — `θ(ε⁻¹•(x−x₀))`, `η((ε²)⁻¹(t−T))`, the paper's `θ_ε,η_ε` |
| `CP:291` `physical_mixed_derivative_bound` | yes | yes — `Fin.append` shape, `C * (ε⁻¹)^(2j+m)`, `Ioc 0 1` |
| `PR:56` `physical_support` | yes | yes — literally the draft's `correction_support`, no `v` hypothesis |
| `PR:77` `physical_removes` | yes | yes — germ form on `spaceMap ε x₀ '' O`, `t ∈ Icc (T−ε²) (T+ε²)` |
| `INS:21` `residual` | yes | yes — `∂_t u + (u·∇)u − ν•Δu + ∇p` |
| `INS:92` `correctionForce` | yes | yes — the five summands of `eq:H` |
| `INS:97` `corrected_background` | yes | yes — `residual ν (v+w) p = residual ν v p + correctionForce ν v w` |
| `CMN:13` `mixedNorm` / `:123` `physical_force_mixed_bound` | yes | yes — all `p q : ℝ≥0∞`, bound `ofReal (ε^(−2+3/p+2/q)) * C`, `C < ⊤` |
| `IE:30` `energyNorm` / `:107` `energyNorm_le_of_squared_bounds` | yes | yes; see issue 4 for the `gradientL2` half |
| `CE:54` `physicalCorrection_uniform_energy` | yes | yes — `∫ x, ‖w_ε(t,x)‖² ≤ C ε³`, `∫ x : Space` Lebesgue |
| `LC:14/30` `exists_spatial_cutoff`/`exists_temporal_cutoff` | yes | yes — `ContDiffBump`; temporal instance at `T=0, δ=1` gives the paper's `η` |
| `IF:32` `InsertionFamily.velocity` | yes | yes — `v z + physicalCorrection … + parabolicVelocity ε⁻¹ (T−ε²) x₀ (zeroPastField u)` |
| `TE:49/68` `exists_global_reference_extension` / `…_on` | yes | yes — `:68` builds only `LC.exists_local_background_removal` (`LC:130`), i.e. the **unscaled** `localCorrection v x₀ χ η` |

## Scratch identification results (`/tmp/i02_review_probe.lean`, since deleted)

`lake env lean /tmp/i02_review_probe.lean` → **exit 0**, no output. Six `example`s:

1. `timePotential v x₀ (t,x) = ∫ ρ in 0..1, ρ • cross (v (t, x₀+ρ•(x−x₀))) (x−x₀)` — **`rfl`** ✔
2. `physicalCorrection v x₀ T θ η ε z = −curl (fun y => (temporalCutoff η T ε z.1 * spatialCutoff θ x₀ ε y) • timePotential v x₀ (z.1,y)) z.2` — **`simp only [physicalCorrection, localCorrection, spatialCurl]`** ✔
3. `correctionForce ν v w (t,x) = ∂_t w − ν•Δw + Dv(w) + Dw(v) + (w·∇)w` (`eq:H`) — **`rfl`** ✔
4. `InsertionFamily.velocity U v x₀ T θ η ε z = v z + physicalCorrection … z + scaledPacket U x₀ T ε z` — **`rfl`** ✔
5. `alpha p q + 1 = −2 + 3/p.toReal + 2/q.toReal`, all `p q : ℝ≥0∞` — **`simp only [alpha]; ring`** ✔; `alpha ⊤ ⊤ = −3` — **`simp`** ✔
6. (extra) `mixedNorm p q F = eLpNorm (fun t => …) q volume` — time over all of `ℝ` — **`rfl`** ✔

All four `rfl`/`simp` claims of `COMPARISON.md:81-90` confirmed, plus the `ring` claim
of the `mixedConst` row.

## Gaps list, audited

* **`‖w_ε‖_{E_T} ≤ Cε^{3/2}` absent — CONFIRMED.** `energyNorm` occurs only in
  `InsertionEnergy.lean` (`:30,34,107,112,248,261,316,340,381,394`); no `3/2` rpow
  occurs anywhere in `InsertionEnergy.lean` or `CorrectionEnergy.lean`. The only
  ε-rate energy statement is `IE.insertion_energy_bound` (`:305-366`) for
  `perturbation = u_ε − v` (packet **plus** correction), bounded by
  `√(2(Aε³+Bε)) + √(2(Cε³+Dε))`. Only the two squared halves exist for the pure
  correction: `CE:54` (`∫‖w_ε(t)‖² ≤ Cε³`) and `IE:175` (`gradientSquare T w_ε ≤ Cε³`).
* **Reference-regularity extension is the largest remaining item — CONFIRMED.**
  `hv : ContDiff ℝ ∞ v` (global) at `PR:12,19,77`; `CP:30,41,49,63,83,147,187,201,223,263,291`;
  `CFP:51,57,129,173,185,204,227,270`; `CE:42,54,74,89,108,130,169`;
  `CMN:75,102,123,164,188,202`; `CVN:14,22,42,60,83,106,119,134,155`; `IE:175,327`;
  `LI:21,97,133`. **Zero** `ContDiffOn` occurrences in `PR/CP/CFP/CE/CMN/CVN`. The
  bridge has to be threaded through the whole ε-family chain, which is broader than
  any other unit; the estimate in `COMPARISON.md` §3 is fair.
* **`TimeExtension.lean` covers the unscaled cutoff only — CONFIRMED.**
  `TE.exists_local_background_removal_on` (`:68`) delegates to
  `LC.exists_local_background_removal` (`:130`), which returns
  `localCorrection v x₀ χ η` with `χ` from `exists_spatial_cutoff` and `η` from
  `exists_temporal_cutoff T δ` — **no** `spatialCutoff θ x₀ ε` / `temporalCutoff η T ε`,
  hence no ε-family. `TE.exists_global_reference_extension` (`:49`) is generic and is
  directly usable for split unit 1, as claimed.

## Check log

1. **Typecheck.** `. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/I02/Spec.lean`
   → **exit 0**, **empty output** (0 bytes), ~3 s. Negative control: the same runner on
   `example : (1:Nat) = 2 := rfl` → exit 1 with a type mismatch, so the exit 0 is real.
2. **Hygiene.** `grep -nE "sorry|axiom|admit|native_decide|unsafe" research/I02/Spec.lean`
   → one hit, `:13`, inside the module docstring ("introduces no `axiom`, no `sorry`…").
   Top-level declarations: `alpha` (`:85`), `scaledSpatialCutoff` (`:91`),
   `scaledTemporalCutoff` (`:98`), `scaledPacket` (`:108`), `structure CorrectionAPI`
   (`:140`), `def correctionStatement : Prop` (`:507`). **No `theorem`/`lemma`/`example`
   /`instance`/`opaque`/`partial` anywhere** — the file asserts nothing.
3. **Fidelity.** Every field compared against `03-torus.tex:101-105, 112-118, 130-131,
   163-193, 210-243, 293-296, 321-339` and `04-whole-space.tex:8, 20-29, 31-41, 44-51,
   68, 306`, and against `01-introduction.tex:15-30, 60-67, 138-146` and
   `02-preliminaries.tex:152`. Confirmed present and exact: `2ε² < min(T,δ)`
   (`eps_time` ↔ `03:212`), `εR_* < r` (`eps_space` ↔ `03:212` + `03:105`), supports
   (`03:188-189`, `04:38`), exponents `−2j−m` and `−2−m` (`03:227-230`), `E_T`
   exponent `3/2` (`03:234`), `α(p,q)+1` for all `p,q` incl. `∞` (`03:235-237`),
   unchanged `π` in `corrected_background` (`03:321-325`, `04:51`).
4. **R42 consumption.** All ten I02 sub-claims of `STATEMENTS.md:270-274` present; both
   extra exports of `section4/REVIEW.md:77-88` covered (`perturbation_divergence_free`,
   modulo issue 1; and `corrected_background`'s unchanged `π`). `forceDiff`
   (`g_ε−g ∈ C_c^∞(B×(0,∞))`, `04:38`) follows from `force_smooth` +
   `force_compactSupport` + `force_support_ball` + `force_positive_time`.
5. **Reuse spot-check** — 16 rows above (target 10); every cited line number exact.
6. **Scratch probe** — six identifications, exit 0; `/tmp/i02_review_probe.lean` deleted.
