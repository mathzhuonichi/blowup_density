# ATTEMPTS — lane 150-C01-e4-assembly (row E4 + row energyIdentity)

Module delivered: `formalization/NSFormalization/Section4/C01/EnergyDerivative.lean`
(namespace `NSFormalization.Section4.C01`).  Axiom audit: `research/C01/axioms_e4.lean` — all
5 declarations `[propext, Classical.choice, Quot.sound]`, plus two non-vacuity `example`s on
`A04.zeroSol 1 2` (row E4 window `[1/2,1] ⊂ (0,2)` at interior point `1/4`; row
energyIdentity at interior time `1`).

## Result summary (both rows DONE)

* `energyDerivative_hasDerivAt (w hf) (hc : 0 < c) (hcS : c ≤ S) (hST : S < T) {r}
  (hr : r ∈ Ioo 0 (S − c))` — the exact statement review 148 §4 prescribed and the `hd`
  slot of `energyIdentity_classical` (`MomentumCarrierB.lean:254`): the `L²` energy of the
  velocity, re-indexed by the `+c` shift and clamped to `[0,S]`, is differentiable at every
  interior `r`, derivative `2⟪u(r+c,·), ∂ₜu(r+c,·)⟫_{L²}`.
* `energyIdentity_classical_unconditional (w hf) {t} (ht : t ∈ Ioo 0 T)` — the raw-integral
  energy identity as a genuine `HasDerivAt` at every interior time:
  `d/dt ‖u(s,·)‖²_{L²} = −2ν·∫∑ᵢ‖fderiv u(t,·)·(axis i)‖² + 2·∫⟪u(t,·), f(t,·)⟫` at `t`,
  the energy presented as `s ↦ ‖(velocityField w _ (projIcc 0 ((t+T)/2) _ s)).toLp‖²`.

Supporting (all std 3 axioms): `wordEnergy_zero`, `wordInner_sum_zero`,
`velocity_hasDerivAt_time`.

## What closed, and how

### Item 1 — window translation
`T' := S − c`, `hT' := sub_nonneg.mpr hcS`.  Two continuous shifts:
`ιvel : Icc 0 (S−c) → Icc 0 S`, `σ : Icc 0 (S−c) → Icc c S`, both `r ↦ ⟨r.1 + c, _⟩`,
continuity `(continuous_subtype_val.add continuous_const).subtype_mk _`.  `A := velocityField
w hST ∘ ιvel`, `B r := temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ r).2)`.
`hA := (velocityField_jetLp_continuous w hST n).comp hιvel`,
`hB := (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ`.

### Item 2 — the pointwise `hd`
`velocity_hasDerivAt_time w (hs : s ∈ Ioo 0 T) x : HasDerivAt (fun ρ => w.velocity (ρ,x))
(temporalDerivative w.velocity s x) s`, re-proved **unconditionally** by mirroring the `hvelx`
block of `A04.timeDeriv_isSobolevDatum` (`TimeDerivative.lean:194-205`) with its `2 ≤ m` /
`ContDiffOn G` baggage dropped — just `w.velocity_smooth.comp (contDiff_id.prodMk
contDiff_const).contDiffOn hsub` → `.differentiableOn … |>.hasDerivAt`.  The value
`deriv (fun r => w.velocity (r,x)) s` produced by `.hasDerivAt` is **defeq** to
`temporalDerivative w.velocity s x` (both `fderiv ℝ (fun s' => w.velocity (s',x)) s 1`), so
`exact` closes with the `temporalDerivative` spelling.

The `hd` clause: at interior `t`, chain-rule `∂ₜ(u(ρ+c,·))` via `velocity_hasDerivAt_time` at
`t+c`, then the `+c` shift `(hasDerivAt_id t).add_const c`; the `projIcc` clamp is undone by
`congr_of_eventuallyEq` on `Ioo 0 T' ∈ 𝓝 t` (`projIcc_of_mem`).  `(B ⟨t,…⟩).field x =
temporalDerivative w.velocity (t+c) x` is defeq via `temporalSliceField_field`, so the value
matches.

### Item 3 — the `s = 0` word bridge
No `wordEnergy_zero` in the vendor (confirmed N3).  Two local lemmas, each one line:
`wordEnergy_zero A : wordEnergy 0 A = ‖A.toLp‖²` by `simp [wordEnergy, wordField_zero]`;
`wordInner_sum_zero X Y : (∑ n ∈ range 1, ∑ w:Fin n→Fin 3, ⟪(wordField X w).toLp,
(wordField Y w).toLp⟫) = ⟪X.toLp, Y.toLp⟫` by `simp [wordField_zero]` (`simp` collapses the
singleton `Fin 0 → Fin 3` `univ` sum on its own).

### Item 4 — assembly
`wordEnergy_hasDerivWithinAt (S−c) hT' A B hA hB hd 0 ⟨r, hr.1.le, hr.2.le⟩`, then
`simp only [Nat.zero_add, wordEnergy_zero, wordInner_sum_zero]` (the `Nat.zero_add` is
required — the vendor value is over `range (0+1)`, not `range 1`), then
`HasDerivWithinAt.hasDerivAt (Icc_mem_nhds hr.1 hr.2)`.  The item-6 `rfl` check **held**:
`A ⟨r,_⟩.toLp` is defeq `velocitySliceField w _.toLp` (both `SmoothL2Field` with `field =
fun x => w.velocity (r+c, x)` up to a proof-irrelevant `Icc 0 S` witness; no `jetLp_congr` /
`toLp` bridge was needed).

### Item 5 — hand-off (raw energy at the raw interior time)
Choose `c := t/2`, `S := (t+T)/2` (so `S − c = T/2`) and instantiate item 4 at `r := t − t/2`
(so `unshift t = t − c` lines up).  `hg.comp t ((hasDerivAt_id t).sub_const (t/2))` transports
the point `t − c ↦ t` (here the energy is `ℝ`-valued, so ordinary `.comp` with `*1`).  The
value's slice times `(t − t/2) + t/2` are rewritten to `t` by `field_ext (simp only
[velocitySliceField_field, harith])` (`harith : (t−t/2)+t/2 = t` by `ring`) for both
`velocitySliceField` and `temporalSliceField`; then `energyIdentity_classical w hf ht … rfl`
turns `2⟪u,∂ₜu⟫` into the raw integrals; finally `congr_of_eventuallyEq` identifies the raw
clamped energy with the shifted energy near `t` (both `projIcc`s are the identity there,
`(s−t/2)+t/2 = s` by `ring` inside a `Subtype.ext`).

**Form of the value:** raw-integral vocabulary of `energyIdentity_classical`
(`∫ x, ∑ i, ‖fderiv ℝ u.field x (axis i)‖²` and `∫ x, ⟪u.field x, f.field x⟫`).  The one
remaining bridge to `research/C01/Spec.lean`'s `energyIdentity` (contract :344) is the
`gradientSq`/`pairing`/`l2Sq` vocabulary step (`PiLp.norm_sq_eq_of_L2`, per `REVIEW_E3E4.md` /
row E2) — a `verification`-side Bindings lane, since `gradientSq`/`gradientTensor` are
`Contracts.V1` objects that `formalization/` cannot import.

## Failed / discarded approaches (with the exact error text)

* **`HasDerivAt.comp` for the velocity chain rule** (item 2's `hd`) — the velocity is
  `Space = EuclideanSpace ℝ (Fin 3)`-valued, so the `g' * h'` `comp` does not typecheck.
  Error: `Application type mismatch … HasDerivAt.comp t hbase … expected HasDerivAt ?m ?m
  (t+c)`.  Fix: `HasDerivAt.scomp` (scalar-then-vector, derivative `h' • g'`), value cleaned
  with `one_smul`.

* **Explicitly typing the composed step**
  `have hcomp : HasDerivAt (fun ρ => w.velocity (ρ+c,x)) (…) t := simpa … using hbase.scomp …`
  — this pins the `Space` normed-group instance to `WithLp.instAddCommGroup`, while `scomp`
  delivers the `PiLp.normedAddCommGroup …` path; `simpa` then fails with a `Type mismatch`
  between the two `@HasDerivAt … (WithLp.instAddCommGroup …)` vs `(PiLp.normedAddCommGroup …)`
  instance diamonds.  Fix: **never state an intermediate `Space`-valued `HasDerivAt` type
  explicitly** — keep the `scomp` result as-is (its `∘` form) and hand it to
  `congr_of_eventuallyEq` with the eventuallyEq's RHS written as
  `(fun ρ => w.velocity (ρ,x)) ∘ (fun ρ => ρ + c)`.

* **`⟪…⟫_ℝ` notation** — not in scope under `open scoped RealInnerProductSpace` (that gives the
  bare `⟪…⟫`); `⟪…⟫_ℝ` errored `unexpected identifier; expected ')'`.  The bare `⟪…⟫` is
  `inner ℝ` and matches both the vendor value and `energyIdentity_classical`.

* **`simp only [wordEnergy_zero, wordInner_sum_zero]` without `Nat.zero_add`** — the vendor
  value is `2 * ∑ n ∈ range (0+1), …`, and `wordInner_sum_zero` (stated over `range 1`) does
  not fire (`simp` reported the arg unused); the final `exact` then failed with the sum not
  collapsed.  Fix: prepend `Nat.zero_add` so `range (0+1) → range 1`.

* **Re-stating item 4's function with a placeholder membership `⟨…, _⟩`** in the item-5
  eventuallyEq — `error: don't know how to synthesize placeholder for argument property`.
  Fix: do not re-state the shifted function; hand `hcomp` to `congr_of_eventuallyEq` and reduce
  the pointwise goal with `congrArg (fun z => ‖z.toLp‖²)` then `congrArg (velocityField w hST)
  (Subtype.ext …)`, so the membership proofs stay elaborated inside `hcomp`.

* **Rewriting the value's slice time with `rw [sub_add_cancel] at hE`** (an earlier item-5
  draft) — dependent-rewrite motive failure was expected, so it was never used; instead the
  time was moved with `field_ext` on a plain field equation (`simp only
  [velocitySliceField_field, harith]`), which has no dependent-proof subject.

## Commands run

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.EnergyDerivative` | exit 0, `Built … EnergyDerivative`, `Build completed successfully (10302 jobs)`; no `Section4`/module warning |
| `lake env lean …/EnergyDerivative.lean` | exit 0, **0 bytes** |
| `lake env lean ../research/C01/axioms_e4.lean` | exit 0; 5/5 `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` examples elaborate silently |
| `grep -nE 'sorry|admit|native_decide|maxHeartbeats|^\s*axiom ' EnergyDerivative.lean axioms_e4.lean` | no output; also `grep set_option` empty |
| `make check` | exit 0 (13 contract-policy tests OK; 30 work items consistent) |

Standalone reproduction of item 4: `research/C01/probes/e4_probe2.lean` (imports
`PressureJetPath`, redeclares the theorems locally; `lake env lean` exit 0 / 0 bytes).  The
item-5 draft probe was folded into the module and removed (it re-declared a name the module
now exports).
