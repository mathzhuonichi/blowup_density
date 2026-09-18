# Lane 409-T22-UB3-cutoff-datum — report (Opus continuation)

Replaces the lane's first (codex) report, which delivered no theorem; that text is kept
verbatim at the bottom under "Superseded".

## 1. What was proved

Both U-B3 targets, in `formalization/NSFormalization/Section3/T22/CutoffDatum.lean`
(namespace `NSFormalization.Section3.T22`), with no named input and no extra axiom.

**(a) Existence of a smooth cutoff.**

```lean
theorem exists_cutoff {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1)
```

The "`χ = 1` near `K`" clause is the filter form `∀ᶠ x in 𝓝ˢ K, χ x = 1`. The explicit
open-set form the brief also allowed is available as

```lean
theorem exists_cutoff_isOpen {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∃ V : Set Space, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1
```

so U-Z1 can use whichever spelling it prefers.

**(b) The cutoff datum realizes the zero extension.**

```lean
theorem isCutoffDatum_realizes_zeroExtension {Ω K : Set Space} {s : ℝ} {χ : Space → ℝ}
    {z : SpatialField} {A B : RealVectorSobolev s}
    (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ1 : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    (hcut : IsCutoffDatum s χ A B)
    (hA : restrictDatum Ω s A = restrictField Ω z)
    (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    IsSobolevDatum s (zeroExtension Ω z) B
```

Two deviations from the brief's sketch of (b), both in the caller's favour:

* `HasCompactSupport χ` is **required** (the brief's signature omitted it). Without it
  `χ·ψ` need not have compact support, hence is not a `DomainTest Ω`, and the hypothesis
  `hA` cannot be applied. (a) supplies it, so U-Z1 pays nothing.
* `IsOpen Ω` and `K ⊆ Ω` are **not** required. The pointwise identity behind the proof
  holds at every point of `Space`, not just on `Ω`, so no measurability of `Ω` enters.

Routes (details in `research/T22/ATTEMPTS_UB3.md`):

* (a) = Mathlib smooth Urysohn in model-space form. `exists_compact_between` produces a
  compact `L` with `K ⊆ interior L ⊆ L ⊆ Ω`; `exists_contMDiffMap_one_nhds_of_subset_interior`
  with `I := 𝓘(ℝ, Space)`, `M := Space`, `n := ⊤` produces the function; `contMDiff_iff_contDiff`
  converts `ContMDiff` back to `ContDiff ℝ ∞`; `support ⊆ L` gives `tsupport ⊆ L ⊆ Ω` and
  compact support.
* (b) = `HasCompactSupport.hasTemperateGrowth` + `SchwartzMap.smulLeftCLM_apply_apply` (so the
  `IsCutoffDatum` graph really is pointwise multiplication — this discharges risk 5 in
  `T22_SPLIT.md §3`), then the pointwise identity `(χψ) x · z x i = ψ x · (E₀z) x i`, valid at
  every `x` by a three-way case split on `x ∈ tsupport (E₀z)` / `x ∈ Ω`, closed with
  `setIntegral_eq_integral_of_forall_compl_eq_zero` and `integral_congr_ae`.

## 2. What exists in Lean now

* `formalization/NSFormalization/Section3/T22/CutoffDatum.lean` (new, 161 lines): the three
  theorems above. Imports only `NSFormalization.Section3.T22.Domain` and
  `Mathlib.Geometry.Manifold.PartitionOfUnity`. No existing module was edited.
* `research/T22/probes/cutoff_datum_closes.lean` (rewritten): instantiates (a) and
  `exists_cutoff_isOpen` on `Ω = ball 0 1`, `K = closedBall 0 (1/2)`; feeds the cutoff chosen
  from (a) into (b) at that concrete geometry; and closes a non-vacuous instance of (b)
  (the zero field, `IsCutoffDatum s χ 0 0`, giving `IsSobolevDatum s (zeroExtension Ω 0) 0`).
* `research/T22/axioms_ub3.lean` (rewritten): `#print axioms` for all three theorems.
* `research/T22/ATTEMPTS_UB3.md`, this report, and the `T22_SPLIT.md` U-B3 status line, all
  rewritten (codex text kept as "superseded").

## 3. Gap

* U-B3 itself has no residual: both targets are closed, nothing is assumed, nothing is
  `sorry`-ed.
* Handover facts U-Z1 must respect: (b) needs `HasCompactSupport χ` in addition to the
  brief's listed hypotheses; and the `K` in (b) is only a support container for `E₀z` and
  the set near which `χ = 1` — it is *not* required to sit inside `Ω`, so U-Z1 can reuse
  the same `K` from `zeroExtensionComparison` without an extra side condition.
* `exists_cutoff` pulls `Mathlib.Geometry.Manifold.PartitionOfUnity` into the T22 import
  closure. It is a pure-Mathlib import (no vendor code, no warnings), and the module builds
  in 2.7 s on the prebuilt closure, but anyone assembling U-REG's `Tests` module should know
  the manifold library is now transitively imported.
* The lane's first (codex) claims are contradicted by the build: `exists_smooth_tsupport_subset`
  and `exists_contDiff_one_nhds_of_subset` are indeed not identifiers under this pin, but the
  renamed vector-space bump API (`exists_contDiff_tsupport_subset`,
  `IsOpen.exists_contDiff_support_eq`) exists and, more importantly, is not what (a) needs;
  and there is no missing "zero-extension pairing bridge" — `IsSobolevDatum` unfolds to the
  pairing directly.

## 4. Commands run and results

All from the worktree, `. scripts/lean-env.sh` first, `lake` from `verification/`.

| command | result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.Domain NSFormalization.Section3.T22.RestrictBridge NSFormalization.Section3.T22.OrderZero` | `Build completed successfully (9931 jobs).` (the closure the codex run never built) |
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffDatum` | `✔ [9874/9874] Built NSFormalization.Section3.T22.CutoffDatum (2.7s)` / `Build completed successfully (9874 jobs).` — 0 errors |
| `lake env lean ../formalization/NSFormalization/Section3/T22/CutoffDatum.lean` | no output (0 errors, 0 warnings) |
| `lake env lean ../research/T22/probes/cutoff_datum_closes.lean` | no output (0 errors, 0 warnings) |
| `lake env lean ../research/T22/axioms_ub3.lean` | `exists_cutoff`, `exists_cutoff_isOpen`, `isCutoffDatum_realizes_zeroExtension` each `depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `make check` | exit 0 (`13 tests OK`, `45 work items: ownership, contract registration and task cards consistent.`) |

Probe of the Mathlib API before writing any proof: `#check @exists_contMDiffMap_one_nhds_of_subset_interior`,
`#check @exists_compact_between`, `#check @contMDiff_iff_contDiff` all elaborate, and the manifold
lemma applies to `Space = EuclideanSpace ℝ (Fin 3)` with `I := 𝓘(ℝ, Space)` (all instances found).

---

## Superseded — the lane's first (codex) report, verbatim

> # Lane 409-T22-UB3-cutoff-datum
>
> ## Theorems
>
> No new theorem was closed. The intended statements are `exists_cutoff` and
> `isCutoffDatum_realizes_zeroExtension` from U-B3.
>
> ## Files
>
> Added `research/T22/ATTEMPTS_UB3.md`, `research/T22/axioms_ub3.lean`, and the
> basic domain probe `research/T22/probes/cutoff_datum_closes.lean`.
>
> ## Gaps
>
> The pinned Mathlib reports `unknown identifier` for both
> `exists_smooth_tsupport_subset` and `exists_contDiff_one_nhds_of_subset`. The
> zero-extension pairing bridge required by the second theorem is also absent from
> current T22 imports. No prohibited placeholder was introduced.
>
> ## Commands
>
> `#check` probes were run with `cd verification && lake env lean`; both named cutoff
> lemmas failed with `unknown identifier`. The basic probe and axioms audit remain to
> be run after a replacement cutoff API is identified.
>
> The probe gate also stops before elaboration because the dependent `Domain.olean` has not
> been built in this worktree (`object file .../Section3/T22/Domain.olean does not exist`).
