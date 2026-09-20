# T14 (packet import + `lem:packetenergy`, `01-introduction.tex:15-28`, `02-preliminaries.tex:127-153`) — reconciliation of drafts A (lane 273, gpt-5.6-sol) and B (lane 274, gpt-6-astra)

Lead: erenup, 2026-09-17 (UTC 21:15).

## 1. Agreement
Both reuse the registered ℝ³ packet contract verbatim (`Contracts/V1/Packet.lean` `PacketAPI ν`: `U, P, F, K, M, D, τ` with regularity, supports, PDE, blowup, the exact `IsLUB` definition of `M`, the integral definition of `D`, the initial quiet interval and the smooth zero extension to negative times — i.e. `lem:packetenergy`'s "M, D < ∞, vanishing on an initial interval, extension by zero" clauses are **inherited**, not restated), and add exactly the display `eq:packetenergy` `‖U(t)‖²₂ + 2ν∫₀ᵗ‖∇U‖²₂ ≤ 2∫₀ᵗ‖F(s)‖₂ N(s) ds = N(t)²` with `N(t) = ∫₀ᵗ‖F(s)‖₂ ds`, for `0 ≤ t < 1`. Both give the existential statement `∀ ν > 0, ∃ packet with the energy clause` in the paper's quantifier order. Neither periodizes (the packet is compactly supported in space, so the torus packet is its periodization — a T10-level remark).

## 2. Rulings
| point | A | B | ruling |
|---|---|---|---|
| packaging | `TorusPacketEnergyAPI ν extends PacketAPI ν` with one field `packet_energy` (the `≤` and the `=` as a conjunction) | `PacketEnergyAPI P : Prop` with `energy_le_work`, `work_eq_square`; `PacketImportAPI ν extends PacketAPI ν` with `energy : PacketEnergyAPI toPacketAPI` | **B** (two fields mirror the paper's chained display; the `Prop` record over a given packet lets T15/T17 state their hypotheses over `P`). |
| integration domain | `Ioc 0 t` | `Ioo 0 t` | **`Ioo`** (B); a.e. equal, and consistent with `PacketAPI.dissipation_integrable` on `Ioo 0 1`. |
| accumulated force | `packetForceAccumulation` | `accumulatedForce` | **`accumulatedForce`** (B). |
| family selector | `TorusPacketEnergyFamily.select : ∀ ν > 0, TorusPacketEnergyAPI ν` | `packetImportStatement : Prop` | **both**: the `Prop` statement (B) and the data-carrying family (A, renamed `PacketImportFamily`) — the latter is what T15/T17 consume (`SECTION3_PLAN.md` §3: "fix one solution at each viscosity"). |

## 3. Decisions
`research/T14/Spec.lean` = B's `PacketEnergyAPI`/`PacketImportAPI`/`packetImportStatement` + A's `PacketImportFamily`; docstrings with both drafts' citations. Proof plan: the energy identity on `[0,b]`, `b < 1`, from compact support + the ℝ³ PDE (Section 4's `Bindings/Packet.lean` `packet ν` supplies the `PacketAPI` witness; the energy display is a new Grönwall-free computation: A03/C01-style `sqrt_energy_le_primitive` from Section 4 (`Section4/C01/EnergyBounds.lean:179`, `Paper1/ScalarEnergy.lean:22`) gives `‖U(t)‖₂ ≤ N(t)` immediately).

## 4. Next
Lane 280: reconciled `research/T14/Spec.lean` + merged `COMPARISON.md`; then the proof lane (S–M, sol) and registration (`T02`/`T01` bucket per §3).
