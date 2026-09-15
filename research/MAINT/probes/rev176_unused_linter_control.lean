import Mathlib

/-! A proof-only reference keeps a compatibility hypothesis in the public type
without triggering Lean's unused-variable linter. -/

theorem rev176_unused_linter_control (P : Prop) (h : P) : True := by
  have _h := h
  trivial
