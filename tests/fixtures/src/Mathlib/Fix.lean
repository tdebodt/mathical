module

variable {α : Type*} [Field α]

/-- The main theorem.
It has a second line. -/
theorem Thm (x : α) (h : x ≠ 0) : x / x = 1 := by
  field_simp

lemma A : (1 : α) ≠ 0 := one_ne_zero

/-- A hub definition. -/
def Hub (x : α) : α := x * x

theorem axb : True := trivial

/-- A short name. -/
abbrev Short (x : α) : α := Hub x
