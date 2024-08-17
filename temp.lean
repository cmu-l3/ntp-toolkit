def p := True
def q := True
axiom p_eq_true : p = True
axiom q_eq_true : q = True

-- The `goalDelta` approach fails because `have : p = True := by exact p_eq_true` does
-- not open a goal but `by exact p_eq_true` closes a goal
theorem list_eq_self : ∀ l : List α, l = l := by
  intro l
  cases l
  . have : p = True := by exact p_eq_true
    rfl
  . have : q = True := by exact q_eq_true
    rfl
