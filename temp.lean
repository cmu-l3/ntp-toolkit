def p := True
def q := True
axiom p_eq_true : p = True
axiom q_eq_true : q = True

-- The `goalDelta` approach fails because `have : p = True := by exact p_eq_true` does
-- not open a goal but `by exact p_eq_true` closes a goal
theorem list_eq_self (l : List α) : l = l := by
  cases l
  . have : p = True := by exact p_eq_true
    rfl
  . have : q = True := q_eq_true
    rfl

theorem zero_eq_zero : 0 = 0 := by omega

theorem true : ∃ a : Nat, ∀ p : Prop, p → p := by
  have : True := trivial
  refine ⟨0, ?_⟩
  intro p
  have : p → p := by
    intro hp
    have h1 : p := hp
    have h2 : p := hp
    have h3 : p := hp
    trivial
  exact this
