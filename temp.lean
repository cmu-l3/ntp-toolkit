import QuerySMT
import Aesop

def p := True
def q := True
axiom p_eq_true : p = True
axiom q_eq_true : q = True

namespace TacticProofs

theorem list_eq_self1 (l : List α) : l = l := by
  cases l
  . have : p = True := by exact p_eq_true
    rfl
  . have : q = True := q_eq_true
    rfl

theorem list_eq_self2 (α : Type) (l : List α) : l = l := by
  exact list_eq_self1 l

theorem list_eq_self3 (α : Type) (l : List α) : l = l := by
  cases l <;> simp [p_eq_true, q_eq_true]

theorem test1 (x : Nat) : x = x := by rfl

theorem test2 (x : α) : x = x := by rfl

theorem test3 (α : Type _) (x : α) : x = x := by rfl

theorem test4 (α : Type) (x : α) : x = x := by rfl

theorem test5 (α : Type) (f : α → Prop) (hf : ∀ x : α, f x = True) (x : α) : f x := by
  duper [*] {portfolioInstance := 7}

theorem zero_eq_zero : 0 = 0 := by omega

theorem querySMTTest (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  intros h0 h1
  apply @Classical.byContradiction
  intro negGoal
  have smtLemma0 : ¬x ≤ z → x + -Int.ofNat 1 * z ≥ Int.ofNat 1 := by
    simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, Int.reduceNeg, Int.neg_mul, Int.one_mul, ← ge_iff_le]
    omega
  have smtLemma1 : y ≤ z → ¬y + -Int.ofNat 1 * z ≥ Int.ofNat 1 := by simp; omega
  have smtLemma2 : x ≤ y → ¬x + -Int.ofNat 1 * y ≥ Int.ofNat 1 := by simp; omega
  have smtLemma3 :
    (x + -Int.ofNat 1 * y ≥ Int.ofNat 1 ∨ y + -Int.ofNat 1 * z ≥ Int.ofNat 1) ∨ ¬x + -Int.ofNat 1 * z ≥ Int.ofNat 1 :=
    by simp; omega
  duper [h0, h1, negGoal, smtLemma0, smtLemma1, smtLemma2, smtLemma3] {portfolioInstance := 7}

theorem skolemizationTest1 (α : Type) [Inhabited α] (p : Prop) (f : α → Prop) (h : p ∨ ∃ x : α, f x) : p ∨ ∃ x : α, f x := by
  exact h -- `skolemizeAll` can succeed because `α` is known to be inhabited

theorem skolemizationTest2 (α : Type) (p : Prop) (f : α → Prop) (h : p ∨ ∃ x : α, f x) : p ∨ ∃ x : α, f x := by
  exact h -- `skolemizeAll` fails because `α` isn't known to be inhabited and the fact that `α` isn't inhabited doesn't follow from `h`

end TacticProofs

namespace TermProofs

theorem termProof1 : 0 = 0 := rfl

theorem termProof2 (x : Nat) : x + 0 = x := Nat.add_zero x

theorem termProof3 (p q : Prop) (h : p → q) (hp : p) : q := h hp

theorem termProof4 (b : Prop) (h : a → b) : a → b := h

end TermProofs
