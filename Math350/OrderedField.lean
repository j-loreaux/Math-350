import Mathlib.Algebra.Field.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.LibrarySearch

section OrderedField

class OrderedField (F : Type _) extends Field F, LinearOrder F :=
  add_lt_add_right : ∀ {a b} (c : F), a < b → a + c < b + c
  mul_lt_mul_right : ∀ {a b : F}, a < b → (∀ {c}, 0 < c → a * c < b * c)

variable {F : Type _} [OrderedField F]

export OrderedField (add_lt_add_right mul_lt_mul_right)

macro "assume " h:ident : tactic =>
  `(tactic| intro $h:ident)

lemma add_lt_add_left {a b} (c : F) : a < b → c + a < c + b := by
  -- to prove an implication, we can assume the hypothesis
  assume h
  rw [add_comm c a, add_comm c b]
  apply add_lt_add_right
  exact h

lemma mul_lt_mul_left {a b : F} : a < b → (∀ {c}, 0 < c → c * a < c * b) := by
  -- to prove an implication, we can assume the hypothesis
  assume h
  assume c
  rw [mul_comm c a, mul_comm c b]
  apply mul_lt_mul_right
  exact h

lemma trichotomy (a b : F) : b < a ∨ a = b ∨ a < b := by
  rw [←le_iff_eq_or_lt]
  exact lt_or_le _ _

-- `lt_trans` is the fact that `<` is transitive
example (a b c : F) : a < b → b < c → a < c := lt_trans

lemma lt_iff_neg_add_lt_zero (a b : F) : a < b ↔ -b + a < 0 := by
  constructor
  · assume h
    calc
      -b + a < -b + b := add_lt_add_left _ h
      _      = 0      := by rw [neg_add_self]
  · assume h
    calc
      a = b + (-b + a) := by simp
      _ < b + 0        := add_lt_add_left _ h
      _ = b            := by simp

lemma neg_lt_neg {a b : F} : a < b → -b < -a := by
  assume h
  calc
    -b = -b + (a + -a) := by rw [add_neg_self, add_zero]
    _  = (-b + a) + -a := by rw [add_assoc]
    _  < 0 + -a        := by
      apply add_lt_add_right
      rw [lt_iff_neg_add_lt_zero] at h
      exact h
    _  = -a            := by rw [zero_add]

lemma neg_lt_neg_iff {a b : F} : a < b ↔ -b < -a := by
  constructor
  · exact neg_lt_neg
  · assume h
    have h' : -(-a) < -(-b) := neg_lt_neg h
    rw [neg_neg, neg_neg] at h'
    exact h'

lemma mul_lt_mul_right_of_neg {a b : F} : a < b → (∀ {c}, c < 0 → b * c < a * c) := by
  assume h
  intro c hc
  rw [neg_lt_neg_iff, neg_zero] at hc
  rw [neg_lt_neg_iff, ←mul_neg, ←mul_neg]
  apply mul_lt_mul_right
  exact h
  exact hc

lemma sq_pos {a : F} (ha : a ≠ 0) : 0 < a * a := by
  have : a < 0 ∨ 0 < a := Ne.lt_or_lt ha
  cases this with
  | inl ha =>
    have h := mul_lt_mul_right_of_neg ha ha
    simpa using h
  | inr ha =>
    have h := mul_lt_mul_right ha ha
    simpa using h

lemma inv_pos {a : F} (ha : 0 < a) : 0 < a⁻¹ := by
  have ha₁ : a ≠ 0 := ne_of_gt ha
  have ha₂ : a⁻¹ ≠ 0 := inv_ne_zero ha₁
  have ha₃ : 0 < a⁻¹ * a⁻¹ := sq_pos ha₂
  have ha₄ := mul_lt_mul_right ha ha₃
  rw [←mul_assoc a, mul_inv_cancel ha₁] at ha₄
  simpa using ha₄

example {a : F} (ha : a < 0) : a⁻¹ < 0 := by
  rw [neg_lt_neg_iff, neg_zero] at ha ⊢
  suffices 0 < (-a)⁻¹ by
    rw [←inv_neg]
    exact this
  apply inv_pos
  exact ha

end OrderedField
