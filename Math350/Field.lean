import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg

namespace Hidden

class Field (F : Type _) extends Zero F, One F, Mul F, Add F, Neg F, Inv F where
  add_comm : ∀ a b : F, a + b = b + a
  mul_comm : ∀ a b : F, a * b = b * a
  add_assoc : ∀ a b c : F, (a + b) + c = a + (b + c)
  mul_assoc : ∀ a b c : F, (a * b) * c = a * (b * c)
  add_zero : ∀ a : F, a + 0 = a
  add_neg_self : ∀ a : F, a + (-a) = 0
  mul_one : ∀ a : F, a * 1 = a
  mul_inv : ∀ {a : F}, a ≠ 0 → a * a⁻¹ = 1
  left_distrib : ∀ a b c : F, a * (b + c) = a * b + a * c
  one_ne_zero : (1 : F) ≠ 0

section Field

variable {F : Type _} [Field F]

export Field (add_comm mul_comm add_assoc mul_assoc add_zero add_neg_self mul_one mul_inv left_distrib
  one_ne_zero)

lemma zero_add (a : F) : 0 + a = a :=
  calc
    0 + a = a + 0 := add_comm 0 a
    _     = a     := add_zero a

lemma neg_add_self (a : F) : -a + a = 0 :=
  calc
    -a + a = a + -a := by rw [add_comm]
    _      = 0      := by rw [add_neg_self]

-- do the same for multiplication
lemma one_mul (a : F) : 1 * a = a :=
  sorry

-- do the same for multiplication
-- here `ha` is a *proof* that `a ≠ 0`, which we will need to use at some point
lemma inv_mul {a : F} (ha : a ≠ 0) : a⁻¹ * a = 1 :=
  calc 
    a⁻¹ * a = a * a⁻¹ := by rw [mul_comm]
    _       = 1       := by rw [mul_inv ha]

lemma right_distrib (a b c : F) : (a + b) * c = a * c + b * c :=
  sorry

-- something that behaves like `0` must *be* `0`.
-- note that `h` is a *proof* that `∀ a : F, a + z = a`, which we can *use*
-- see how it appears in our *local context*
lemma zero_unique (z : F) (h : ∀ a, a + z = a) : z = 0 :=
  calc
    z = 0 + z := by rw [zero_add]
    _ = 0     := by rw [h]

-- something that behaves like `-a` must *be* `-a`.
-- note that `h` is a *proof* that `a + b = 0`, which we can *use*
-- see how it appears in our *local context*
lemma neg_unique (a b : F) (h : a + b = 0) : b = -a :=
  sorry

lemma one_unique (n : F) (h : ∀ a, a * n = a) : n = 1 :=
  sorry

lemma inv_unique (a b : F) (ha : a ≠ 0) (h : a * b = 1) : b = a⁻¹ :=
  sorry

lemma zero_mul (a : F) : 0 * a = 0 := by
  have h : a + 0 * a = a :=
    calc
      a + 0 * a = 1 * a + 0 * a := by rw [one_mul]
      _         = (1 + 0) * a   := by rw [right_distrib]
      _         = a             := by rw [add_zero, one_mul]
  calc
    0 * a = (-a + a) +  0 * a := by rw [neg_add_self, zero_add]
    _     = -a + (a + 0 * a)  := by rw [add_assoc]
    _     = -a + a            := by rw [h]
    _     = 0                 := by rw [neg_add_self]

-- don't do a lot of work here! And don't just copy-and-paste!
lemma mul_zero (a : F) : a * 0 = 0 :=
  sorry

-- what tools do we have for showing something is equal to `-a`? Only `neg_unique`!
lemma neg_one_mul (a : F) : (-1) * a = -a := by
  apply neg_unique
  -- since the conlcusion of `neg_unique` is exactly "something is equal to `-a`",
  -- we can `apply` that theorem, and then we just need to show the hypotheses in that theorem are
  -- satisfied.
  calc
    a + (-1) * a = 1 * a + (-1) * a := by rw [one_mul]
    _            = (1 + -1) * a     := by rw [right_distrib]
    _            = 0 * a            := by rw [add_neg_self]
    _            = 0                := by rw [zero_mul]

lemma neg_mul (a b : F) : (-a) * b = - (a * b) := by
  rw [←neg_one_mul a, mul_assoc, neg_one_mul]

lemma mul_neg (a b : F) : a * -b = - (a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

-- note: we can't quite use `neg_unique` because this doesn't say "something is equal to `-a`" and
-- instead is says "`-a` is equal to something". We can switch the order using `symm`.
lemma neg_neg (a : F) : -(-a) = a := by
  symm
  apply neg_unique
  rw [neg_add_self]

lemma no_zero_divisors (a b : F) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0 -- allows us to use a proof by cases
  · left -- when proving an `∨`, let's us prove only the left one
    rw [ha]
  · right -- when proving an `∨`, let's us prove only the right one
    rw [←Ne.def] at ha -- changes `¬ a = 0` to `a ≠ 0`, purely cosmetic
    calc
      b = (a⁻¹ * a) * b := by rw [inv_mul ha, one_mul] -- here we need to provide the proof `ha` that `a ≠ 0`
      _ = a⁻¹ * (a * b) := by rw [mul_assoc]
      _ = 0             := by rw [h, mul_zero]

example (a b : F) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  -- we can write `suffices new_goal by tauto` to replace the goal with `new_goal` which is
  -- *logically* equivalent to the first goal.
  suffices a ≠ 0 → b = 0 by tauto
  intro ha
  calc
    b = (a⁻¹ * a) * b := by rw [inv_mul ha, one_mul] -- here we need to provide the proof `ha` that `a ≠ 0`
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = 0             := by rw [h, mul_zero]

example (p q r : Prop) : (p → q → r) ↔ (p ∧ q → r) := by
  tauto

example (p q : Prop) : (p → q) ↔ (¬p ∨ q) := by
  tauto

example {X : Type _} [Nonempty X] (P : X → Prop) : ¬(∀ x : X, P x) ↔ ∃ x : X, ¬P x := by
  push_neg -- tauto doesn't solve this, but `push_neg` does!
  rfl

end Field

end Hidden
