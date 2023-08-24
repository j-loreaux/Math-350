import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Positivity
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.TFAE
import Mathlib.Algebra.GeomSum

section Generic
variable {F : Type _} [LinearOrderedField F] [DenselyOrdered F]

/-- An element `u : F` is an *upper bound* of a set `S ⊆ F`, if `s ≤ u` for all `s ∈ S`.
In the library, this is called `mem_upperBounds`. -/
example (S : Set F) (u : F) : u ∈ upperBounds S ↔ ∀ s ∈ S, s ≤ u := 
  Iff.rfl -- `Iff.rfl` means "this `↔` is true by definition"

/-- A subset `S ⊆ F` is said to be *bounded above* if it has some upper bound.
In the library, this is called `bddAbove_def`. -/
example (S : Set F) : BddAbove S ↔ ∃ u, u ∈ upperBounds S :=
  Iff.rfl

/-- `u` is the LUB of `S` if and only if it is an upper bound of `S` and it
is les than or equal to every other upper bound of `S`.

This is true by definition, but it doesn't have a name in the library, so we
give it one ourselves. -/
lemma isLUB_iff {u : F} {S : Set F} :
    IsLUB S u ↔ (u ∈ upperBounds S ∧ ∀ u' ∈ upperBounds S, u ≤ u') :=
  Iff.rfl

/-- The least upper bound for a set is unique (if it exists!), see the `Rat.lean` file. -/
lemma isLUB_unique (S : Set F) (u u' : F) (hu : IsLUB S u) (hu' : IsLUB S u') :
    u = u' := by
  rw [isLUB_iff] at hu hu'
  obtain ⟨hu_bd, hu_least⟩ := hu
  obtain ⟨hu'_bd, hu'_least⟩ := hu'
  refine le_antisymm ?_ ?_
  · exact hu_least u' hu'_bd
  · exact hu'_least u hu_bd

/-- Often in analysis it is useful to prove an inequality `x ≤ y` by giving
yourself an arbitrarily small buffer `ε`, and proving the inequality 
`x ≤ y + ε`. If this holds for all `ε > 0`, then `x ≤ y`.

In the library this is called `le_of_forall_pos_le_add` -/
example {x y : F} (h : ∀ ε > 0, x ≤ y + ε) : x ≤ y := by
  -- we prove the contrapositive
  contrapose h
  -- so suppose `y < x`
  push_neg at h ⊢
  -- choose `ε := (x - y) / 2`
  use (x - y) / 2
  constructor
  -- since `y < x`, then `x - y` is positive and hence so is `ε`.
  · linarith
  -- `y + ε = y + (x - y) / 2 = (x + y) / 2 < (y + y) / 2 = y`.
  · linarith

/-- If `u` is an upper bound of a set `S` in a densely linearly ordered field, then
`u` is the least upper bound of `S` if and only if for every `ε > 0` there is some
`s ∈ S` which exceeds `u - ε`.

It can often be useful to use this equivalent characterization of least upper bounds. -/
lemma isLUB_iff_forall_exists_sub_lt {u : F} {S : Set F} (hu : u ∈ upperBounds S) :
    IsLUB S u ↔ ∀ ε > 0, ∃ s ∈ S, u - ε < s := by
  -- we're going to change the statement we need to prove to an equivalent one
  rw [isLUB_iff] 
  -- since we already know `u` is an upper bound we can ignore that condition
  simp only [hu, true_and]
  conv =>
    arg 1 -- look at the left-hand side of the `iff`
    ext b -- and zoom in to the expression inside the `∀`
    -- `· ↔ ·` is equivalent to `¬· ↔ ¬·`, and just by using
    -- the definition of `upperBounds`, and pushing the negations
    -- through, we get an equivalent condition
    rw [←not_imp_not, mem_upperBounds] 
    push_neg
  constructor
  -- in one direction we just plug in `b := u - ε` and we're done
  -- once we check that `u - ε < u`, which is true since `ε > 0`.
  · intro h ε hε 
    specialize h (u - ε)
    exact h (by linarith)
  -- for the other direction plug in `ε := u - b`, and after 
  -- simplification, we're done
  · intro h b
    specialize h (u - b)
    simpa using h

-- this is an alternate proof of the previous theorem. It's a bit
-- longer, but it might be a bit easier to follow.
example {u : F} {S : Set F} (hu : u ∈ upperBounds S) :
    IsLUB S u ↔ ∀ ε > 0, ∃ s ∈ S, u - ε < s := by
  constructor
  -- supppose `u` is the least upper bound of `S`.
  -- equivalently, for every `b`, `u ≤ b` if and only if
  -- `b` is also an upper bound of `S`. 
  · intro h
    rw [isLUB_iff_le_iff] at h
    -- Let `ε > 0` 
    intros ε hε
    -- use the equivalent condition with `b = u - ε`.
    specialize h (u - ε)
    -- since `u - ε < u`, then `¬ u ≤ u - ε`, and so
    -- `u - ε` is not an upper bound of `S`.
    rw [←not_iff_not] at h
    have := h.mp (by linarith)
    -- then this means exactly that there is some `s ∈ S`
    -- with `u - ε < s`.
    rw [mem_upperBounds] at this
    push_neg at this
    exact this
  · intro h
    rw [isLUB_iff_le_iff]
    intro y
    constructor
    · intro huy
      rw [mem_upperBounds] at hu ⊢
      intros x hx
      calc
        x ≤ u := hu x hx
        _ ≤ y := huy
    · intro hy
      apply le_of_forall_pos_le_add
      intro ε hε
      specialize h ε hε
      obtain ⟨s, hS, hs⟩ := h
      calc
        u ≤ s + ε := by linarith
        _ ≤ y + ε := by
          apply add_le_add_right
          exact hy hS

lemma forall_exists_sub_lt_of_isLUB {u : F} {S : Set F} (h : IsLUB S u) :
  ∀ ε > 0, ∃ s ∈ S, u - ε < s :=
(isLUB_iff_forall_exists_sub_lt (isLUB_iff.mp h).1).mp h

end Generic

section Real

/-- The defining property of the real numbers: every nonempty set which is 
bounded above has a least upper bound (LUB). As you can see, in the library
this is called `Real.exists_isLUB`.

This property is called *completeness*. It turns out that `ℝ` is the *unique*
complete (linearly) ordered field. Technically, this notion is called 
*order completeness*, because there is another notion called *Cauchy 
completeness* which we will discuss later. -/
example (S : Set ℝ) (h_non : S.Nonempty) (h_bdd : BddAbove S) :
    ∃ u : ℝ, IsLUB S u :=
  Real.exists_isLUB S h_non h_bdd

/-- The least upper bound of a nonempty set `S` which is bounded above is 
called the *supremum*. In thie library, this is called `sSup S`, and the 
fact that this element is the least upper bound of `S` is called `isLUB_csSup`. -/
example (S : Set ℝ) (h_non : S.Nonempty) (h_bdd : BddAbove S) :
    IsLUB S (sSup S) :=
  isLUB_csSup h_non h_bdd

/-- The real numbers are an *Archimedean* field. -/
lemma exists_nat_gt' (x : ℝ) : ∃ n : ℕ, x < n := by
  -- we proceed by contradition. Suppose no such `n` exists.
  -- so every natural number is less than or equal to `x`.
  by_contra' h
  -- we claim `x` is an upper bound for `ℕ`
  have bdd : x ∈ upperBounds {y : ℝ | ∃ n : ℕ, y = n} := by
    rintro _ ⟨n, rfl⟩
    exact h n
  have nonemp : {y : ℝ | ∃ n : ℕ, y = n}.Nonempty := ⟨0, ⟨0, by simp⟩⟩
  have := isLUB_csSup nonemp ⟨x, bdd⟩
  obtain ⟨-, ⟨n, -, rfl⟩, h'⟩ := forall_exists_sub_lt_of_isLUB this 1 one_pos
  have not_up_bd : ¬ sSup {y : ℝ | ∃ n : ℕ, y = n} ∈ upperBounds {y : ℝ | ∃ n : ℕ, y = n} := by
    rw [mem_upperBounds]
    push_neg
    exact ⟨n + 1, ⟨⟨n + 1, by simp⟩, by linarith⟩⟩
  apply not_up_bd
  exact (isLUB_iff.mp this).1

/-- A (linearly) ordered field is said to be Archimedean if and one of the following
equivalent conditions holds -/
lemma tfae_archimedean {F : Type _} [LinearOrderedField F] :
    List.TFAE [ -- The following are equivalent (i.e., TFAE)
      -- Every element of `F` is less than some natural number
      ∀ x : F, ∃ n : ℕ, x < n,
      -- For any positive elements `x y`, there is a natural number `n`
      -- such that `y < n • x`.
      ∀ x y : F, 0 < x → 0 < y → ∃ n : ℕ, y < n • x,
      -- every positive number is greater than the reciprocal of
      -- of some (positive) natural number.
      ∀ x : F, 0 < x → ∃ n : ℕ, 1 / (n + 1: F) < x,
      -- The set of natural numbers is unbounded above in `F`.
      ¬ BddAbove {y : F | ∃ n : ℕ, y = n},
      -- every positive element of the field lies in some half-open
      -- interval `x ∈ [n, n + 1)`
      ∀ x : F, 0 < x → ∃ n : ℕ, (n : F) ≤ x ∧ x < n + 1
    ] := by
  tfae_have 1 → 2
  /- Suppose `1` and `x y : F` are positive.
   -/
  · intro h x y hx _hy
    obtain ⟨n, hn⟩ := h (y * x⁻¹)
    use n
    rw [mul_inv_lt_iff hx, mul_comm, ←nsmul_eq_mul] at hn
    exact hn
  tfae_have 2 → 3
  · intro h x hx
    obtain ⟨n, hn⟩ := h x 1 hx one_pos
    use n
    have : n ≠ 0 := by
      rintro rfl
      rw [zero_nsmul] at hn
      linarith
    have : 0 < n := Nat.pos_of_ne_zero this
    rw [div_lt_iff (by exact_mod_cast n.succ_pos), mul_comm, add_mul, ←nsmul_eq_mul,
      one_mul]
    simpa using add_lt_add hn hx
  tfae_have 2 → 4
  · rintro h ⟨x, hx⟩
    have x_pos : 0 < x :=
      lt_of_lt_of_le zero_lt_one (mem_upperBounds.mp hx (1 : F) ⟨1, by simp⟩)
    obtain ⟨n, hn⟩ := h 1 x zero_lt_one x_pos
    rw [nsmul_eq_mul, mul_one] at hn
    linarith [mem_upperBounds.mp hx (n : F) ⟨n, rfl⟩]
  tfae_have 4 → 5
  · intro h x hx
    by_cases hx' : x < 1
    · exact ⟨0, ⟨by simpa using hx.le, by simpa using hx'⟩⟩
    · push_neg at hx'
      have h_non : {n : ℕ | x < n}.Nonempty := by 
        rw [not_bddAbove_iff] at h
        obtain ⟨-, ⟨k, rfl⟩, hk⟩ := h x
        exact ⟨k, hk⟩
      obtain ⟨m, hmx, hm⟩ := WellFounded.wellFounded_iff_has_min.mp
        Nat.lt.isWellOrder.toIsWellFounded.wf {n : ℕ | x < n} h_non
      have hm' : 1 < m := by exact_mod_cast hx'.trans_lt hmx
      refine ⟨m - 1, ?_, hmx.trans_eq <| by exact_mod_cast (Nat.sub_add_cancel hm'.le).symm⟩
      have := mt <| hm (m - 1)
      simp only [not_lt, not_le, Set.mem_setOf_eq] at this 
      refine this <| Nat.sub_lt_self zero_lt_one hm'.le
  tfae_have 5 → 1
  /- Supose `5` and `x : F`. -/
  · intro h x
    by_cases hx : x ≤ 0
    /- If `x ≤ 0`, then `x < 1`. -/
    · use 1
      exact_mod_cast hx.trans_lt zero_lt_one
      /- If `0 < x`, then by the hypothesis `5`,
      we can find an `n` such that `n ≤ x` and `x < n + 1`.
      So we can select `n + 1`. -/
    · push_neg at hx
      obtain ⟨n, -, hn⟩ := h x hx
      exact ⟨n + 1, by exact_mod_cast hn⟩
  tfae_have 3 → 1
  /- suppose `3` and `x : F`. -/
  · intro h x
    by_cases hx : x ≤ 0
    /- If `x ≤ 0`, then `x < 1`. -/
    · exact ⟨1, by exact_mod_cast hx.trans_lt zero_lt_one⟩
    /- If `0 < x`, then `0 < 1 / x`, and so by the hypothesis `3`,
    we can find an `n : ℕ` such that `1 / (n + 1) < 1 / x`. -/
    · push_neg at hx
      obtain ⟨n, hn⟩ := h (1 / x) <| one_div_pos.mpr hx
      /- We claim that `n + 1` is a natural number that works.
      Indeed, since both `x` and `n + 1` are positive, and `1 / (n + 1) < 1 / x`,
      then we conclude `x < n + 1`. -/
      refine ⟨n + 1, ?_⟩
      exact_mod_cast (one_div_lt_one_div (by exact_mod_cast n.succ_pos) hx).mp hn
  tfae_finish

end Real

section Properties

open Finset BigOperators

/- Here, `range n` consists of the numbers `0, 1, 2, ..., n - 1`.

As you can see below, in the library this lemma is called `geom_sum_eq`. -/
example {x : ℝ} (hx : x ≠ 1) (n : ℕ): 
    ∑ k in range n, x ^ k = (x ^ n - 1) / (x - 1) :=
  geom_sum_eq hx n

/- If `x` is less than `y`, then it is less than their average (i.e., arithmetic mean).

In the library, this lemma is called `left_lt_add_div_two`, but `linarith` can prove it. -/
example {x y : ℝ} (h : x < y) : x < (x + y) / 2 := by
  linarith 
  
/- I bet you can guess the name of the lemma saying `(x + y) / 2 < y`, it's 
`add_div_two_lt_right`. -/
example {x y : ℝ} (h : x < y) : (x + y) / 2 < y := by
  linarith


lemma lt_iff_sq_lt_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < y ↔ x ^ 2 < y ^ 2 := by
  simpa [abs_of_nonneg hx, abs_of_nonneg hy] using (sq_lt_sq (x := x) (y := y)).symm

lemma lt_iff_sqrt_lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < y ↔ x.sqrt < y.sqrt := by
  have := (lt_iff_sq_lt_sq x.sqrt_nonneg y.sqrt_nonneg).symm
  simpa [Real.sq_sqrt hx, Real.sq_sqrt hy]

example {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : (x * y).sqrt ≤ (x + y) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · rw [div_pow, add_sq, ← mul_le_mul_left zero_lt_two, ← mul_assoc, ← mul_le_mul_left zero_lt_two,
      two_mul]
    refine (add_le_add_left (two_mul_le_add_sq x y) _).trans_eq ?_
    ring

example (x : ℝ) : 0 ≤ |x| := abs_nonneg x
example (x : ℝ) : 0 ≤ |x| := by positivity

example (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y := abs_le
example (x y : ℝ) : x ≤ |y| ↔ x ≤ y ∨ x ≤ -y := le_abs

example (x y : ℝ) : |x * y| = |x| * |y| := abs_mul x y

example (x : ℝ) : |-x| = |x| := abs_neg x

-- `abs_sub_comm`
example (x y : ℝ) : |x - y| = |y - x| :=
  calc
    |x - y| = |-(y - x)| := by rw [neg_sub]
    _       = |y - x|    := abs_neg _

-- this is called the *triangle inequality*
example (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add x y

-- `abs_sub_abs_le_abs_sub`
example (x y : ℝ) : |x| - |y| ≤ |x - y| := by
  rw [sub_le_iff_le_add]
  have := abs_add (x - y) y
  simpa

-- `abs_abs_sub_abs_le_abs_sub`
example (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| := by
  rw [abs_le]
  constructor
  · rw [neg_le, neg_sub, abs_sub_comm]
    exact abs_sub_abs_le_abs_sub y x
  · exact abs_sub_abs_le_abs_sub x y



end Properties