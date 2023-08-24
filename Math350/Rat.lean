
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

open Rat

lemma Rat.sq_ne_two (x : ℚ) : x ^ 2 ≠ 2 := by
  -- suppose `x ^ 2 = 2`
  intro h'  
  -- write `x = p / q` with `q : ℕ`, `q ≠ 0`, `p : ℤ` and `p` and `q` are coprime
  obtain ⟨p, q, hq, hp⟩ := x
  -- rewrite to get `p ^ 2 = 2 * q ^ 2`
  have h2 : (2 : ℚ).num = 2 ∧ (2 : ℚ).den = 1 := ⟨rfl, rfl⟩
  rw [←mkRat_self 2, mk_eq_mkRat, h2.1, h2.2, sq, mkRat_mul_mkRat,
    mkRat_eq_iff (by positivity) (by positivity), ←sq, ←sq] at h'
  simp at h'
  -- `2` is prime
  have hprime := Int.prime_two
  -- and (by `h'`) it divides `p ^ 2`, it must divide `p` so we can get `p = 2 * k`.
  obtain ⟨k, rfl⟩ := hprime.dvd_of_dvd_pow ⟨(q : ℤ) ^ 2, h'⟩
  -- expand out to get `2 * (2 * k ^ 2) = 2 * q ^ 2`, then cancel to get `2 * k ^ 2 = q ^ 2`.
  rw [mul_pow, sq, mul_assoc] at h'
  -- since `2` is prime and it divides `q ^ 2`, it must divide `q` so we can get `q = 2 * j`.
  have h'' : 2 * k ^ 2 = (q : ℤ) ^ 2 := mul_left_cancel₀ two_ne_zero h'
  -- so we can get `p = 2 * j`.
  obtain ⟨j, hj⟩ := hprime.dvd_of_dvd_pow ⟨k ^ 2, h''.symm⟩
  -- but `p q` were suppose to be coprime, but that means `2 * k` and `2 * j` are coprime, 
  -- but that's a contradiction since `2` divides both of these.
  rw [←Int.natAbs_cast q, ←Int.coprime_iff_nat_coprime, hj] at hp
  exact hprime.not_unit <| hp.isUnit_of_dvd' ⟨k, rfl⟩ ⟨j, rfl⟩

lemma Rat.add_sq_lt_two (x : ℚ) (hx : x ^ 2 < 2) :
    x < x + (2 - x ^ 2) / 4 ∧ (x + (2 - x ^ 2) / 4) ^ 2 < 2 := by
  have h2x : 0 < 2 - x ^ 2 := sub_pos.mpr hx
  have h2x' : 2 - x ^ 2 ≤ 2 := sub_le_self 2 <| by positivity
  have hx_bd : x < 3 / 2 := 
    (le_abs_self x).trans_lt <| abs_lt_of_sq_lt_sq (hx.trans <| by norm_num) (by positivity)
  refine ⟨by linarith, ?_⟩
  simp [add_sq, sq (2 - x ^ 2)]
  calc
    _ ≤ x ^ 2 + 2 * (3 / 2) * ((2 - x ^ 2) / 4) + (2 - x ^ 2) * 2 / 4 ^ 2 := by gcongr
    _ = x ^ 2 + (2 * (3 / 2) / 4 + 2 / 4 ^ 2) * (2 - x ^ 2) := by ring
    _ < x ^ 2 + 1 * (2 - x ^ 2) := by gcongr; norm_num
    _ = 2 := by simp

lemma Rat.two_lt_sub_sq (x : ℚ) (hx : 2 < x ^ 2) (hx' : x < 2) :
    x - (x ^ 2 - 2) / 4 < x ∧ 2 < (x - (x ^ 2 - 2) / 4) ^ 2 := by
  have h2x : 0 < x ^ 2 - 2 := sub_pos.mpr hx
  refine ⟨by linarith, ?_⟩
  rw [sub_sq]
  calc
    2 = x ^ 2 - 2 * (2 / 4) * (x ^ 2 - 2) := by norm_num
    _ < x ^ 2 - 2 * (x / 4) * (x ^ 2 - 2) := by gcongr
    _ = x ^ 2 - 2 * x * ((x ^ 2 - 2) / 4) + 0 := by ring
    _ < x ^ 2 - 2 * x * ((x ^ 2 - 2) / 4) + ((x ^ 2 - 2) / 4) ^ 2 := by gcongr; positivity

lemma Rat.upperBounds_setOf_sq_lt_two :
    upperBounds {x : ℚ | x ≤ 0 ∨ x ^ 2 < 2} = {x : ℚ | 0 ≤ x ∧ 2 < x ^ 2} := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intro u hu 
    simp only [Set.mem_setOf_eq]
    refine ⟨hu (.inl le_rfl), ?_⟩
    apply lt_of_le_of_ne ?_ u.sq_ne_two.symm 
    by_contra' h
    obtain ⟨hu₁, hu₂⟩ := u.add_sq_lt_two h
    linarith [hu (.inr hu₂)]
  · rintro u ⟨hu₁, hu₂⟩ x (hx | hx)
    · exact hx.trans hu₁
    · exact (le_abs_self x).trans <| abs_le_of_sq_le_sq (hx.trans hu₂).le hu₁

/-- Some sets of rational numbers don't have least upper bounds (which are
still rational), -/
example : ¬ ∃ u : ℚ, IsLUB {x : ℚ | x ≤ 0 ∨ x ^ 2 < 2} u := by
  -- suppose such a `u` *does* exist.
  rintro ⟨u, hu⟩ 
  -- unfold what it means to be the LUB, and use an equality for
  -- `upperBounds {x : ℚ | x ≤ 0 ∨ x ^ 2 < 2}`.
  rw [IsLUB, Rat.upperBounds_setOf_sq_lt_two, IsLeast, mem_lowerBounds] at hu
  obtain ⟨⟨hu₁, hu₂⟩, hu₃⟩ := hu
  -- Since `1.9 ∈ {x | 0 ≤ x ∧ x ^ 2 < 2}`, and `u` is a lower bound for this set: `u ≤ 1.9 < 2`.
  have hu2 := (hu₃ 1.9 (by norm_num)).trans_lt (by norm_num : (1.9 : ℚ) < 2)
  -- Then `u ≤ u - (u ^ 2 - 2) / 4`, as long as we can show the latter is in this set.
  have := hu₃ (u - (u ^ 2 - 2) / 4) ?_
  · linarith -- that of course leads to an obvious contradiction since `0 < (u ^ 2 - 2) / 4` 
  · constructor
    -- showing it's positive is not too hard, and this is one place where we use `u < 2`.
    · rw [sub_nonneg]
      calc 
        _ ≤ (2 ^ 2 - 2) / 4 := by gcongr
        _ ≤ u := le_of_pow_le_pow 2 hu₁ zero_lt_two (lt_trans (by norm_num) hu₂).le
    -- showing it satisfies the other inequality is the content of `Rat.two_lt_sub_sq`.
    · exact (u.two_lt_sub_sq hu₂ hu2).2

/-- The set `{x : ℚ | x ^ 2 < 2}` from the previous example is nonempty
and bounded above. -/
example : {x : ℚ | x ≤ 0 ∨ x ^ 2 < 2}.Nonempty ∧ BddAbove {x : ℚ | x ≤ 0 ∨ x ^ 2 < 2} := by
  constructor
  · exact Set.nonempty_def.mpr <| ⟨0, .inl le_rfl⟩
  · use 2 -- we claim that `2` is an upper bound.
    rintro x (hx | hx)
    · exact hx.trans <| by norm_num
    · exact le_of_pow_le_pow 2 (by norm_num) (by norm_num) <| hx.le.trans <| by norm_num
