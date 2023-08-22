import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Positivity
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.TFAE

section generic
variable {F : Type _} [LinearOrderedField F] [DenselyOrdered F]

-- mem_upperBounds
-- isLUB_iff_le_iff

lemma isLUB_iff {u : F} {S : Set F} :
    IsLUB S u ↔ (u ∈ upperBounds S ∧ ∀ u' ∈ upperBounds S, u ≤ u') :=
  Iff.rfl

-- `le_of_forall_pos_le_add`
example {x y : F} (h : ∀ ε > 0, x ≤ y + ε) : x ≤ y := by
  contrapose h
  push_neg at h ⊢
  use (x - y) / 2
  constructor
  · linarith
  · linarith

lemma isLUB_iff_forall_exists_sub_lt {u : F} {S : Set F} (hu : u ∈ upperBounds S) :
    IsLUB S u ↔ ∀ ε > 0, ∃ s ∈ S, u - ε < s := by
  constructor
  · intro h
    rw [isLUB_iff_le_iff] at h
    intros ε hε
    specialize h (u - ε)
    rw [←not_iff_not] at h
    have := h.mp (by linarith)
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

end generic

lemma exists_nat_gt' (x : ℝ) : ∃ n : ℕ, x < n := by
  by_contra' h
  have bdd : x ∈ upperBounds {y : ℝ | ∃ n : ℕ, (n : ℝ) ≤ x ∧ y = n} := by
    rintro _ ⟨n, hn, rfl⟩
    exact hn
  have nonemp : {y : ℝ | ∃ n : ℕ, (n : ℝ) ≤ x ∧ y = n}.Nonempty := ⟨0, ⟨0, h 0, by simp⟩⟩
  have := isLUB_csSup nonemp ⟨x, bdd⟩
  obtain ⟨-, ⟨n, -, rfl⟩, h'⟩ := forall_exists_sub_lt_of_isLUB this 1 one_pos
  have not_up_bd : ¬ sSup {y : ℝ | ∃ n : ℕ, (n : ℝ) ≤ x ∧ y = n} ∈ upperBounds {y : ℝ | ∃ n : ℕ, (n : ℝ) ≤ x ∧ y = n} := by
    rw [mem_upperBounds]
    push_neg
    exact ⟨n + 1, ⟨⟨n + 1, h _, by simp⟩, by linarith⟩⟩
  apply not_up_bd
  exact (isLUB_iff.mp this).1

lemma tfae_arch {F : Type _} [LinearOrderedField F] :
    List.TFAE [
      ∀ x : F, ∃ n : ℕ, x < n,
      ∀ x y : F, 0 < x → 0 < y → ∃ n : ℕ, y < n • x,
      ∀ x : F, 0 < x → ∃ n : ℕ, 1 / (n : F) < x,
      ¬ BddAbove {y : F | ∃ n : ℕ, y = n},
      ∀ x : F, 0 < x → ∃ n : ℕ, ((n - 1 : F) ≤ x ∧ x < n)
    ] := by
  tfae_have 1 → 2
  · intro h x y hx hy
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
    rw [div_lt_iff (by exact_mod_cast this), mul_comm, ←nsmul_eq_mul]
    exact hn
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
    · exact ⟨1, ⟨by simpa using hx.le, by simpa using hx'⟩⟩
    · push_neg at hx'
      use WellFounded.min Nat.lt.isWellOrder.toIsWellFounded.wf {n : ℕ | x < n} ?_
      rw [BddAbove, Set.not_nonempty_iff_eq_empty] at h
      have x_not_mem : x ∉ upperBounds {y : F | ∃ n : ℕ, y = n} := h ▸ Set.not_mem_empty x
      rw [mem_upperBounds] at x_not_mem
      push_neg at x_not_mem
      obtain ⟨-, ⟨n, rfl⟩, hn⟩ := x_not_mem
      refine ⟨n, ?_⟩
      sorry
      sorry
  tfae_have 5 → 1
  · intro h x
    by_cases hx : x ≤ 0
    · use 1
      exact_mod_cast hx.trans_lt zero_lt_one
    · push_neg at hx
      obtain ⟨n, -, hn⟩ := h x hx
      exact ⟨n, hn⟩
  tfae_have 3 → 1
  · sorry
  tfae_finish
