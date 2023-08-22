import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Group.Bounds
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Order.Pointwise

set_option autoImplicit false

namespace Hidden

def Cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n m, n ≥ N → m ≥ N → |a n - a m| < ε

def CvgsTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε

lemma cvgsTo_one_div_nat : CvgsTo (fun n ↦ 1 / n) 0 := by
  rw [CvgsTo]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε -- follows from the Archimedean property
  use n + 1
  intro k hk
  have k_pos : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) (by exact_mod_cast hk : (n + 1 : ℝ) ≤ k)
  simp only [sub_zero, ge_iff_le, neg_le_self_iff, inv_nonneg, Nat.cast_nonneg, sup_of_le_left,
  gt_iff_lt, one_div, abs_of_pos (inv_pos.mpr k_pos)]
  refine lt_of_le_of_lt ?_ hn
  rw [one_div]
  exact (inv_le_inv k_pos (by positivity)).mpr (by exact_mod_cast hk)

@[simp]
lemma cvgsTo_const (A : ℝ) : CvgsTo (Function.const ℕ A) A :=
  fun ε hε => ⟨0, by simpa using hε⟩

@[simp]
lemma cvgsTo_const' (A : ℝ) : CvgsTo (fun _ ↦ A) A :=
  cvgsTo_const A

@[simp]
lemma cvgsTo_const_zero : CvgsTo 0 0 := cvgsTo_const 0

@[simp]
lemma cvgsTo_const_one : CvgsTo 1 1 := cvgsTo_const 1

lemma CvgsTo.cauchy {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) : Cauchy a := by
  intros ε hε
  obtain ⟨N, hN⟩ := ha (ε / 2) (by positivity)
  refine ⟨N, fun n m hn hm => ?_⟩
  calc
    |a n - a m| = |(a n - A) + (A - a m)| := by simp
    _           ≤ |a n - A| + |A - a m| := abs_add _ _
    _           = |a n - A| + |a m - A| := by rw [abs_sub_comm A]
    _           < ε / 2 + ε / 2         := add_lt_add (hN n hn) (hN m hm)
    _           = ε := add_halves ε

lemma Cauchy.bounded {a : ℕ → ℝ} (ha : Cauchy a) : Metric.Bounded (Set.range a) := by
  obtain ⟨N, hN⟩ := ha 1 one_pos
  have := ((Finset.range N).finite_toSet.image a).bounded
  rw [Metric.bounded_iff_subset_ball (a N)] at this ⊢
  obtain ⟨r, hr⟩ := this
  use max r 1
  rintro - ⟨n, rfl⟩
  by_cases hn : n < N
  · exact Metric.closedBall_subset_closedBall (le_max_left _ _) <|
      hr ⟨n, Finset.mem_range.mpr hn, rfl⟩
  · push_neg at hn
    apply Metric.closedBall_subset_closedBall (le_max_right _ _) <|
      by simpa using (hN n N hn le_rfl).le

lemma cvgsTo_zero_iff_abs {a : ℕ → ℝ} : CvgsTo a 0 ↔ CvgsTo (fun n ↦ |a n|) 0 := by
  simp only [CvgsTo, sub_zero, abs_abs]

lemma CvgsTo.add {a b : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (hb : CvgsTo b B) :
    CvgsTo (a + b) (A + B) := by
  simp only [CvgsTo] at *
  intros ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (half_pos hε)
  use max N₁ N₂
  intros n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  calc
    |a n + b n - (A + B)| = |(a n - A) + (b n - B)| := by ring_nf
    _                     ≤ |a n - A| + |b n - B| := abs_add _ _
    _                     < ε / 2 + ε / 2 := add_lt_add (hN₁ n hn₁) (hN₂ n hn₂)
    _                     = ε             := add_halves ε

lemma cvgsTo_iff_cvgsTo_zero {a : ℕ → ℝ} {A : ℝ} :
    CvgsTo a A ↔ CvgsTo (fun n ↦ a n - A) 0 := by
  simp only [CvgsTo, sub_zero] at *

lemma cvgsTo_iff_const_mul {a : ℕ → ℝ} {A : ℝ} {c : ℝ} (hc : 0 < c) :
    CvgsTo a A ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - A| < c * ε := by
  constructor
  · exact fun h ε hε => h (c * ε) (by positivity)
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (c⁻¹ * ε) (by positivity)
    use N
    simpa only [mul_inv_cancel_left₀ hc.ne'] using hN

lemma cvgsTo_iff_forall_le {a : ℕ → ℝ} {A : ℝ} :
    CvgsTo a A ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - A| ≤ ε := by
  constructor
  · rw [CvgsTo]
    refine forall_imp (fun ε h => ?_ ∘ h)
    apply Exists.imp
    exact fun ε hε n hn => (hε n hn).le
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    use N
    exact fun n hn => (hN n hn).trans_lt (by linarith)

lemma CvgsTo.zero_mul {a b : ℕ → ℝ} (ha : CvgsTo a 0)
    (hb : Metric.Bounded (Set.range b)) : CvgsTo (a * b) 0 := by
  obtain ⟨r, hr⟩ := (Metric.bounded_iff_subset_ball 0).mp hb
  rw [cvgsTo_iff_const_mul (by positivity : 0 < max (r + 1) 1)]
  intros ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  simp only [sub_zero] at hN ⊢
  rw [Pi.mul_apply, abs_mul, mul_comm _ ε]
  refine mul_lt_mul'' (hN n hn) ?_ (abs_nonneg _) (abs_nonneg _)
  calc
    |b n| ≤ r := by
      have := Metric.mem_closedBall.mp <| hr ⟨n, rfl⟩
      rwa [Real.dist_eq, sub_zero] at this
    _     < r + 1 := lt_add_one r
    _     ≤ max (r + 1) 1 := le_max_left _ _

lemma CvgsTo.const_mul {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (C : ℝ) :
    CvgsTo (fun n ↦ C * a n) (C * A) := by
  by_cases hC : C = 0
  · simp [hC]
  · replace hC := abs_pos.mpr hC
    rw [cvgsTo_iff_const_mul hC]
    intros ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    use N
    intro n hn
    rw [←mul_sub, abs_mul]
    exact (mul_lt_mul_left hC).mpr <| hN n hn

lemma CvgsTo.mul_const {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (C : ℝ) :
    CvgsTo (fun n ↦ a n * C) (A * C) := by
  simpa only [mul_comm _ C] using ha.const_mul C

lemma CvgsTo.neg {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) :
    CvgsTo (-a) (-A) := by
  rw [neg_eq_neg_one_mul a, neg_eq_neg_one_mul A]
  exact ha.const_mul (-1)

lemma CvgsTo.sub {a b : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (hb : CvgsTo b B) :
    CvgsTo (a - b) (A - B) := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

lemma CvgsTo.mul {a b : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (hb : CvgsTo b B) :
    CvgsTo (a * b) (A * B) := by
  have : a * b = (a · - A) * (b · - B) + (A * b ·) + (a · * B) - (fun _ ↦ A * B) := by
    funext; simp [sub_mul, mul_sub]; ring
  have ha' := cvgsTo_iff_cvgsTo_zero.mp ha
  have hb' := (cvgsTo_iff_cvgsTo_zero.mp hb).cauchy.bounded
  rw [this]
  simpa using (((ha'.zero_mul hb').add (hb.const_mul A)).add (ha.mul_const B)).sub <|
    cvgsTo_const (A * B)

lemma eventually_lt_abs_of_not_cvgsTo_zero {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (hA : A ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, |A| / 2 < |a n| := by
  replace hA := abs_pos.mpr hA
  obtain ⟨N, hN⟩ := ha (|A| / 2) (by positivity)
  use N
  intros n hn
  specialize hN n hn
  rw [abs_sub_comm] at hN
  replace hN := (abs_sub_abs_le_abs_sub _ _).trans_lt hN
  linarith

lemma CvgsTo.pow {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (p : ℕ) :
    CvgsTo (a ^ p) (A ^ p) := by
  induction p with
  | zero => simp
  | succ k hk => simpa [pow_succ] using ha.mul hk


lemma CvgsTo.inv {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (hA : A ≠ 0) :
    CvgsTo a⁻¹ A⁻¹ := by
  obtain ⟨N₁, hN₁⟩ := eventually_lt_abs_of_not_cvgsTo_zero ha hA
  rw [cvgsTo_iff_const_mul (by positivity : 0 < 2 / (|A| ^ 2))]
  intros ε hε
  obtain ⟨N₂, hN₂⟩ := ha ε hε
  use max N₁ N₂
  intros n hn
  specialize hN₁ n <| (le_max_left _ _).trans hn
  have han : a n ≠ 0 := abs_pos.mp <| (by positivity : 0 < |A| / 2).trans hN₁
  calc
    |(a n)⁻¹ - A⁻¹| = |A⁻¹ * A * (a n)⁻¹ - A⁻¹ * a n * (a n)⁻¹| := by
      rw [mul_assoc, inv_mul_cancel_left₀ hA, mul_inv_cancel_right₀ han]
    _               = (|A|)⁻¹ * |a n - A| * (|a n|)⁻¹ := by
      rw [←sub_mul, ←mul_sub, abs_mul, abs_mul, abs_inv, abs_inv, abs_sub_comm]
    _               ≤ (|A|)⁻¹ * |a n - A| * (2 / |A|) := by
      exact mul_le_mul_of_nonneg_left (by simpa using inv_le_inv_of_le (by positivity) hN₁.le)
        (by positivity)
    _               = 2 / |A| ^ 2 * |a n - A|  := by ring
    _               < 2 / |A| ^ 2 * ε := by
      exact (mul_lt_mul_left (by positivity)).mpr (hN₂ n <| (le_max_right _ _).trans hn)

lemma CvgsTo.div {a b : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (hb : CvgsTo b B) (hB : B ≠ 0) :
    CvgsTo (a / b) (A / B) := by
  simpa only [div_eq_mul_inv] using ha.mul <| hb.inv hB

lemma CvgsTo.zpow {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (hA : A ≠ 0) (k : ℤ) :
    CvgsTo (a ^ k) (A ^ k) := by
  cases k with
  | ofNat p => exact ha.pow p
  | negSucc p => simpa only [zpow_negSucc] using (ha.pow <| p + 1).inv <| pow_ne_zero (p + 1) hA

lemma CvgsTo.of_finite_ne {a b : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (h : {n | a n ≠ b n}.Finite) :
    CvgsTo b A := by
  obtain ⟨N, hN⟩ := h.bddAbove
  rw [mem_upperBounds] at hN
  replace hN := fun x => mt (hN x)
  simp only [not_le, ne_eq, Set.mem_setOf_eq, not_not] at hN
  intros ε hε
  obtain ⟨M, hM⟩ := ha ε hε
  use max (N + 1) M
  intros n hn
  rw [←hN n ((le_max_left _ _).trans hn)]
  exact hM n ((le_max_right _ _).trans hn)

lemma CvgsTo_iff_tail {a : ℕ → ℝ} {A : ℝ} (k : ℕ) : CvgsTo a A ↔ CvgsTo (fun n ↦ a (n + k)) A := by
  constructor
  · intro ha ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    use N
    intros n hn
    refine' hN (n + k) (hn.trans <| n.le_add_right k)
  · intro ha ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    use N + k
    intros n hn
    have hnk : k ≤ n := (k.le_add_left N).trans hn
    replace hn := Nat.le_sub_of_add_le hn
    specialize hN (n - k) hn
    simpa [Nat.sub_add_cancel hnk] using hN

lemma cvgsTo_one_div_nat_succ : CvgsTo (fun n ↦ 1 / (n + 1)) 0 := by
  convert (CvgsTo_iff_tail 1).mp cvgsTo_one_div_nat
  simp

def Dvgs (a : ℕ → ℝ) : Prop := ∀ A, ¬ CvgsTo a A

lemma neg_one_pow_dvgs : Dvgs ((-1) ^ ·) := by
  intro A
  by_cases hA : A ≤ 0
  · rw [CvgsTo]
    push_neg
    refine ⟨1, zero_lt_one, ?_⟩
    intro N
    refine ⟨2 * N, Nat.le_mul_of_pos_left two_pos, ?_⟩
    simp [pow_mul]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [CvgsTo]
    push_neg at hA ⊢
    refine ⟨1, zero_lt_one, ?_⟩
    intro N
    refine ⟨2 * N + 1, by rw [two_mul]; exact (le_add_self).trans (Nat.le_succ _), ?_⟩
    simp [pow_mul, pow_add]
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma CvgsTo.unique {a : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (ha' : CvgsTo a B) : A = B := by
  have : ∀ C, CvgsTo 0 C → C = 0 := by
    intro C hC
    apply abs_eq_zero.mp
    refine le_antisymm ?_ (abs_nonneg _)
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    specialize hN N le_rfl
    simpa using hN
  exact sub_eq_zero.mp (this _ <| by simpa using ha.sub ha')

set_option maxHeartbeats 0

lemma CvgsTo.subseq {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    CvgsTo (a ∘ φ) A := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  exact hN (φ n) (hn.trans <| hφ.id_le n)

lemma dvgs_of_cvgsTo_of_cvgsTo {a : ℕ → ℝ} {A B : ℝ} {φ ψ : ℕ → ℕ} (hφ : StrictMono φ)
    (hψ : StrictMono ψ) (ha : CvgsTo (a ∘ φ) A) (hb : CvgsTo (a ∘ ψ) B) (hAB : A ≠ B) :
    Dvgs a :=
fun _L hL => hAB <| (ha.unique <| hL.subseq hφ).trans <| (hL.subseq hψ).unique hb

example : Dvgs ((-1) ^ ·) := by
  have h₀ : CvgsTo (((-1) ^ ·) ∘ (2 * ·)) 1 := by
    convert cvgsTo_const_one; funext; simp [pow_mul]
  have h₁ : CvgsTo (((-1) ^ ·) ∘ (2 * · + 1)) (-1) := by
    convert cvgsTo_const (-1); funext; simp [pow_mul, pow_add]
  refine dvgs_of_cvgsTo_of_cvgsTo ?_ ?_ h₀ h₁ (by norm_num)
  · exact strictMono_mul_left_of_pos two_pos
  · exact (strictMono_mul_left_of_pos (two_pos : (0 : ℕ) < 2)).add_const 1

lemma range_bounded_iff {a : ℕ → ℝ} :
    Metric.Bounded (Set.range a) ↔ ∃ M, ∀ n, |a n| ≤ M := by
  simp_rw [Metric.bounded_iff_subset_ball (0 : ℝ), Set.range_subset_iff, Metric.mem_closedBall,
    Real.dist_eq, sub_zero]

def Eventually (P : ℕ → Prop) : Prop := ∃ N : ℕ, ∀ n ≥ N, P n

lemma eventually_of_forall {P : ℕ → Prop} (h : ∀ n, P n) : Eventually P :=
  ⟨0, fun n _ => h n⟩

lemma eventually_and {P Q : ℕ → Prop} :
    Eventually (fun n => P n ∧ Q n) ↔ Eventually P ∧ Eventually Q := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨⟨N, fun n hn => (hN n hn).left⟩, ⟨N, fun n hn => (hN n hn).right⟩⟩
  . rintro ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩
    exact ⟨max N₁ N₂, fun n hn =>
      ⟨hN₁ n ((le_max_left _ _).trans hn), hN₂ n ((le_max_right _ _).trans hn)⟩⟩

lemma Eventually.and {P Q : ℕ → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually (fun n => P n ∧ Q n) :=
  eventually_and.mpr ⟨hP, hQ⟩

lemma Eventually.imp_of_forall {P Q : ℕ → Prop} (h : ∀ n, P n → Q n) (hP : Eventually P) :
    Eventually Q := by
  obtain ⟨N, hN⟩ := hP
  exact ⟨N, fun n hn => h n (hN n hn)⟩

lemma Eventually.imp {P Q : ℕ → Prop} (h : Eventually (fun n => P n → Q n))
    (hP : Eventually P) : Eventually Q := by
  refine (h.and hP).imp_of_forall ?_
  exact fun n hn => hn.1 hn.2

lemma CvgsTo.nonneg_of_eventually_nonneg {a : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A)
    (h : Eventually (0 ≤ a ·)) : 0 ≤ A := by
  obtain ⟨N, hN⟩ := h
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha ε hε
  specialize hN (max N N₁) (le_max_left _ _)
  specialize hN₁ (max N N₁) (le_max_right _ _)
  replace hN₁ := (abs_lt.mp hN₁).right
  linarith


lemma CvgsTo.le_of_eventually_le {a b : ℕ → ℝ} {A B : ℝ} (ha : CvgsTo a A) (hb : CvgsTo b B)
    (h : Eventually (fun n => a n ≤ b n)) : A ≤ B := by
  simp (config := { singlePass := false }) [←sub_nonneg] at h ⊢
  simp [-sub_nonneg] at h ⊢
  exact (hb.sub ha).nonneg_of_eventually_nonneg h

lemma CvgsTo.squeeze {a b c : ℕ → ℝ} {A : ℝ} (ha : CvgsTo a A) (hc : CvgsTo c A)
    (h : Eventually (fun n => a n ≤ b n ∧ b n ≤ c n)) : CvgsTo b A := by
  intro ε hε
  specialize ha ε hε
  specialize hc ε hε
  rw [←Eventually] at ha hc ⊢
  refine ((h.and ha).and hc).imp_of_forall ?_
  rintro n ⟨⟨⟨hab, hbc⟩, ha⟩, hc⟩
  simp only [abs_lt] at ha hc ⊢
  cases ha with
  | _ ha₁ ha₂ =>
    cases hc with
    | _ hc₁ hc₂ =>
      constructor
      · linarith
      · linarith

lemma CvgsTo.of_eventually_abs_le {a b : ℕ → ℝ} {A : ℝ} (hb : CvgsTo b 0)
    (h : Eventually (fun n => |a n - A| ≤ b n)) : CvgsTo a A := by
  rw [cvgsTo_iff_cvgsTo_zero, cvgsTo_zero_iff_abs]
  refine cvgsTo_const_zero.squeeze hb ?_
  exact h.imp_of_forall fun n hn => ⟨abs_nonneg _, hn⟩

example : ∃ (a b : ℕ → ℝ) (A : ℝ), CvgsTo a A ∧ CvgsTo b A ∧ Eventually (fun n => a n < b n) :=
  ⟨_, _, 0, by simpa using cvgsTo_one_div_nat.neg, cvgsTo_one_div_nat,
    ⟨1, fun n => by simpa using id⟩⟩

def DvgsToInfty (a : ℕ → ℝ) : Prop := ∀ M, Eventually (M ≤ a ·)

lemma dvgsToInfty_iff {a : ℕ → ℝ} : DvgsToInfty a ↔ ∀ M > 0, Eventually (M ≤ a ·) := by
  constructor
  · exact fun h M _ => h M
  · intro h M
    by_cases hM : 0 < M
    · exact h M hM
    · push_neg at hM
      apply (h 1 zero_lt_one).imp_of_forall
      exact fun n hn => (hM.trans zero_le_one).trans hn

lemma DvgsToInfty.dvgs {a : ℕ → ℝ} (ha : DvgsToInfty a) : Dvgs a := by
  intro A hA
  specialize ha (A + 1)
  specialize hA 1 zero_lt_one
  rw [←Eventually] at hA
  obtain ⟨N, hN⟩ := ha.and hA
  specialize hN N le_rfl
  obtain ⟨h₁, h₂⟩ := hN
  linarith [abs_lt.mp h₂]

lemma Set.range_bddBelow_iff {a : ℕ → ℝ} : BddBelow (Set.range a) ↔ ∃ M, ∀ n, M ≤ a n := by
  simp [BddBelow, Set.Nonempty, mem_lowerBounds]

lemma Set.range_bddAbove_iff {a : ℕ → ℝ} : BddAbove (Set.range a) ↔ ∃ M, ∀ n, a n ≤ M := by
  simp [BddAbove, Set.Nonempty, mem_upperBounds]

lemma DvgsToInfty.add {a b : ℕ → ℝ} (ha : DvgsToInfty a) (hb : BddBelow (Set.range b)) :
    DvgsToInfty (a + b) := by
  obtain ⟨K, hK⟩ := Set.range_bddBelow_iff.mp hb
  intro M
  apply (ha (M - K)).imp_of_forall
  intro n haMK
  simpa using add_le_add haMK (hK n)

lemma DvgsToInfty.mul {a b : ℕ → ℝ} (ha : DvgsToInfty a) {K : ℝ} (hK : 0 < K)
    (hb : Eventually (K ≤ b ·)) : DvgsToInfty (a * b) := by
  rw [dvgsToInfty_iff]
  intro M hM
  apply ((ha (M / K)).and hb).imp_of_forall
  rintro n ⟨haMK, haK⟩
  simpa only [div_mul_cancel M hK.ne']
    using mul_le_mul haMK haK hK.le ((div_pos hM hK).le.trans haMK)

lemma DvgsToInfty.const_mul {a : ℕ → ℝ} (ha : DvgsToInfty a) {K : ℝ} (hK : 0 < K) :
    DvgsToInfty (a · * K) :=
  ha.mul hK (⟨0, fun _ _ => le_rfl⟩ : Eventually (fun _ => K ≤ K))

lemma DvgsToInfty.of_eventually_le {a b : ℕ → ℝ} (ha : DvgsToInfty a)
    (hb : Eventually (fun n => a n ≤ b n)) : DvgsToInfty b := by
  intro M
  apply ((ha M).and hb).imp_of_forall
  rintro n ⟨haM, hab⟩
  exact haM.trans hab

def DvgsToNegInfty (a : ℕ → ℝ) : Prop := ∀ M, Eventually (a · ≤ M)

lemma dvgsToNegInfty_iff {a : ℕ → ℝ} : DvgsToNegInfty a ↔ DvgsToInfty (-a) := by
  simp_rw [DvgsToNegInfty, DvgsToInfty, Pi.neg_apply, le_neg]
  exact ⟨fun h M => h (-M), fun h M => neg_neg M ▸ h (-M)⟩

lemma DvgsToInfty.cvgsTo_zero {a : ℕ → ℝ} (ha : DvgsToInfty a) : CvgsTo a⁻¹ 0 := by
  rw [cvgsTo_iff_forall_le]
  intro ε hε
  --rw [dvgsToInfty_iff] at ha
  apply (ha ε⁻¹).imp_of_forall
  intro n hn
  have han := (inv_pos.mpr hε).trans_le hn
  rw [←inv_le_inv han (inv_pos.mpr hε), inv_inv] at hn
  simp only [Pi.inv_apply, sub_zero, abs_inv]
  rwa [abs_of_nonneg han.le]

lemma dvgsToInfty_iff_inv_cvgsTo_zero {a : ℕ → ℝ} (ha : Eventually (0 < a ·)) :
    DvgsToInfty a ↔ CvgsTo a⁻¹ 0 := by
  constructor
  · exact DvgsToInfty.cvgsTo_zero
  · intro h
    rw [dvgsToInfty_iff]
    intro M hM
    apply (ha.and <| h M⁻¹ (inv_pos.mpr hM)).imp_of_forall
    rintro n ⟨han, haM⟩
    simp only [Pi.inv_apply, sub_zero, abs_of_pos (inv_pos.mpr han)] at haM
    exact ((inv_lt_inv han hM).mp haM).le

lemma bernoulli_inequality {r : ℝ} (hr : -1 ≤ r) : ∀ n : ℕ, 1 + n • r ≤ (1 + r) ^ n
| 0 => by simp
| 1 => by simp
| n + 2 => by
    have := bernoulli_inequality hr (n + 1)
    rw [nsmul_eq_mul, Nat.cast_succ, add_mul, ←add_assoc, pow_succ', mul_add,
      mul_one, ←nsmul_eq_mul]
    refine add_le_add this ?_
    by_cases hr' : 0 ≤ r
    · refine (mul_le_mul_of_nonneg_right ?_ hr')
      calc
        1 ≤ 1 + r := le_add_of_nonneg_right hr'
        _ ≤ (1 + r) ^ (n + 1) := le_self_pow (by linarith) n.succ_pos.ne'
    · push_neg at hr'
      refine (mul_le_mul_of_nonpos_right ?_ hr'.le)
      exact pow_le_one (n + 1) (by linarith) (by linarith)

lemma dvgsTo_arithmetic {r : ℝ} (hr : 0 < r) : DvgsToInfty (· • r) := by
  intro M
  obtain ⟨N, hN⟩ := Archimedean.arch M hr
  use N
  refine fun n hn => hN.trans <| (nsmul_le_nsmul_iff hr).mpr hn

lemma dvgsTo_geometric {r : ℝ} (hr : 1 < r) : DvgsToInfty (r ^ ·) := by
  rw [←add_sub_cancel' 1 r, add_sub_assoc]
  refine DvgsToInfty.of_eventually_le ?_ ⟨0, fun n _ => bernoulli_inequality (by linarith) n⟩
  have : DvgsToInfty (· • (r - 1) + 1) := by
    refine (dvgsTo_arithmetic (by linarith : 0 < r - 1)).add ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact le_rfl
  convert this using 1
  ext
  rw [add_comm]

lemma cvgsTo_geometric {r : ℝ} (hr : |r| < 1) : CvgsTo (r ^ ·) 0 := by
  rw [cvgsTo_zero_iff_abs]
  simp_rw [abs_pow]
  by_cases hr' : r = 0
  · simp [hr', zero_pow]
    refine cvgsTo_const_zero.of_finite_ne ?_
    convert Set.finite_singleton 0
    ext
    simp only [Pi.zero_apply, Set.mem_setOf_eq, Set.mem_singleton_iff]
    refine ⟨Function.mtr fun hx => by simp [hx], fun hx => by simp [hx]⟩
  · replace hr' := abs_pos.mpr hr'
    convert (dvgsTo_geometric <| one_lt_inv hr' hr).cvgsTo_zero using 1
    ext
    simp

lemma _root_.Monotone.cvgsTo {a : ℕ → ℝ} (ha : Monotone a) {M : ℝ} (ha' : ∀ n, a n ≤ M) :
    CvgsTo a (iSup a) := by
  have h_bdd : BddAbove (Set.range a) := ⟨M, by rintro _ ⟨n, rfl⟩; exact ha' n⟩
  have := isLUB_ciSup h_bdd
  intros ε hε
  obtain ⟨-, ⟨N, rfl⟩, hN, hN'⟩ := this.exists_between_sub_self hε
  refine ⟨N, fun n hn => abs_lt.mpr ⟨?_, ?_⟩⟩
  · linarith [hN.trans_le <| ha hn]
  · linarith [le_ciSup h_bdd n]

lemma _root_.Antitone.cvgsTo {a : ℕ → ℝ} (ha : Antitone a) {M : ℝ} (ha' : ∀ n, M ≤ a n) :
    CvgsTo a (iInf a) := by
  have : CvgsTo (- -a) (-iSup (-a)) := (ha.neg.cvgsTo <| fun n => neg_le_neg (ha' n)).neg
  rw [iSup, neg_neg, ←csInf_neg (Set.range_nonempty (-a)), Set.neg_range] at this
  · simp_rw [Pi.neg_apply, neg_neg] at this
    exact this
  · exact ⟨-M, by rintro _ ⟨n, rfl⟩; exact neg_le_neg (ha' n)⟩

lemma _root_.Monotone.dvgsToInfty {a : ℕ → ℝ} (ha : Monotone a) (ha' : ∀ M, ∃ n, M < a n) :
    DvgsToInfty a := by
  intro M
  obtain ⟨N, hN⟩ := ha' M
  refine ⟨N, fun n hn => ?_⟩
  exact hN.le.trans <| ha hn

lemma _root_.Monotone.cvgs_or_dvgs {a : ℕ → ℝ} (ha : Monotone a) :
    CvgsTo a (iSup a) ∨ DvgsToInfty a := by
  by_cases ha' : ∃ M, ∀ n, a n ≤ M
  · obtain ⟨M, hM⟩ := ha'
    exact Or.inl <| ha.cvgsTo hM
  · push_neg at ha'
    exact Or.inr <| ha.dvgsToInfty ha'

open BigOperators

example {r : ℝ} (hr : r ≠ 1) (n : ℕ) : (∑ i in Finset.range n, r ^ i) = (r ^ n - 1) / (r - 1) :=
  geom_sum_eq hr n

example {r : ℝ} (hr : |r| < 1) : CvgsTo (∑ i in Finset.range ·, r ^ i) (1 / (1 - r)) := by
  have hr' : r ≠ 1 := fun h => by rw [h] at hr; norm_num at hr
  simp_rw [geom_sum_eq hr']
  have := ((cvgsTo_geometric hr).sub (cvgsTo_const' 1)).div (cvgsTo_const' (r - 1))
    (fun _ => hr' <| by linarith)
  convert this using 1
  simp only [one_div, zero_sub, neg_div, neg_inv, neg_sub]

noncomputable def nr_sqrt_seq (A a₀ : ℝ) : ℕ → ℝ
| 0 => a₀
| Nat.succ n => (nr_sqrt_seq A a₀ n + A / nr_sqrt_seq A a₀ n) / 2

-- this could get *very* messy

def AccPt (S : Set ℝ) (x : ℝ) : Prop := ∀ ε > 0, (S ∩ (Metric.ball x ε \ {x})).Nonempty

lemma AccPt.some_mem {S : Set ℝ} {x : ℝ} (h : AccPt S x) {ε : ℝ} (hε : 0 < ε) :
    (h ε hε).some ∈ S :=
  ((Set.mem_inter_iff _ _ _).mp (h ε hε).some_mem).1

lemma AccPt.some_abs_lt {S : Set ℝ} {x : ℝ} (h : AccPt S x) {ε : ℝ} (hε : 0 < ε) :
    |(h ε hε).some - x| < ε := by
  have := Set.diff_subset _ _ ((Set.mem_inter_iff _ _ _).mp (h ε hε).some_mem).2
  rwa [Metric.mem_ball, Real.dist_eq] at this

lemma AccPt.some_ne {S : Set ℝ} {x : ℝ} (h : AccPt S x) {ε : ℝ} (hε : 0 < ε) :
    (h ε hε).some ≠ x := by
  have := ((Set.mem_diff _).mp ((Set.mem_inter_iff _ _ _).mp (h ε hε).some_mem).2).2
  rwa [Set.mem_singleton_iff] at this

lemma AccPt.some_abs_pos {S : Set ℝ} {x : ℝ} (h : AccPt S x) {ε : ℝ} (hε : 0 < ε) :
    0 < |(h ε hε).some - x| :=
  lt_of_le_of_ne (abs_nonneg _) (dist_ne_zero.mpr (h.some_ne hε)).symm

lemma AccPt.inter_ball {S : Set ℝ} {x : ℝ} (h : AccPt S x) {ε : ℝ} (hε : 0 < ε) :
    AccPt (S ∩ Metric.ball x ε) x := by
  intro ε' hε'
  obtain ⟨y, y_mem, hy⟩ := h (min ε ε') (lt_min hε hε')
  rw [Set.mem_diff] at hy
  rcases hy with ⟨y_mem', y_nmem⟩
  use y
  refine ⟨⟨y_mem, ?_⟩, ?_⟩
  · exact Metric.ball_subset_ball (min_le_left _ _) y_mem'
  · exact Set.mem_diff_of_mem (Metric.ball_subset_ball (min_le_right _ _) y_mem') y_nmem

noncomputable def AccPt.seqAux {S : Set ℝ} {x : ℝ} (h : AccPt S x) : ℕ → ℝ × {r : ℝ // 0 < r}
| 0 => ((h 1 one_pos).some, ⟨min (|(h 1 one_pos).some - x|) 1, lt_min (h.some_abs_pos one_pos) one_pos⟩)
| (n + 1) => let d := (h.seqAux n).2
    ((h d.1 d.2).some, ⟨min (|(h d.1 d.2).some - x|) (1 / (n + 2) : ℝ),
    lt_min (h.some_abs_pos d.2) (by positivity)⟩)

noncomputable def AccPt.seq {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) : ℝ :=
  (h.seqAux n).1

lemma AccPt.seqAux_snd_eq_abs {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    ((h.seqAux n).2.1 : ℝ) = min (|h.seq n - x|) (1 / (n + 1) : ℝ) := by
  cases n with
  | zero =>
      simp only [Nat.zero_eq, Nat.cast_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true,
        div_self, ge_iff_le]
      rfl
  | succ k =>
      simp only [Nat.cast_succ, add_assoc, one_add_one_eq_two]
      rfl

lemma AccPt.abs_seq_pos {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    0 < |h.seq n - x| := by
  refine lt_of_lt_of_le ?_ (min_le_left _ (1 / (n + 1) : ℝ))
  rw [←h.seqAux_snd_eq_abs]
  exact (h.seqAux n).2.2

lemma AccPt.seq_zero {S : Set ℝ} {x : ℝ} (h : AccPt S x) :
    h.seq 0 = (h 1 zero_lt_one).some :=
  rfl

lemma AccPt.seq_succ {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    h.seq (n + 1) = (h (min (|h.seq n - x|) (1 / (n + 1)))
      (lt_min (h.abs_seq_pos n) (by positivity))).some := by
  simp_rw [←h.seqAux_snd_eq_abs];
  rfl

lemma AccPt.seq_mem {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    h.seq n ∈ S := by
  cases n with
  | zero => rw [h.seq_zero]; exact h.some_mem zero_lt_one
  | succ k => rw [h.seq_succ]; exact h.some_mem (lt_min (h.abs_seq_pos k) (by positivity))


lemma AccPt.abs_seq_succ_lt_min {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    |h.seq (n + 1) - x| < min (|h.seq n - x|) (1 / (n + 1)) := by
  rw [h.seq_succ]
  exact h.some_abs_lt <| lt_min (h.abs_seq_pos n) (by positivity)

lemma AccPt.abs_seq_succ_lt {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    |h.seq (n + 1) - x| < |h.seq n - x| :=
  lt_of_lt_of_le (h.abs_seq_succ_lt_min n) (min_le_left _ _)

lemma AccPt.abs_seq_succ_lt_one_div {S : Set ℝ} {x : ℝ} (h : AccPt S x) (n : ℕ) :
    |h.seq (n + 1) - x| < 1 / (n + 1) :=
  lt_of_lt_of_le (h.abs_seq_succ_lt_min n) (min_le_right _ _)

lemma AccPt.abs_seq_strictAnti {S : Set ℝ} {x : ℝ} (h : AccPt S x) :
    StrictAnti (|h.seq · - x|) :=
  strictAnti_nat_of_succ_lt h.abs_seq_succ_lt

lemma AccPt.seq_injective {S : Set ℝ} {x : ℝ} (h : AccPt S x) :
    Function.Injective h.seq := by
  have h_ne_of_lt : ∀ {n m} (_hnm : n < m), h.seq n ≠ h.seq m := by
    intro n m hnm h_eq
    exact (h.abs_seq_strictAnti hnm).ne' <| congrArg (|· - x|) h_eq
  have key := fun {n m} => mt (@h_ne_of_lt n m)
  push_neg at key
  exact fun n m h_eq => le_antisymm (key h_eq.symm) (key h_eq)

lemma AccPt.seq_cvgsTo {S : Set ℝ} {x : ℝ} (h : AccPt S x) :
    CvgsTo h.seq x := by
  refine cvgsTo_one_div_nat.of_eventually_abs_le ⟨1, fun n hn => ?_⟩
  simp (config := { singlePass := true }) only [←Nat.succ_pred_eq_of_pos hn]
  simpa using (h.abs_seq_succ_lt_one_div n.pred).le

lemma AccPt.infinite {S : Set ℝ} {x : ℝ} (h : AccPt S x) : Set.Infinite S := by
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective h.seq_injective)
  rintro _ ⟨n, rfl⟩
  exact h.seq_mem n

lemma AccPt.mono {S S' : Set ℝ} {x : ℝ} (h : AccPt S x) (h' : S ⊆ S') : AccPt S' x :=
  fun ε hε => (h ε hε).mono (Set.inter_subset_inter_left _ h')

lemma CvgsTo.accPt {a : ℕ → ℝ} {S : Set ℝ} {x : ℝ} (ha : CvgsTo a x)
    (haS : Set.range a ⊆ S \ {x}) : AccPt S x := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  rw [←Set.inter_diff_assoc, Set.inter_comm, Set.inter_diff_assoc]
  exact ⟨a N, Set.mem_inter (hN N le_rfl) (haS ⟨N, rfl⟩)⟩

namespace BolzanoWeierstrass

lemma bisect {S : Set ℝ} {a : ℝ × ℝ}
    (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    ∃ b : ℝ × ℝ, Set.Infinite (S ∩ Set.Icc b.1 b.2) ∧
      a.1 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ a.2 ∧
      |b.2 - b.1| = |a.2 - a.1| * 2⁻¹ := by
  have ha : a.1 ≤ a.2 := by
    by_contra h
    rw [Set.Icc_eq_empty h, Set.inter_empty] at h_inf
    exact Set.finite_empty.not_infinite h_inf
  have hab₁ : a.1 ≤ (a.1 + a.2) / 2 := by linarith
  have hab₂ : (a.1 + a.2) / 2 ≤ a.2 := by linarith
  rw [←Set.Icc_union_Icc_eq_Icc hab₁ hab₂, Set.inter_union_distrib_left, Set.infinite_union]
    at h_inf
  cases h_inf with
  | inl h_inf =>
      refine ⟨(a.1, (a.1 + a.2) / 2), h_inf, le_rfl, hab₁, hab₂, ?_⟩
      simp only
      rw [abs_sub_comm, add_div, ←sub_sub, sub_half, ←sub_div, abs_div, abs_two, abs_sub_comm,
        div_eq_mul_inv]
  | inr h_inf =>
      refine ⟨((a.1 + a.2) / 2, a.2), h_inf, hab₁, hab₂, le_rfl, ?_⟩
      simp only
      rw [add_div, add_comm, ←sub_sub, sub_half, ←sub_div, abs_div, abs_two, abs_sub_comm,
        div_eq_mul_inv]

noncomputable def seqPair {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    ℕ → {b : ℝ × ℝ // Set.Infinite (S ∩ Set.Icc b.1 b.2)}
| 0 => ⟨a, h_inf⟩
| n + 1 => ⟨Classical.choose <| bisect (seqPair h_inf n).prop,
    (Classical.choose_spec <| bisect (seqPair h_inf n).prop).1⟩

noncomputable def seqLower {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    ℕ → ℝ :=
  fun n ↦ (seqPair h_inf n).val.1

lemma seqLower_succ_eq_choose {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2))
    (n : ℕ) : seqLower h_inf (n + 1) = (Classical.choose <| bisect (seqPair h_inf n).prop).1 := by
  rfl

noncomputable def seqUpper {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    ℕ → ℝ :=
  fun n ↦ (seqPair h_inf n).val.2

lemma seqLower_monotone {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    Monotone (seqLower h_inf) :=
  monotone_nat_of_le_succ <| fun n => (Classical.choose_spec <| bisect (seqPair h_inf n).prop).2.1

lemma seqUpper_antitone {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    Antitone (seqUpper h_inf) :=
  antitone_nat_of_succ_le <| fun n =>
    (Classical.choose_spec <| bisect (seqPair h_inf n).prop).2.2.2.1

lemma seqLower_le_seqUpper {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    seqLower h_inf ≤ seqUpper h_inf := by
  intro n
  cases n with
  | zero =>
      simp only [seqLower, seqUpper, seqPair]
      by_contra h
      rw [Set.Icc_eq_empty h, Set.inter_empty] at h_inf
      exact Set.finite_empty.not_infinite h_inf
  | succ k => exact (Classical.choose_spec <| bisect (seqPair h_inf k).prop).2.2.1

lemma seqUpper_sub_seqLower {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2))
    (n : ℕ) : |seqUpper h_inf n - seqLower h_inf n| = |a.2 - a.1| * (2⁻¹) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ k hk =>
      rw [pow_succ', ←mul_assoc, ←hk]
      exact (Classical.choose_spec <| bisect (seqPair h_inf k).prop).2.2.2.2

lemma infinite_Icc_seqLower_seqUpper {S : Set ℝ} {a : ℝ × ℝ}
    (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) (n : ℕ) :
    Set.Infinite (S ∩ Set.Icc (seqLower h_inf n) (seqUpper h_inf n)) := by
  cases n with
  | zero => exact h_inf
  | succ k => exact (seqPair h_inf (k + 1)).prop

lemma seqLower_cvgsTo {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    CvgsTo (seqLower h_inf) (iSup <| seqLower h_inf) := by
  refine (seqLower_monotone h_inf).cvgsTo <| fun n =>
    (seqLower_le_seqUpper h_inf n).trans (seqUpper_antitone h_inf <| zero_le n)

lemma seqUpper_cvgsTo {S : Set ℝ} {a : ℝ × ℝ} (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    CvgsTo (seqUpper h_inf) (iInf <| seqUpper h_inf) := by
  refine (seqUpper_antitone h_inf).cvgsTo <| fun n =>
    (seqLower_monotone h_inf <| zero_le n).trans (seqLower_le_seqUpper h_inf n)

lemma iSup_seqLower_eq_iInf_seqUpper {S : Set ℝ} {a : ℝ × ℝ}
    (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) :
    (iSup <| seqLower h_inf) = (iInf <| seqUpper h_inf) := by
  have h₁ := (seqUpper_cvgsTo h_inf).sub (seqLower_cvgsTo h_inf)
  have h₂ : CvgsTo (fun n ↦ |a.2 - a.1| * (2⁻¹) ^ n) 0 := by
    have := (cvgsTo_geometric
      (by rw [abs_of_pos (by positivity : 0 < (2⁻¹ : ℝ))]; norm_num : |(2⁻¹ : ℝ)| < 1)).const_mul
      (|a.2 - a.1|)
    simpa
  have h₃ : CvgsTo (seqUpper h_inf - seqLower h_inf) (0 : ℝ) := by
    refine h₂.of_eventually_abs_le <| eventually_of_forall (fun n => ?_)
    simpa only [sub_zero, seqUpper_sub_seqLower h_inf, Pi.sub_apply] using le_rfl
  symm
  rw [←sub_eq_zero]
  exact h₁.unique h₃

lemma seqLower_le_iSup {S : Set ℝ} {a : ℝ × ℝ}
    (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) (n : ℕ) :
    seqLower h_inf n ≤ (iSup <| seqLower h_inf) := by
  refine le_ciSup ⟨a.2, ?_⟩ n
  rintro _ ⟨m, rfl⟩
  exact (seqLower_le_seqUpper h_inf m).trans <| seqUpper_antitone h_inf <| zero_le m

lemma iSup_le_seqUpper {S : Set ℝ} {a : ℝ × ℝ}
    (h_inf : Set.Infinite (S ∩ Set.Icc a.1 a.2)) (n : ℕ) :
    (iSup <| seqLower h_inf) ≤ seqUpper h_inf n := by
  rw [iSup_seqLower_eq_iInf_seqUpper]
  refine ciInf_le ⟨a.1, ?_⟩ n
  rintro _ ⟨m, rfl⟩
  exact (seqLower_monotone h_inf <| zero_le m).trans (seqLower_le_seqUpper h_inf m)

lemma exists_accPt {S : Set ℝ} (h_bdd : Metric.Bounded S) (h_inf : Set.Infinite S) :
    ∃ x, AccPt S x := by
  obtain ⟨M, hM⟩ := (Metric.bounded_iff_subset_ball (0 : ℝ)).mp h_bdd
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hM
  rw [←Set.inter_eq_left_iff_subset.mpr hM] at h_inf
  set M' := (-M, M)
  change Set.Infinite (S ∩ Set.Icc M'.1 M'.2) at h_inf
  use iSup (seqLower h_inf)
  have : ∀ n, ∃ s : ℝ,
      s ∈ (S \ {iSup (seqLower h_inf)}) ∩ Set.Icc (seqLower h_inf n) (seqUpper h_inf n) := by
    intro n
    obtain ⟨s, hs_mem, hs_not⟩ := (infinite_Icc_seqLower_seqUpper h_inf n).exists_not_mem_finset
      {iSup (seqLower h_inf)}
    use s
    refine Set.mem_inter (Set.mem_diff_of_mem (Set.mem_of_mem_inter_left hs_mem) ?_) ?_
    · simpa using hs_not
    · exact Set.mem_of_mem_inter_right hs_mem
  choose a h using this
  have ha : CvgsTo a (iSup <| seqLower h_inf) := (seqLower_cvgsTo h_inf).squeeze
    ((iSup_seqLower_eq_iInf_seqUpper h_inf).symm ▸ seqUpper_cvgsTo h_inf) <|
    eventually_of_forall fun n => (Set.mem_of_mem_inter_right (h n) : _)
  refine ha.accPt ?_
  rintro _ ⟨n, rfl⟩
  exact Set.mem_of_mem_inter_left (h n)

end BolzanoWeierstrass

lemma Cauchy.cvgsTo {a : ℕ → ℝ} (ha : Cauchy a) : ∃ A : ℝ, CvgsTo a A := by
    by_cases h : (Set.range a).Finite
    · have foo : ∃ ε > 0, ∀ x ∈ Set.range a, ∀ y ∈ Set.range a, x ≠ y → ε ≤ |x - y| := by
        refine h.induction_on ⟨1, zero_lt_one, fun x hx => hx.elim⟩ ?_
        rintro x s hx hs ⟨ε, hε, h'⟩
        by_cases hs' : s = ∅
        · simpa [hs'] using ⟨ε, hε⟩
        · rw [←Ne.def, ←Set.nonempty_iff_ne_empty] at hs'
          obtain ⟨z, z_mem, hz⟩ := s.exists_min_image (fun y ↦ |x - y|) hs hs'
          have hxz : x ≠ z := mt (fun h' => h' ▸ z_mem) hx
          have hxz' : 0 < |x - z| := abs_pos.mpr (sub_ne_zero.mpr hxz)
          refine  ⟨min ε (|x - z|), lt_min hε hxz', fun y hy w hw hyw => ?_⟩
          rw [Set.mem_insert_iff] at hy hw
          rcases hy with (rfl | hy) <;> rcases hw with (rfl | hw)
          · contradiction
          · exact (min_le_right _ _).trans (hz w hw)
          · exact (min_le_right _ _).trans (abs_sub_comm y w ▸ hz y hy)
          · exact (min_le_left _ _).trans (h' y hy w hw hyw)
      have eventually_eq : ∃ x, ∃ N, ∀ n ≥ N, a n = x := by
        obtain ⟨ε, hε, haε⟩ := foo
        obtain ⟨N, hN⟩ := ha ε hε
        refine ⟨a N, N, fun n hn => ?_⟩
        replace haε := mt <| haε (a n) ⟨n, rfl⟩ (a N) ⟨N, rfl⟩
        push_neg at haε
        exact haε <| hN n N hn le_rfl
      obtain ⟨A, N, hN⟩ := eventually_eq
      use A
      refine fun ε hε => ⟨N, fun n hn => ?_⟩
      simpa [hN n hn] using hε
    · replace h : Set.Infinite (Set.range a) := h
      obtain ⟨A, hA⟩ := BolzanoWeierstrass.exists_accPt ha.bounded h
      use A
      rw [cvgsTo_iff_const_mul (by positivity : (0 : ℝ) < 3)]
      intro ε hε
      obtain ⟨N, hN⟩ := ha ε hε
      replace hA := (hA.inter_ball hε).infinite
      obtain ⟨x, hx_mem, hx_nmem⟩ := hA.exists_not_mem_finset <| (Finset.range N).image a
      rw [Set.mem_inter_iff] at hx_mem
      rcases hx_mem with ⟨⟨n, rfl⟩, hn_mem⟩
      refine ⟨N, fun m hm => ?_⟩
      have hn : n ≥ N := by
        by_contra' hn'
        exact hx_nmem <| Finset.mem_image.mpr ⟨n, by simpa using hn', rfl⟩
      calc
        |a m - A| = |(a m - a N) + (a N - a n) + (a n - A)| := by ring_nf
        _         ≤ |a m - a N| + |a N - a n| + |a n - A| := abs_add_three _ _ _
        _         < ε + ε + ε := by
          refine add_lt_add (add_lt_add (hN m N hm le_rfl) (hN N n le_rfl hn)) ?_
          simpa using hn_mem
        _         = 3 * ε := by ring

lemma cauchy_iff_cvgsTo {a : ℕ → ℝ} : Cauchy a ↔ ∃ A : ℝ, CvgsTo a A := by
  refine ⟨fun ha => ha.cvgsTo, ?_⟩
  rintro ⟨A, hA⟩
  exact hA.cauchy


end Hidden

namespace Hidden2

def SeqCvgsTo (a : ℕ → ℝ) (A : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - A| < ε

def SeqDvgsToInfty (a : ℕ → ℝ) : Prop :=
∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, M ≤ a n

def FunCvgsToAtInfty (f : ℝ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℝ, ∀ x ≥ N, |f x - L| < ε

def FunOrSeqCvgsAtInfty {X : Type _} [SemilatticeSup X] (f : X → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : X, ∀ x ≥ N, |f x - L| < ε

lemma FunOrSeq₁ (a : ℕ → ℝ) (A : ℝ) : SeqCvgsTo a A = FunOrSeqCvgsAtInfty a A := rfl
lemma FunOrSeq₂ (f : ℝ → ℝ) (L : ℝ) : FunCvgsToAtInfty f L = FunOrSeqCvgsAtInfty f L := rfl

def FunCvgsToAt (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

def FunCvgsToAtRight (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - a ∧ x - a < δ → |f x - L| < ε

def FunCvgsToAtLeft (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < a - x ∧ a - x < δ → |f x - L| < ε

/-
For functions `f : ℝ → ℝ` we can contemplate a bunch of different limits:

We can: converge to L, diverge to ∞, diverge to -∞

as: x → a, x → ∞, x → -∞, x → a⁺, x → a⁻, |x| → ∞.

Already that's 18 different kinds of limits. Yuck! We would have to prove lemmas about *all* of
these.

But, notice how all of these statements are similar. Let's try to understand them better.

They all have the form: ∀ ... ∃ ... ∀ ... → ...

we can think of the ∃ ∀ as an eventually statement

But we can also do it slightly differently

Note that `|f x - L| < ε` is the same thing as `f x ∈ (L - ε, L + ε)`, and the latter is a special
kind of set involving `L`. likewise `0 < |x - a| < δ` is the same as `x ∈ (a - δ, a) ∪ (a, a + δ)`
And `0 < x - a < δ` is the same same `x ∈ (a, a + δ)`. Similarly, `x ≥ N` is the same as
`x ∈ [N, ∞)`.
-/

def FunCvgsToAtInfty' (f : ℝ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℝ, ∀ x, x ∈ Set.Ici N → f x ∈ Set.Ioo (L - ε) (L + ε)

def FunCvgsToAtInfty'' (f : ℝ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℝ, ∀ x, x ∈ Set.Ici N → x ∈ f ⁻¹' Set.Ioo (L - ε) (L + ε)

def FunCvgsToAtInfty''' (f : ℝ → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : ℝ, Set.Ici N ⊆ f ⁻¹' Set.Ioo (L - ε) (L + ε)

/-
def FunOrSeqCvgsAtInfty {X : Type _} [SemilatticeSup X] (f : X → ℝ) (L : ℝ) : Prop :=
∀ ε > 0, ∃ N : X, ∀ x ≥ N, |f x - L| < ε

lemma FunOrSeq₁ (a : ℕ → ℝ) (A : ℝ) : SeqCvgsTo a A = FunOrSeqCvgsAtInfty a A := rfl
lemma FunOrSeq₂ (f : ℝ → ℝ) (L : ℝ) : FunCvgsToAtInfty f L = FunOrSeqCvgsAtInfty f L := rfl

def FunCvgsToAt (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

def FunCvgsToAtRight (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < x - a ∧ x - a < δ → |f x - L| < ε

def FunCvgsToAtLeft (f : ℝ → ℝ) (L : ℝ) (a : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, 0 < a - x ∧ a - x < δ → |f x - L| < ε
-/

/-
So we can think of limits as given two collections of special sets (in the domain and codomain),
for every special set in the codomain, there is a special set in the domain contained in the
preimage.

Now the only question is: what rules do we need to have for these special sets?

* They should be closed under finite intersections
* It should be a nonempty collection
* (less obvious): it should be closed under supersets. One way to think about this is that we just
  want the preimage of a special set to be special. However, making sure it has *exactly* the form
  is likely not to be the case (ever!), but the condition is that we just want it to contain one
  of these special sets, and if the special sets are closed under supersets, then we have what we
  want.

Such a collection of sets is called a *filter*. A subcollection of a filter which generates the
filter by taking supersets if called a *filter basis*.

In particular, a nonempty collection of sets closed under finite intersections is a filter basis
for the filter consisting of the supersets of those sets
-/

#print Filter

/-
One should think of filters as "generalized sets".

-/

end Hidden2
