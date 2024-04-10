import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Basic
import MIL.Common

example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  induction' n with n ih
  · simp [fac]
  focus
    by_cases h : n ≤ 0 <;> simp_all [fac]
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
      _ = 2 ^ (n - 1) * 2 := by ring
      _ ≤ fac n * 2 := by gcongr
      _ = 2 * fac n := by ring
      _ ≤ (n + 1) * fac n := by gcongr; omega
section

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl

example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · rw [fac, prod_range_zero]
  rw [fac, ih, prod_range_succ, mul_comm]

example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih, Nat.succ_eq_add_one]
  ring

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by simp_arith)
  induction' n with k ih

  case zero =>
    simp

  case succ =>
    rw [Finset.sum_range_succ]
    rw [show 6 * (∑ x in range (k + 1), x ^ 2 + (k + 1) ^ 2) = 6 * ∑ x in range (k + 1), x ^ 2 + 6 * (k + 1) ^ 2 by ring]
    rw [← ih]
    rw [show Nat.succ k = k + 1 from by rfl]
    ring

example (n : ℚ) : (4 + 4 * n) / 4 = 4 / 4 + n:= by
  have : 4 ≠ 0 := by norm_num
  field_simp
  ring
end

inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

@[simp]
theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' n with k ih

  case zero =>
    rw [zero_add]
    simp [add]

  case succ m =>
    rename_i c
    rw [add, succ_add]
    rw [ih]
    rw [succ_add, add]

theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' k with k ih
  case zero =>
    simp [add, mul]

  case succ =>
    rw [add, mul]
    rw [ih]
    rw [show mul m (succ k) = add (mul m k) m from by rfl]
    rw [add_assoc]

infix:65 " + " => add

infix:70 " * " => mul

theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih

  case zero =>
    rfl

  case succ =>
    rw [mul, ih]
    rfl

theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih
  case zero =>
    rfl

  case succ =>
    rw [mul]
    rw [ih]; clear ih
    rw [mul, add, add]
    rw [show (m * n + n) + m  = m * n + (n + m) from by rw [add_assoc]]
    rw [show (m * n + m) + n = m * n + (m + n) from by rw [add_assoc]]
    rw [add_comm n m]

theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with k ih
  . rw [zero_mul, mul]
  · rw [mul]
    rw [succ_mul]
    rw [ih]

end MyNat
