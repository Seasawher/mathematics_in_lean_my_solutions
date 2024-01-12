import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

#check max_le

#check le_max_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left
  done

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  focus
    aesop
  focus
    aesop

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  aesop

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  focus
    exact aux _ _ _
  focus
    by_cases _h : a ≤ b
    focus
      simp
      exact le_total a b
    focus
      simp
      exact le_total a b

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have : |a| ≤ |a - b| + |b| := by
    nth_rw 1 [show a = (a - b) + b from by abel]
    refine abs_add (a - b) ?_
  rw [@tsub_le_iff_right]
  assumption
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  have ⟨v, hv⟩ := h
  use y * z + x + x * v * v
  rw [hv]
  ring
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  repeat
    apply dvd_gcd
    · exact Nat.gcd_dvd_right _ _
    · exact Nat.gcd_dvd_left _ _
  done
end
