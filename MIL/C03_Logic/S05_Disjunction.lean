import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  -- `0 ≤ x` かどうかで場合分けを行う
  let xsign := le_or_gt 0 x
  cases xsign

  case inl h =>
    rw [abs_of_nonneg h]

  case inr h =>
    rw [abs_of_neg h]
    simp
    rw [@le_iff_lt_or_eq]
    left
    assumption

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  let xsign := le_or_gt 0 x
  cases xsign

  case inl h =>
    rw [abs_of_nonneg h]
    simpa

  case inr h =>
    rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  let sign := le_or_gt 0 (x + y)
  cases sign

  case inl h =>
    rw [abs_of_nonneg h]
    gcongr
    all_goals
      exact le_abs_self _

  case inr h =>
    rw [abs_of_neg h]
    have hx := neg_le_abs_self x
    have hy := neg_le_abs_self y
    linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  case mp =>
    intro h
    cases le_or_gt 0 y
    case inl hy =>
      rw [abs_of_nonneg hy] at h
      left
      assumption
    case inr hy =>
      rw [abs_of_neg hy] at h
      right
      assumption
    done
  case mpr =>
    intro h
    rcases h with hl | hr
    case inl =>
      cases le_or_gt 0 y
      case inl hy =>
        rw [abs_of_nonneg hy]
        assumption
      case inr hy =>
        rw [abs_of_neg hy]
        calc
          x < y := hl
          _ < 0 := hy
          _ < - y := by linarith
    case inr =>
      calc
        x < -y := hr
        _ ≤ |y| := neg_le_abs_self y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  case mp =>
    intro h
    cases le_or_gt 0 x
    case inl hx =>
      rw [abs_of_nonneg hx] at h
      constructor
      · linarith
      · assumption
    case inr hx =>
      rw [abs_of_neg hx] at h
      constructor
      · linarith
      focus
        calc
          x < 0 := by linarith
          _ < -x := by linarith
          _ < y := by linarith
  case mpr =>
    intro h
    rcases h with ⟨hl, hr⟩
    rcases le_or_gt 0 x with pos | neg
    focus
      rw [abs_of_nonneg pos]
      assumption
    focus
      rw [abs_of_neg neg]
      linarith
  done

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  obtain ⟨x, y, h⟩ := h
  rcases h with h | h
  all_goals
    rw [h]
    linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [← @mul_self_eq_one_iff]
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rwa [← @sq_eq_sq_iff_eq_or_eq_neg]

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [← @mul_self_eq_one_iff]
  rw [← h]
  ring

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rwa [← @sq_eq_sq_iff_eq_or_eq_neg]

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  tauto
