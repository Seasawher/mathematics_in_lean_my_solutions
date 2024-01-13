import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- 後で使うので名前を付けておく
lemma my_inf_comm : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  simp

  apply le_inf
  simp

  exact inf_le_left

@[simp]
lemma inf_triple_left : x ⊓ y ⊓ z ≤ x := by
  -- 補題を用意する
  calc x ⊓ y ⊓ z
    _ ≤ x ⊓ y := @inf_le_left _ _ (x ⊓ y) z
    _ ≤ x := by apply inf_le_left

@[simp]
lemma inf_triple_mid : x ⊓ y ⊓ z ≤ y := by
  -- 補題を用意する
  calc x ⊓ y ⊓ z
    _ ≤ x ⊓ y := @inf_le_left _ _ (x ⊓ y) z
    _ ≤ y := by apply inf_le_right

@[aesop safe]
lemma my_inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  simp

  rw [my_inf_comm]
  simp

-- 後で使うので名前を付けておく
lemma my_sup_comm : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  simp

  apply sup_le
  simp

  exact le_sup_left

@[simp]
lemma sup_triple_left : x ≤ x ⊔ y ⊔ z := by
  -- 補題を用意する
  calc x
    _ ≤ x ⊔ y := le_sup_left
    _ ≤ x ⊔ y ⊔ z := le_sup_left

@[simp]
lemma sup_triple_mid : y ≤ x ⊔ y ⊔ z := by
  -- 補題を用意する
  calc y
    _ ≤ x ⊔ y := le_sup_right
    _ ≤ x ⊔ y ⊔ z := le_sup_left

@[aesop safe]
lemma my_sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  simp

  all_goals
    rw [my_sup_comm]
    simp

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  simp

  apply le_inf
  all_goals
    simp

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  simp

  exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

@[gcongr]
lemma my_sup_le_sup_right (h : a ≤ b) : a ⊔ c ≤ b ⊔ c := by
  -- 補題を用意する
  apply sup_le

  focus
    calc a
      _ ≤ b := h
      _ ≤ b ⊔ c := le_sup_left

  focus
    exact le_sup_right

@[gcongr]
lemma my_inf_le_inf_right (h : a ≤ b) : a ⊓ c ≤ b ⊓ c := by
  -- 補題を用意する
  apply le_inf

  focus
    calc a ⊓ c
      _ ≤ a := inf_le_left
      _ ≤ b := h

  focus
    exact inf_le_right

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  show a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)
  apply le_antisymm
  all_goals simp_all

  focus
    show b ⊓ c ≤ a ⊔ ((a ⊔ b) ⊓ c)
    rw [← @ge_iff_le]
    calc a ⊔ (a ⊔ b) ⊓ c
      _ ≥ (a ⊔ b) ⊓ c := le_sup_right
    gcongr
    exact le_sup_right
  focus
    show (a ⊔ b) ⊓ c ≤ a ⊔ (b ⊓ c)
    rw [my_inf_comm]
    rw [h]
    rw [my_inf_comm c b]
    gcongr
    exact inf_le_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  all_goals simp_all

  focus
    show a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ c
    rw [my_sup_comm (a ⊓ b) c]
    rw [h]
    rw [my_sup_comm b _]
    gcongr
    exact le_sup_right

  focus
    calc a ⊓ (a ⊓ b ⊔ c)
      _ ≤ (a ⊓ b) ⊔ c := inf_le_right
    gcongr
    exact inf_le_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  simpa

example (h: 0 ≤ b - a) : a ≤ b := by
  simpa using h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  gcongr

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have := calc
    0 = dist x x := by rw [dist_self x]
    _ ≤ dist x y + dist y x := dist_triangle x y x
    _ = dist x y + dist x y := by rw [dist_comm x y]
    _ = 2 * dist x y := by ring
  simpa using this

end
