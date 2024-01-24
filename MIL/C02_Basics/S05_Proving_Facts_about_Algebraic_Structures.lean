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
theorem my_inf_comm : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  all_goals
    simp

@[simp]
lemma inf_triple_left : x ⊓ y ⊓ z ≤ x := by
  calc x ⊓ y ⊓ z
    _ ≤ x ⊓ y := @inf_le_left _ _ (x ⊓ y) z
    _ ≤ x := by apply inf_le_left

@[simp]
lemma inf_triple_mid : x ⊓ y ⊓ z ≤ y := by
  calc x ⊓ y ⊓ z
    _ ≤ x ⊓ y := @inf_le_left _ _ (x ⊓ y) z
    _ ≤ y := by apply inf_le_right

lemma my_inf_assoc : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · simp
  · rw [my_inf_comm]
    simp

theorem my_sup_comm : x ⊔ y = y ⊔ x := @my_inf_comm αᵒᵈ _ _ _

theorem my_sup_assoc : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := @my_inf_assoc αᵒᵈ _ _ _ _

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  all_goals
    simp

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  all_goals
    simp

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
