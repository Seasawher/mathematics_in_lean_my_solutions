import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · aesop
  · aesop

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  simp at hx
  rcases hx with ⟨y, ys, e⟩
  have : y = x := h e
  rwa [← this]

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y hy
  aesop

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y hy
  simp
  have ⟨x, this⟩ := h y
  use x
  aesop

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y hy
  aesop

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x
  aesop

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  aesop

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y
  aesop

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y hy
  simp at hy
  rcases hy with ⟨⟨x, xs, e₁⟩, ⟨x', xt, e₂⟩⟩
  have : f x = f x' := by rw [e₁, e₂]
  replace : x = x' := h this
  aesop

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y hy
  aesop

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x hy
  aesop

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  aesop

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y hy
  aesop

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x hx
  aesop

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x hx
  aesop

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  all_goals
    intro z
    aesop

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  aesop

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y hy
  simp at hy
  obtain ⟨x, _, hfx⟩ := hy i
  use x

  constructor

  case h.right =>
    assumption

  case h.left =>
    simp
    intro j
    have ⟨xj, hxj, hfj⟩ := hy j
    rw [← hfj] at hfx
    have := injf hfx
    rwa [this]

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  aesop

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  dsimp [InjOn]
  intro x xpos y zpos hxy
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xpos]
    _ = sqrt y ^ 2 := by rw [hxy]
    _ = y := by rw [sq_sqrt zpos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  dsimp [InjOn]
  intro x xpos y ypos hxy
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xpos]
    _ = sqrt (y ^ 2) := by rw [hxy]
    _ = y := by rw [sqrt_sq ypos]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext z
  constructor
  case mp =>
    rintro ⟨x, hx, rfl⟩
    simp at *
    exact sqrt_nonneg x

  case mpr =>
    intro hz
    simp at *
    use z ^ 2
    constructor
    · positivity
    · rw [sqrt_sq hz]

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext z
  constructor
  case mp =>
    rintro ⟨x, rfl⟩
    simp
    exact sq_nonneg x
  case mpr =>
    intro hz
    use sqrt z
    simp at *
    rw [sq_sqrt hz]

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  case mp =>
    intro finj
    dsimp [LeftInverse]
    intro x
    apply finj
    rw [inverse_spec (f x) (Exists.intro x rfl)]

  case mpr =>
    intro comp
    dsimp [LeftInverse] at comp
    intro x x' h
    calc
      x = inverse f (f x) := by rw [comp x]
      _ = inverse f (f x') := by rw [h]
      _ = x' := by rw [comp x']

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor <;> intro h

  case mp =>
    dsimp [Function.RightInverse]
    intro y
    apply inverse_spec
    apply h y

  case mpr =>
    intro y
    dsimp [Function.RightInverse, LeftInverse] at h
    aesop

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    dsimp [S]
    assumption
  have h₃ : j ∉ S := by
    dsimp [S]
    rw [h]
    simpa
  contradiction

-- COMMENTS: TODO: improve this
end
