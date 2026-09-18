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
  · intro h x xs
    have := mem_image_of_mem f xs
    exact h this
  · intro h x ⟨y, ys, fyx⟩
    rw [← fyx]
    exact h ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro _ ⟨_, _, feq⟩
  rwa [← h feq]

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro _ ⟨y, fyu, fyx⟩
  rw [← fyx]
  exact fyu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro x xu
  rcases h x with ⟨y, fy⟩
  use y
  rw [← fy] at xu
  exact ⟨xu, fy⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro _ ⟨y, ys, fyx⟩
  exact ⟨y, h ys, fyx⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro _ xfu
  exact h xfu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro _ ⟨_, ⟨ys, yt⟩, fyx⟩
  rw [← fyx]
  exact ⟨mem_image_of_mem f ys, mem_image_of_mem f yt⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨⟨_, ys, fyx⟩, _, zt, fzx⟩
  rw [← fyx] at fzx
  rcases mem_image_of_mem f ys with ⟨_, as, ha⟩
  rcases mem_image_of_mem f zt with ⟨b, bt, hb⟩
  rw [fzx] at hb
  rw [← hb] at ha
  exact ⟨b, ⟨by rwa [h ha] at as, bt⟩, by rwa [hb]⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro _ ⟨⟨y, ys, fyx⟩, h⟩
  use y
  have : y ∉ t := by
    by_contra h'
    have := mem_image_of_mem f h'
    rw [fyx] at this
    contradiction
  exact ⟨⟨ys, this⟩, fyx⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rfl

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  · rintro ⟨⟨y, ys, fyx⟩, xv⟩
    exact ⟨y, ⟨ys, by rwa [← fyx] at xv⟩, fyx⟩
  · rintro ⟨_a, ⟨ys, fyv⟩, rfl⟩
    exact ⟨mem_image_of_mem f ys, fyv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro _ ⟨y, ⟨ys, _⟩, fyx⟩
  exact ⟨⟨y, ys, fyx⟩, by rwa [← fyx]⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro _ ⟨xs, fxu⟩
  exact ⟨mem_image_of_mem f xs, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    exact ⟨x, xs, rfl⟩
  · right
    exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  · rintro ⟨y, ⟨i, yAi⟩, fyx⟩
    exact ⟨i, y, yAi, fyx⟩
  · rintro ⟨i, y, yAi, fyx⟩
    exact ⟨y, ⟨i, yAi⟩, fyx⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro x ⟨y, yAi, fyx⟩
  simp at yAi
  simp
  intro i
  use y
  exact ⟨yAi i, fyx⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro x; simp
  intro h
  rcases h i with ⟨y, _, fyx⟩
  use y
  constructor
  · intro j
    rcases h j with ⟨y', _, fy'x⟩
    rw [← fy'x] at fyx
    rwa [injf fyx]
  · exact fyx

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
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
  intro x xnonneg y ynonneg e
  calc
    x = √(x * x) := by rw [sqrt_mul_self xnonneg]
    _ = √x * √x := by rw [sqrt_mul xnonneg]
    _ = √y * √y := by rw [e]
    _ = √(y * y) := by rw [sqrt_mul ynonneg]
    _ = y := by rw [sqrt_mul_self ynonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg e
  dsimp at e
  calc
    x = √(x * x) := by rw [sqrt_mul_self xnonneg]
    _ = √(x ^ 2) := by rw [pow_two]
    _ = √(y ^ 2) := by rw [e]
    _ = √(y * y) := by rw [pow_two]
    _ = y := by rw [sqrt_mul_self ynonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x; constructor
  · rintro ⟨_, _, rfl⟩
    apply sqrt_nonneg
  · intro xpos
    use x * x
    exact ⟨mul_self_nonneg x, sqrt_mul_self xpos⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x; constructor
  · rintro ⟨y, rfl⟩
    exact sq_nonneg y
  · intro xnonneg
    use √x
    exact sq_sqrt xnonneg

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
  · intro injf x
    apply injf
    apply inverse_spec
    use x
  · rintro h x y e
    rw [← h x, ← h y, e]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro sujf _
    apply inverse_spec
    apply sujf
  · intro h x
    have := h x
    use inverse f x

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
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

-- COMMENTS: TODO: improve this
end
