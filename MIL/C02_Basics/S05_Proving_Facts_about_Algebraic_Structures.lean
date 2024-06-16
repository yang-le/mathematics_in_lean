import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
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

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · have h₁ : x ⊓ y ⊓ z ≤ x ⊓ y := by
      apply inf_le_left
    have h₂ : x ⊓ y ⊓ z ≤ z := by
      apply inf_le_right
    have h₃ : x ⊓ y ⊓ z ≤ x := by
      apply le_trans h₁ inf_le_left
    have h₄ : x ⊓ y ⊓ z ≤ y := by
      apply le_trans h₁ inf_le_right
    apply le_inf h₃ (le_inf h₄ h₂)
  · have h₁ : x ⊓ (y ⊓ z) ≤ x := by
      apply inf_le_left
    have h₂ : x ⊓ (y ⊓ z) ≤ y ⊓ z := by
      apply inf_le_right
    have h₃ : x ⊓ (y ⊓ z) ≤ y := by
      apply le_trans h₂ inf_le_left
    have h₄ : x ⊓ (y ⊓ z) ≤ z := by
      apply le_trans h₂ inf_le_right
    apply le_inf (le_inf h₁ h₃) h₄

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · have h₁ : x ≤ x ⊔ (y ⊔ z) := by
      apply le_sup_left
    have h₂ : y ⊔ z ≤ x ⊔ (y ⊔ z) := by
      apply le_sup_right
    have h₃ : y ≤ x ⊔ (y ⊔ z) := by
      apply le_trans le_sup_left h₂
    have h₄ : z ≤ x ⊔ (y ⊔ z) := by
      apply le_trans le_sup_right h₂
    apply sup_le (sup_le h₁ h₃) h₄
  · have h₁ : x ⊔ y ≤ x ⊔ y ⊔ z := by
      apply le_sup_left
    have h₂ : z ≤ x ⊔ y ⊔ z := by
      apply le_sup_right
    have h₃ : x ≤ x ⊔ y ⊔ z := by
      apply le_trans le_sup_left h₁
    have h₄ : y ≤ x ⊔ y ⊔ z := by
      apply le_trans le_sup_right h₁
    apply sup_le h₃ (sup_le h₄ h₂)

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm _ a, absorb1, inf_comm (a ⊔ b), h]
  rw [← sup_assoc a, inf_comm c, absorb2, inf_comm c]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, sup_comm _ a, absorb2, sup_comm (a ⊓ b), h]
  rw [← inf_assoc, sup_comm c, absorb1, sup_comm c]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have h₁ : -a + a ≤ -a + b := by
    apply add_le_add_left h
  rw [neg_add_self, neg_add_eq_sub] at h₁
  exact h₁

example (h: 0 ≤ b - a) : a ≤ b := by
  have h₁ : a + 0 ≤ a + (b - a) := by
    apply add_le_add_left h
  rw [add_zero, ← neg_add_eq_sub, ← add_assoc, add_neg_self, zero_add] at h₁
  exact h₁

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply sub_nonneg.mpr at h
  apply mul_nonneg at h
  apply h at h'
  rw [mul_sub_right_distrib] at h'
  exact sub_nonneg.mp h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
