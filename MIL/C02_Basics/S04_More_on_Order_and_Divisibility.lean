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

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    have h : min (min a b) c ≤ (min a b) := by
      apply min_le_left
    apply le_min
    · show min (min a b) c ≤ a
      apply le_trans h
      apply min_le_left
    · show min (min a b) c ≤ min b c
      apply le_min
      apply le_trans h
      apply min_le_right
      apply min_le_right
  · show min a (min b c) ≤ min (min a b) c
    have h : min a (min b c) ≤ (min b c) := by
      apply min_le_right
    apply le_min
    · show min a (min b c) ≤ min a b
      apply le_min
      apply min_le_left
      apply le_trans h
      apply min_le_left
    · show min a (min b c) ≤ c
      apply le_trans h
      apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have h₁ : min a b + c ≤ a + c := by
    apply add_le_add_right
    apply min_le_left
  have h₂ : min a b + c ≤ b + c := by
    apply add_le_add_right
    apply min_le_right
  apply le_min h₁ h₂

example : min a b + c = min (a + c) (b + c) := by
  have h : min (a + c) (b + c) ≤ min a b + c := by
    have h₁ : min (a + c) (b + c) + -c ≤ min (a + c + -c) (b + c + -c) := by
      apply aux
    repeat rw [add_neg_cancel_right] at h₁
    linarith
  apply le_antisymm (aux a b c) h

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h : |a - b + b| ≤ |a - b| + |b| := by
    apply abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith
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
  apply dvd_add
  apply dvd_add
  · apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm

  apply dvd_gcd
  apply gcd_dvd_right
  apply gcd_dvd_left

  apply dvd_gcd
  apply gcd_dvd_right
  apply gcd_dvd_left
end
