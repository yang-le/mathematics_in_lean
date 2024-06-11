import MathLib.Data.Nat.Prime
import MathLib.Tactic.Linarith.Frontend
import Mathlib.Tactic.ByContra

theorem inifinitude_of_prime : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  intro N

  let M := N.factorial + 1
  let p := M.minFac

  have pp : Nat.Prime p := by
    refine Nat.minFac_prime ?n1
    have : N.factorial > 0 := by exact Nat.factorial_pos N
    linarith

  use p
  constructor
  by_contra! h
  have h₁ : p ∣ N.factorial + 1 := by exact Nat.minFac_dvd M
  have h₂ : p ∣ N.factorial := by
    refine Nat.dvd_factorial ?_ ?_
    exact Nat.minFac_pos M
    exact Nat.le_of_succ_le ht
  have h : p ∣ 1 := by exact (Nat.dvd_add_iff_right h₂).mpr h₁
  exact Nat.Prime.not_dvd_one pp h
  exact pp
