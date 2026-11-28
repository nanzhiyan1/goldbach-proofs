import Mathlib

theorem Conjectures.Cuts.Refute51c05dd90eec360519ea8b7f : ¬ (have x1 : ℕ → ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x2 ∧ Nat.Prime (x1 - x2)}.card; ∀ x2 ≤ (10 : ℕ) ^ (12 : ℕ), Even x2 → ∃ (x5 : ℕ), (2 : ℕ) ≤ x5 ∧ ((2 : ℕ) ^ x5) ^ (2 : ℕ) ≤ x2 ∧ (0 : ℕ) < x1 (x2 - (2 : ℕ) ^ x5) ∧ (0 : ℕ) < x1 (x2 + (2 : ℕ) - (2 : ℕ) ^ x5)) := by
  intro h
  obtain ⟨k, hk, hpow, _⟩ := h 0 (by norm_num) (by decide)
  have h4 : (4 : ℕ) ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have h16 : 16 ≤ (2 ^ k) ^ 2 := by
    rw [pow_two]
    calc
      16 = 4 * 4 := by norm_num
      _ ≤ (2 ^ k) * (2 ^ k) := Nat.mul_le_mul h4 h4
  omega
