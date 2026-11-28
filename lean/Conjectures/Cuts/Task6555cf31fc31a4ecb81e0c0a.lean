import Mathlib

namespace Conjectures.Cuts.Task6555cf31fc31a4ecb81e0c0a_aux

/-- `2 ^ (k + 1) ≤ k ^ 8` on the range of `k` used below (checked in the kernel). -/
theorem two_pow_le_pow_eight (k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ 39) :
    2 ^ (k + 1) ≤ k ^ 8 := by
  have h : ∀ j ∈ Finset.Icc 2 39, 2 ^ (j + 1) ≤ j ^ 8 := by decide
  exact h k (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- For `n ≤ 10 ^ 12` the dyadic logarithm is large enough: `n ≤ (log₂ (n+2)) ^ 8`. -/
theorem le_log_pow_eight (n : ℕ) (hn : n ≤ 10 ^ 12) : n ≤ Nat.log 2 (n + 2) ^ 8 := by
  have hn2 : n + 2 ≠ 0 := by omega
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (n + 2)
  have hpow : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 := Nat.pow_log_le_self 2 hn2
  have hm1 : 1 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by norm_num : 2 ^ 1 ≤ n + 2)
  have hm39 : Nat.log 2 (n + 2) ≤ 39 := by
    by_contra h
    have h40le : 40 ≤ Nat.log 2 (n + 2) := by omega
    have h4 : 2 ^ 40 ≤ 2 ^ Nat.log 2 (n + 2) := Nat.pow_le_pow_right (by norm_num) h40le
    have h40 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
    have h12 : (10 : ℕ) ^ 12 = 1000000000000 := by norm_num
    omega
  rcases Nat.lt_or_ge (Nat.log 2 (n + 2)) 2 with hsmall | hbig
  · have hlog1 : Nat.log 2 (n + 2) = 1 := by omega
    have hn1 : n ≤ 1 := by
      have : n + 2 < 4 := by simpa [hlog1] using hlt
      omega
    simpa [hlog1] using hn1
  · have h8 := two_pow_le_pow_eight (Nat.log 2 (n + 2)) hbig hm39
    omega

/-- The Dirichlet approximation theorem puts every point of `[0, 1]` into the level-`(log₂)⁴`
Farey arcs of radius `(log₂)⁴ / (q n)` once `n ≤ (log₂ (n+2)) ^ 8`. -/
theorem exists_arc {n : ℕ} (hn : 1 ≤ n) (hlog : n ≤ Nat.log 2 (n + 2) ^ 8) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ q r : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (n + 2) ^ 2) ^ 2 ∧ r ≤ q ∧ r.Coprime q ∧
      |y - (r : ℝ) / (q : ℝ)| ≤
        ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 2 / ((q : ℝ) * (n : ℝ)) := by
  set m := Nat.log 2 (n + 2)
  set N := (m ^ 2) ^ 2
  have hm1 : 1 ≤ m := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 1 ≤ n + 2)
  have hN1 : 1 ≤ N := by
    have : 1 ≤ m ^ 2 := Nat.pow_le_pow_left hm1 2
    exact Nat.pow_le_pow_left this 2
  have hN : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le y hN
  have hd : 0 < q.den := q.pos
  have hdR : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hd
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hmul : |y * (q.den : ℝ) - (q.num : ℝ)| ≤ 1 / 2 := by
    have hstep : y * (q.den : ℝ) - (q.num : ℝ) = (y - (q : ℝ)) * (q.den : ℝ) := by
      rw [Rat.cast_def, sub_mul, div_mul_cancel₀ _ hdR.ne']
    rw [hstep, abs_mul, abs_of_pos hdR]
    have hq' : |y - (q : ℝ)| ≤ 1 / ((N : ℝ) + 1) / (q.den : ℝ) := by
      rw [div_div]
      exact hq
    calc |y - (q : ℝ)| * (q.den : ℝ)
        ≤ (1 / ((N : ℝ) + 1) / (q.den : ℝ)) * (q.den : ℝ) :=
          mul_le_mul_of_nonneg_right hq' hdR.le
      _ = 1 / ((N : ℝ) + 1) := by rw [div_mul_cancel₀ _ hdR.ne']
      _ ≤ 1 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hnum0 : 0 ≤ q.num := by
    have hb : y * (q.den : ℝ) - (q.num : ℝ) ≤ 1 / 2 := (abs_le.mp hmul).2
    have hy0d : 0 ≤ y * (q.den : ℝ) := mul_nonneg hy0 hdR.le
    have h2 : (-1 : ℤ) < q.num := by
      have h1 : ((-1 : ℤ) : ℝ) < (q.num : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp h1
    omega
  have hnumd : q.num ≤ (q.den : ℤ) := by
    have hb : -(1 / 2) ≤ y * (q.den : ℝ) - (q.num : ℝ) := (abs_le.mp hmul).1
    have hy1d : y * (q.den : ℝ) ≤ (q.den : ℝ) := by
      calc y * (q.den : ℝ) ≤ 1 * (q.den : ℝ) := mul_le_mul_of_nonneg_right hy1 hdR.le
        _ = (q.den : ℝ) := one_mul _
    have h2 : q.num < (q.den : ℤ) + 1 := by
      have h1 : (q.num : ℝ) < (((q.den : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp h1
    omega
  refine ⟨q.den, q.num.toNat, hd, hden, ?_, ?_, ?_⟩
  · have : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum0
    omega
  · have hcop : q.num.natAbs.Coprime q.den := q.reduced
    have hna : q.num.natAbs = q.num.toNat := by
      have h1 := Int.natAbs_of_nonneg hnum0
      have h2 := Int.toNat_of_nonneg hnum0
      omega
    rwa [hna] at hcop
  · have hqcast : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      have h : (q.num : ℝ) = (q.num.toNat : ℝ) := by
        have h2 : (q.num : ℤ) = (q.num.toNat : ℤ) := (Int.toNat_of_nonneg hnum0).symm
        have h3 : (q.num : ℝ) = ((q.num.toNat : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) h2
        rwa [Int.cast_natCast] at h3
      rw [Rat.cast_def, h]
    rw [hqcast] at hq
    refine hq.trans ?_
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hNN : (n : ℝ) ≤ (N : ℝ) * ((N : ℝ) + 1) := by
      have h1 : n ≤ N * N := by
        calc n ≤ m ^ 8 := hlog
          _ = (m ^ 2) ^ 2 * (m ^ 2) ^ 2 := by ring
          _ = N * N := rfl
      have h2 : (n : ℝ) ≤ (N : ℝ) * (N : ℝ) := by exact_mod_cast h1
      nlinarith
    rw [div_le_div_iff₀ (mul_pos (by linarith) hdR) (mul_pos hdR hnR)]
    have hnum : ((m ^ 2 : ℕ) : ℝ) ^ 2 = (N : ℝ) :=
      (Nat.cast_pow (m ^ 2) 2).symm.trans rfl
    rw [hnum]
    calc 1 * ((q.den : ℝ) * (n : ℝ)) = (q.den : ℝ) * (n : ℝ) := by ring
      _ ≤ (q.den : ℝ) * ((N : ℝ) * ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hNN hdR.le
      _ = (N : ℝ) * (((N : ℝ) + 1) * (q.den : ℝ)) := by ring
end Conjectures.Cuts.Task6555cf31fc31a4ecb81e0c0a_aux

open Conjectures.Cuts.Task6555cf31fc31a4ecb81e0c0a_aux

theorem Conjectures.Cuts.Task6555cf31fc31a4ecb81e0c0a :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℕ → ℝ := fun (x6 x7 : ℕ) => if x7 ^ (3 : ℕ) ≤ x6 then x1 x7 else (0 : ℝ); have x7 : ℕ → ℕ → ℝ := fun (x7 x8 : ℕ) => x1 x8 - x6 x7 x8; have x8 : ℕ → ℕ := fun (x8 : ℕ) => Max.max (1 : ℕ) (Nat.log (2 : ℕ) x8 / (2 : ℕ)); have x9 : ℕ → ℝ → ℝ := fun (x9 : ℕ) (x10 : ℝ) => (∑ x11 ∈ Finset.range (x8 x9), Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x11 + (1 : ℕ)) * x10)) / ↑(x8 x9); have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | x11 ∉ x5 x10 ∧ (1 / 2 : ℝ) < x9 x10 x11}; have x11 : ℕ → (ℕ → Prop) → Set ℝ := fun (x11 : ℕ) (x12 : ℕ → Prop) => {x13 : ℝ | ∃ (x14 : ℕ) (x15 : ℕ), (1 : ℕ) ≤ x14 ∧ x14 ≤ x4 x11 ^ (2 : ℕ) ∧ x15 ≤ x14 ∧ x15.Coprime x14 ∧ x12 x14 ∧ |x13 - ↑x15 / ↑x14| ≤ ↑(x4 x11) ^ (2 : ℕ) / (↑x14 * ↑x11)}; have x12 : ℕ → ℝ → ℝ := fun (x12 : ℕ) (x13 : ℝ) => ‖x3 x12 (x7 x12) x13‖ ^ (2 : ℕ); have x13 : ℕ → ℝ := fun (x13 : ℕ) => ↑x13 * ((1 : ℝ) + Real.log ↑x13) ^ (4 : ℕ); have x14 : Set ℝ → (ℝ → ℝ) → ℝ := fun (x14 : Set ℝ) (x15 : ℝ → ℝ) => intervalIntegral (x14.indicator x15) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; ∀ x15 ≤ (10 : ℕ) ^ (12 : ℕ), Even x15 → x14 ((x10 x15 \ x11 x15 fun (x18 : ℕ) => True) ∩ {x18 : ℝ | x13 x15 < x12 x15 x18}) (x12 x15) ≤ ↑x15 / (2304 : ℝ) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 hx15 heven
  rcases Nat.eq_zero_or_pos x15 with rfl | hnpos
  · have h12 : ∀ y : ℝ, x12 0 y = 0 := by
      intro y
      have h0 : x7 0 0 = 0 := by
        show x1 0 - (if (0 : ℕ) ^ 3 ≤ 0 then x1 0 else (0 : ℝ)) = 0
        norm_num
      have h3 : x3 0 (x7 0) y = 0 := by
        show ∑ k ∈ Finset.range (0 + 1), ((x7 0 k : ℝ) : ℂ) * x2 ((k : ℝ) * y) = 0
        rw [Finset.sum_range_one, h0]
        simp
      show ‖x3 0 (x7 0) y‖ ^ 2 = 0
      rw [h3]
      simp
    have hInt : x14 ((x10 0 \ x11 0 fun _ => True) ∩ {y : ℝ | x13 0 < x12 0 y})
        (x12 0) = 0 := by
      show intervalIntegral
          (((x10 0 \ x11 0 fun _ => True) ∩ {y : ℝ | x13 0 < x12 0 y}).indicator
            (x12 0)) 0 1 MeasureTheory.MeasureSpace.volume = 0
      have hcongr : Set.EqOn
          (((x10 0 \ x11 0 fun _ => True) ∩ {y : ℝ | x13 0 < x12 0 y}).indicator (x12 0))
          (fun _ => (0 : ℝ)) (Set.uIcc 0 1) := by
        intro y _
        by_cases hmem : y ∈ (x10 0 \ x11 0 fun _ => True) ∩ {y : ℝ | x13 0 < x12 0 y}
        · rw [Set.indicator_of_mem hmem, h12]
        · exact Set.indicator_of_notMem hmem _
      exact (intervalIntegral.integral_congr hcongr).trans intervalIntegral.integral_zero
    rw [hInt]
    positivity
  · have hlog : x15 ≤ Nat.log 2 (x15 + 2) ^ 8 := le_log_pow_eight x15 hx15
    have hx11 : ∀ y ∈ Set.uIcc (0 : ℝ) 1, y ∈ x11 x15 (fun _ => True) := by
      intro y hy
      have hyI : y ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hy
        exact hy
      obtain ⟨q, r, hq1, hq2, hrq, hcop, hbound⟩ :=
        exists_arc hnpos hlog (Set.mem_Icc.mp hyI).1 (Set.mem_Icc.mp hyI).2
      show ∃ (q : ℕ) (r : ℕ), 1 ≤ q ∧ q ≤ x4 x15 ^ 2 ∧ r ≤ q ∧ r.Coprime q ∧
        (fun _ => True) q ∧
        |y - (r : ℝ) / (q : ℝ)| ≤ ((x4 x15 : ℕ) : ℝ) ^ 2 / ((q : ℝ) * (x15 : ℝ))
      exact ⟨q, r, hq1, hq2, hrq, hcop, trivial, hbound⟩
    have hInt : x14 ((x10 x15 \ x11 x15 fun _ => True) ∩
        {y : ℝ | x13 x15 < x12 x15 y}) (x12 x15) = 0 := by
      show intervalIntegral
          (((x10 x15 \ x11 x15 fun _ => True) ∩
            {y : ℝ | x13 x15 < x12 x15 y}).indicator (x12 x15)) 0 1
            MeasureTheory.MeasureSpace.volume = 0
      have hcongr : Set.EqOn
          (((x10 x15 \ x11 x15 fun _ => True) ∩
            {y : ℝ | x13 x15 < x12 x15 y}).indicator (x12 x15))
          (fun _ => (0 : ℝ)) (Set.uIcc 0 1) := by
        intro y hy
        refine Set.indicator_of_notMem ?_ _
        intro hmem
        exact hmem.1.2 (hx11 y hy)
      exact (intervalIntegral.integral_congr hcongr).trans intervalIntegral.integral_zero
    rw [hInt]
    positivity
