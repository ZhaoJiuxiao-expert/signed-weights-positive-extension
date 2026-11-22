import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

open scoped BigOperators

namespace RademacherBound
set_option maxHeartbeats 1000000

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem mass_bound_of_signs
    (A : ι → κ → ℝ) (w : ι → ℝ) (a : κ → ℝ) (t : ℝ)
    (hw : ∀ i, w i = -1 ∨ w i = 1)
    (ha : ∀ j, 0 ≤ a j)
    (h_interp : ∀ i, w i = ∑ j, a j * A i j)
    (h_corr : ∀ j, (∑ i, w i * A i j) ≤ t) :
    (Fintype.card ι : ℝ) ≤ t * ∑ j, a j := by
  calc
    (Fintype.card ι : ℝ) = ∑ i, w i * w i := by
      symm
      calc
        _ = ∑ _i : ι, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => by
          rcases hw i with h | h <;> rw [h] <;> norm_num)
        _ = _ := by simp
    _ = ∑ i, w i * (∑ j, a j * A i j) :=
      Finset.sum_congr rfl (fun i _ => congrArg (w i * ·) (h_interp i))
    _ = ∑ j, a j * (∑ i, w i * A i j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun i _ => by ring))
    _ ≤ ∑ j, a j * t := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (h_corr j) (ha j))
    _ = t * ∑ j, a j := by rw [← Finset.sum_mul, mul_comm (∑ j, a j)]

noncomputable def sign (b : Bool) : ℝ := if b then 1 else -1

private theorem exp_sign_bound (u x : ℝ) (hx : |x| ≤ 1) :
    (∑ b : Bool, Real.exp (u * (sign b * x))) ≤ 2 * Real.exp (u ^ 2 / 2) := by
  have hs : x ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (show |x| ≤ |(1 : ℝ)| by simpa using hx))
  have hu : (u * x) ^ 2 ≤ u ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg u) hs
  have hc := (Real.cosh_le_exp_half_sq (u * x)).trans
    (Real.exp_le_exp.mpr (by linarith : (u * x)^2 / 2 ≤ u^2 / 2))
  rw [Real.cosh_eq] at hc
  rw [Fintype.univ_bool]
  norm_num [sign]
  linarith

private theorem exp_sum_signs_bound [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ 1) (u : ℝ) :
    (∑ w : ι → Bool, Real.exp (u * (∑ i, sign (w i) * x i))) ≤
      (Fintype.card (ι → Bool) : ℝ) * Real.exp (u ^ 2 * Fintype.card ι / 2) := by
  calc
    _ = ∏ i, ∑ b : Bool, Real.exp (u * (sign b * x i)) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ _i : ι, 2 * Real.exp (u ^ 2 / 2) :=
      Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))
        (fun i _ => exp_sign_bound u (x i) (hx i))
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, mul_pow, ← Real.exp_nat_mul]
      simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
      congr 2
      ring

theorem exists_signs_with_correlation_bound (A : ι → κ → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (hι : 0 < Fintype.card ι) (hκ : 0 < Fintype.card κ) :
    ∃ w : ι → ℝ, (∀ i, w i = -1 ∨ w i = 1) ∧
      ∀ j, (∑ i, w i * A i j) ≤ Real.sqrt (2 * Fintype.card ι * Real.log (2 * Fintype.card κ)) := by
  classical
  let m : ℝ := Fintype.card ι
  let h : ℝ := Fintype.card κ
  let L := Real.log (2 * h)
  let t := Real.sqrt (2 * m * L)
  let u := t / m
  have hm : 0 < m := Nat.cast_pos.mpr hι
  have hh : 1 ≤ h := by
    change (1 : ℝ) ≤ (Fintype.card κ : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card κ from hκ)
  have h2 : 1 < 2 * h := by linarith
  have hL : 0 < L := Real.log_pos h2
  have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hu : 0 < u := div_pos ht hm
  have hts : t ^ 2 = 2 * m * L := Real.sq_sqrt (by positivity)
  have he : u * t = u ^ 2 * m / 2 + L := by
    dsimp [u]
    field_simp [ne_of_gt hm]
    nlinarith [congrArg (fun v : ℝ => m * v) hts]
  have hexp : Real.exp (u * t) = 2 * h * Real.exp (u ^ 2 * m / 2) := by
    rw [he, Real.exp_add, Real.exp_log (by linarith : 0 < 2 * h)]
    ring
  suffices ∃ w : ι → Bool, ∀ j, (∑ i, sign (w i) * A i j) ≤ t by
    obtain ⟨w, hw⟩ := this
    exact ⟨fun i => sign (w i), fun i => by cases hwi : w i <;> simp [sign, hwi], hw⟩
  by_contra hbad
  push_neg at hbad
  have hlower (w : ι → Bool) :
      Real.exp (u * t) ≤ ∑ j, Real.exp (u * (∑ i, sign (w i) * A i j)) := by
    obtain ⟨j, hj⟩ := hbad w
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hj) (le_of_lt hu))).trans
      (Finset.single_le_sum (f := fun k => Real.exp (u * (∑ i, sign (w i) * A i k)))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ j))
  let N : ℝ := Fintype.card (ι → Bool)
  let E := Real.exp (u ^ 2 * m / 2)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNE : 0 < N * E := mul_pos hN (Real.exp_pos _)
  have hsum : N * (2 * h * E) ≤ h * (N * E) :=
    calc
      _ = ∑ _w : ι → Bool, Real.exp (u * t) := by simp [N, E, hexp]
      _ ≤ ∑ w : ι → Bool, ∑ j, Real.exp (u * (∑ i, sign (w i) * A i j)) :=
        Finset.sum_le_sum (fun w _ => hlower w)
      _ ≤ ∑ _j : κ, N * E := by
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum (fun j _ => exp_sum_signs_bound (fun i => A i j) (fun i => hA i j) u)
      _ = _ := by simp [h]
  nlinarith [mul_pos (by linarith : 0 < h) hNE]

theorem exists_signs_mass_lower_bound (A : ι → κ → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) (hι : 0 < Fintype.card ι) (hκ : 0 < Fintype.card κ) :
    ∃ w : ι → ℝ, (∀ i, w i = -1 ∨ w i = 1) ∧
      ∀ a : κ → ℝ, (∀ j, 0 ≤ a j) → (∀ i, w i = ∑ j, a j * A i j) →
        Real.sqrt ((Fintype.card ι : ℝ) / (2 * Real.log (2 * Fintype.card κ))) ≤ ∑ j, a j := by
  obtain ⟨w, hw, hc⟩ := exists_signs_with_correlation_bound A hA hι hκ
  refine ⟨w, hw, ?_⟩
  intro a ha hi
  let m : ℝ := Fintype.card ι
  let h : ℝ := Fintype.card κ
  let B := 2 * Real.log (2 * h)
  have hm : 0 < m := Nat.cast_pos.mpr hι
  have hh : 1 ≤ h := by
    change (1 : ℝ) ≤ (Fintype.card κ : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card κ from hκ)
  have hB : 0 < B := mul_pos (by norm_num) (Real.log_pos (by linarith))
  have hMB : 0 < m * B := mul_pos hm hB
  have hmass : m ≤ Real.sqrt (m * B) * ∑ j, a j := by
    apply mass_bound_of_signs A w a _ hw ha hi
    intro j
    exact (hc j).trans_eq (congrArg Real.sqrt (by dsimp [m, B, h]; ring))
  have hhyp : Real.sqrt (m / B) * Real.sqrt (m * B) = m := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ m / B)]
    have hcancel : m / B * (m * B) = m ^ 2 := by
      field_simp [ne_of_gt hB]
      ring
    rw [hcancel, Real.sqrt_sq (le_of_lt hm)]
  apply (mul_le_mul_right (Real.sqrt_pos.2 hMB)).mp
  rw [hhyp, mul_comm (∑ j, a j)]
  exact hmass
end RademacherBound
