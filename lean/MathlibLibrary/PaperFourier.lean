import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace PaperFourier

noncomputable def ramp (y t : ℝ) : ℝ := max (y / t - 1) 0

def endpoint (X : ℕ) (H : ℝ → ℝ) : ℝ :=
  (X : ℝ) * H ((X : ℝ) + 1) - ((X : ℝ) + 1) * H (X : ℝ)

theorem ramp_endpoint (X n : ℕ) (hn : 0 < n) :
    endpoint X (fun y => ramp y (n : ℝ)) = if n ≤ X then 1 else 0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold endpoint ramp
  split_ifs with h
  · have hR : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast h
    have hleft : 0 ≤ ((X : ℝ) + 1) / (n : ℝ) - 1 :=
      sub_nonneg.mpr ((one_le_div hnR).2 (by linarith))
    have hright : 0 ≤ (X : ℝ) / (n : ℝ) - 1 :=
      sub_nonneg.mpr ((one_le_div hnR).2 hR)
    simp only [max_eq_left hleft, max_eq_left hright]
    ring
  · have hR : (X : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))
    have hleft : ((X : ℝ) + 1) / (n : ℝ) - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_one hnR).2 hR)
    have hright : (X : ℝ) / (n : ℝ) - 1 ≤ 0 :=
      sub_nonpos.mpr ((div_le_one hnR).2 (by linarith))
    simp only [max_eq_right hleft, max_eq_right hright]
    ring

theorem weighted_ramp_endpoint
    (X : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) (hs : ∀ n ∈ s, 0 < n) :
    endpoint X (fun y => ∑ n ∈ s, a n * ramp y (n : ℝ)) =
      ∑ n ∈ s.filter (fun n => n ≤ X), a n := by
  unfold endpoint
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have h := ramp_endpoint X n (hs n hn)
  unfold endpoint at h
  calc
    _ = a n * ((X : ℝ) * ramp ((X : ℝ) + 1) (n : ℝ) -
        ((X : ℝ) + 1) * ramp (X : ℝ) (n : ℝ)) := by ring
    _ = _ := by rw [h]; split_ifs <;> ring

theorem centered_endpoint (X : ℕ) (hX : 0 < X)
    (G : ℝ → ℝ) (a₀ c : ℝ) :
    endpoint X (fun y => G y + a₀ * (y * Real.log y) + c * y) =
      endpoint X G + a₀ * (X : ℝ) * ((X : ℝ) + 1) *
        Real.log (1 + 1 / (X : ℝ)) := by
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hXn : (X : ℝ) ≠ 0 := ne_of_gt hXp
  have hXs : (X : ℝ) + 1 ≠ 0 := by positivity
  have he : 1 + 1 / (X : ℝ) = ((X : ℝ) + 1) / (X : ℝ) := by
    field_simp
  rw [he, Real.log_div hXs hXn]
  unfold endpoint
  ring

theorem centered_ramp_endpoint (X : ℕ) (hX : 0 < X)
    (s : Finset ℕ) (a : ℕ → ℝ) (hs : ∀ n ∈ s, 0 < n)
    (G : ℝ → ℝ) (a₀ c : ℝ)
    (hG : ∀ y, (∑ n ∈ s, a n * ramp y (n : ℝ)) =
      G y + a₀ * (y * Real.log y) + c * y) :
    (∑ n ∈ s.filter (fun n => n ≤ X), a n) =
      endpoint X G + a₀ * (X : ℝ) * ((X : ℝ) + 1) *
        Real.log (1 + 1 / (X : ℝ)) := by
  rw [← weighted_ramp_endpoint X s a hs, funext hG, centered_endpoint X hX]
end PaperFourier
