import PositiveWindow
import GramCertificate

namespace Goldbach.MultiplicationCertificate

open Goldbach.GramCertificate

/-- Accumulate weights at the residue coordinates of the products by k. -/
def row (q : Nat) (S : List Nat) (c : Int) (w : Nat → Int) (k z : Nat) : Int :=
  sumOver (1 :: S) fun b => if z = (k * b) % q then PositiveWindow.amplitude c w b else 0

/-- Gram matrix of the residue-coordinate vectors, with the stated diagonal shift. -/
def matrix (q : Nat) (S : List Nat) (c : Int) (w : Nat → Int) (δ : Int)
    (i j : Nat) : Int :=
  addDiagonal (gram (List.range q) (row q S c w)) δ i j

private theorem sumOver_eq_sumBy (S : List Nat) (f : Nat → Int) :
    sumOver S f = PositiveWindow.sumBy f S := by
  induction S with
  | nil => rfl
  | cons a S ih => simp [sumOver, PositiveWindow.sumBy, ih]

private theorem sumOver_eq_of_nodup (rs : List Nat) (hr : rs.Nodup) (t : Nat) (a : Int) :
    sumOver rs (fun z => if z = t then a else 0) = if t ∈ rs then a else 0 := by
  induction rs with
  | nil => simp [sumOver]
  | cons z rs ih =>
      obtain ⟨hn, htail⟩ := List.nodup_cons.mp hr
      by_cases ht : z = t
      · subst z
        simp [sumOver, ih htail, hn]
      · simp [sumOver, ih htail, ht, Ne.symm ht]

/-- The concrete Gram dot product at (1,k) is exactly the congruence sum. -/
theorem first_row_eq_kernel (q : Nat) (hq : 0 < q) (S : List Nat)
    (c : Int) (w : Nat → Int) (δ : Int) (k : Nat) :
    matrix q S c w δ 1 k = PositiveWindow.kernel q S c w δ k := by
  let A := PositiveWindow.amplitude c w
  have hCollapse (a b : Nat) :
      sumOver (List.range q) (fun z =>
        (if z = a % q then A a else 0) *
        (if z = (k * b) % q then A b else 0)) =
        if a % q = (k * b) % q then A a * A b else 0 := by
    by_cases h : a % q = (k * b) % q
    · have hPoint (z : Nat) :
          (if z = a % q then A a else 0) *
          (if z = (k * b) % q then A b else 0) =
          if z = a % q then A a * A b else 0 := by
        by_cases hz : z = a % q
        · simp only [if_pos hz, if_pos (hz.trans h)]
        · simp [hz]
      simp only [hPoint]
      rw [sumOver_eq_of_nodup _ (List.nodup_range q)]
      have hm : a % q ∈ List.range q := List.mem_range.mpr (Nat.mod_lt a hq)
      rw [if_pos hm, if_pos h]
    · have hPoint (z : Nat) :
          (if z = a % q then A a else 0) *
          (if z = (k * b) % q then A b else 0) =
          if z = a % q then 0 else 0 := by
        by_cases hz : z = a % q
        · subst z
          simp [h]
        · simp [hz]
      simp only [hPoint]
      rw [sumOver_eq_of_nodup _ (List.nodup_range q)]
      simp [h]
  unfold matrix addDiagonal gram row PositiveWindow.kernel
  simp only [Nat.one_mul, ← sum_mul_right, ← sum_mul_left]
  simp only [sum_swap (List.range q) (1 :: S), hCollapse, A]
  rw [sum_swap (1 :: S) (1 :: S)]
  simp only [sumOver_eq_sumBy]
  by_cases hk : k = 1
  · subst k
    rfl
  · rw [if_neg (Ne.symm hk), if_neg hk]

/-- The specified window, identity mass, and nonnegative ordinary quadratic form
    for the same matrix; positive shift also yields positive definiteness. -/
theorem certificate {X q : Nat} {S : List Nat} (c : Int) (w : Nat → Int) (δ : Int)
    (hX : 2 ≤ X) (hq : X * X < q) (hS : S.Nodup)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b) (hδ : 0 ≤ δ) :
    (∀ k : Nat, 2 ≤ k → k ≤ X →
      matrix q S c w δ 1 k = if k ∈ S then c * w k else 0) ∧
    matrix q S c w δ 1 1 = c * c + PositiveWindow.sumBy (fun n => w n * w n) S + δ ∧
    (∀ (is : List Nat) (x : Nat → Int), is.Nodup →
      0 ≤ quadratic is (matrix q S c w δ) x) ∧
    (∀ (is : List Nat) (x : Nat → Int), is.Nodup → 0 < δ →
      ∀ j ∈ is, x j ≠ 0 → 0 < quadratic is (matrix q S c w δ) x) := by
  have hq0 : 0 < q := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk0 hk
    rw [first_row_eq_kernel q hq0]
    exact PositiveWindow.kernel_window c w δ hX hq hS hRange hRatio hk0 hk
  · rw [first_row_eq_kernel q hq0]
    exact PositiveWindow.kernel_one c w δ hX hq hS hRange
  · intro is x his
    unfold matrix
    rw [quadratic_addDiagonal is _ x δ his]
    exact regularized_nonneg is _ _ x δ hδ
  · intro is x his hδpos j hj hx
    exact gram_addDiagonal_pos is _ _ x δ his hδpos j hj hx

#print axioms first_row_eq_kernel
#print axioms certificate

end Goldbach.MultiplicationCertificate
