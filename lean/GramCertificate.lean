import Std

namespace Goldbach.GramCertificate

/-- Sum over an explicit finite enumeration. -/
def sumOver (xs : List α) (f : α → Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumOver rest f

theorem sum_add (xs : List α) (f g : α → Int) :
    sumOver xs (fun i => f i + g i) = sumOver xs f + sumOver xs g := by
  induction xs with
  | nil => simp [sumOver]
  | cons i rest ih =>
    simp only [sumOver, ih]
    omega

theorem sum_mul_left (xs : List α) (a : Int) (f : α → Int) :
    sumOver xs (fun i => a * f i) = a * sumOver xs f := by
  induction xs with
  | nil => simp [sumOver]
  | cons i rest ih => simp [sumOver, ih, Int.mul_add]

theorem sum_mul_right (xs : List α) (a : Int) (f : α → Int) :
    sumOver xs (fun i => f i * a) = sumOver xs f * a := by
  simpa only [Int.mul_comm] using sum_mul_left xs a f

theorem sum_swap (xs : List α) (ys : List β) (f : α → β → Int) :
    sumOver xs (fun i => sumOver ys (f i)) =
      sumOver ys (fun j => sumOver xs (fun i => f i j)) := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons j rest ih =>
      change 0 = sumOver rest (fun _ => 0) at ih
      simpa [sumOver] using ih
  | cons i rest ih => simp only [sumOver, ih, sum_add]

private theorem sum_nonneg (xs : List α) (f : α → Int)
    (hf : ∀ i ∈ xs, 0 ≤ f i) : 0 ≤ sumOver xs f := by
  induction xs with
  | nil => simp [sumOver]
  | cons i rest ih =>
    exact Int.add_nonneg (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

private theorem sum_pos (xs : List α) (f : α → Int)
    (hf : ∀ i ∈ xs, 0 ≤ f i) (j : α) (hj : j ∈ xs) (hp : 0 < f j) :
    0 < sumOver xs f := by
  induction xs with
  | nil => simp at hj
  | cons i rest ih =>
    have hr : ∀ k ∈ rest, 0 ≤ f k := fun k hk => hf k (by simp [hk])
    simp only [List.mem_cons] at hj
    simp only [sumOver]
    rcases hj with he | he
    · subst i
      have h := sum_nonneg rest f hr
      omega
    · have h := ih hr he
      have hi := hf i (by simp)
      omega

private theorem square_nonneg (a : Int) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- The Gram entry for two members of a finite vector family. -/
def gram (rs : List R) (u : I → R → Int) (i j : I) : Int :=
  sumOver rs (fun r => u i r * u j r)

def quadratic (is : List I) (M : I → I → Int) (x : I → Int) : Int :=
  sumOver is (fun i => sumOver is (fun j => x i * x j * M i j))

/-- The two finite index sums of the Gram quadratic form give a square per coordinate. -/
theorem gram_square_sum (is : List I) (rs : List R) (u : I → R → Int) (x : I → Int) :
    quadratic is (gram rs u) x =
      sumOver rs (fun r =>
        sumOver is (fun i => x i * u i r) * sumOver is (fun j => x j * u j r)) := by
  unfold quadratic gram
  simp only [← sum_mul_left]
  simp only [show ∀ a b c d : Int, a * b * (c * d) = (a * c) * (b * d) from
    fun a b c d => by ac_rfl]
  simp only [sum_swap is rs]
  simp only [sum_mul_left, sum_mul_right]

theorem gram_nonneg (is : List I) (rs : List R) (u : I → R → Int) (x : I → Int) :
    0 ≤ quadratic is (gram rs u) x := by
  rw [gram_square_sum]
  exact sum_nonneg _ _ (fun _ _ => square_nonneg _)

/-- Add the quadratic form of the diagonal matrix `δ I` on the listed indices. -/
def regularized (is : List I) (M : I → I → Int) (x : I → Int) (δ : Int) : Int :=
  quadratic is M x + δ * sumOver is (fun i => x i * x i)

theorem regularized_nonneg (is : List I) (rs : List R) (u : I → R → Int)
    (x : I → Int) (δ : Int) (hδ : 0 ≤ δ) :
    0 ≤ regularized is (gram rs u) x δ :=
  Int.add_nonneg (gram_nonneg is rs u x)
    (Int.mul_nonneg hδ (sum_nonneg _ _ (fun _ _ => square_nonneg _)))

theorem regularized_pos (is : List I) (rs : List R) (u : I → R → Int)
    (x : I → Int) (δ : Int) (hδ : 0 < δ)
    (j : I) (hj : j ∈ is) (hx : x j ≠ 0) :
    0 < regularized is (gram rs u) x δ := by
  have hsq : 0 < x j * x j := by
    by_cases h : 0 < x j
    · exact Int.mul_pos h h
    · exact Int.mul_pos_of_neg_of_neg (by omega) (by omega)
  have hdiag := sum_pos is (fun i => x i * x i) (fun _ _ => square_nonneg _) j hj hsq
  have hp := Int.mul_pos hδ hdiag
  have hg := gram_nonneg is rs u x
  unfold regularized
  omega

private theorem sum_diagonal [DecidableEq I] (is : List I) (i : I)
    (a : Int) (h : is.Nodup) :
    sumOver is (fun j => if i = j then a else 0) = if i ∈ is then a else 0 := by
  induction is with
  | nil => simp [sumOver]
  | cons j rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp h
    by_cases he : i = j
    · subst j
      simp [sumOver, ih hrest, hnot]
    · simp [sumOver, ih hrest, he]

/-- The ordinary matrix obtained by adding `δ` to each diagonal entry. -/
def addDiagonal [DecidableEq I] (M : I → I → Int) (δ : Int) (i j : I) : Int :=
  M i j + if i = j then δ else 0

theorem quadratic_addDiagonal [DecidableEq I] (is : List I) (M : I → I → Int)
    (x : I → Int) (δ : Int) (h : is.Nodup) :
    quadratic is (addDiagonal M δ) x = regularized is M x δ := by
  have inner (i : I) :
      sumOver is (fun j => x i * x j * (if i = j then δ else 0)) =
        if i ∈ is then δ * (x i * x i) else 0 := by
    have pointwise (j : I) :
        x i * x j * (if i = j then δ else 0) =
          if i = j then δ * (x i * x i) else 0 := by
      by_cases he : i = j
      · subst j
        simp only [if_true]
        ac_rfl
      · simp [he]
    simp only [pointwise, sum_diagonal is i _ h]
  have drop_if (xs : List I) (hs : ∀ i ∈ xs, i ∈ is) :
      sumOver xs (fun i => if i ∈ is then δ * (x i * x i) else 0) =
        sumOver xs (fun i => δ * (x i * x i)) := by
    induction xs with
    | nil => rfl
    | cons i rest ih =>
      rw [sumOver, sumOver, if_pos (hs i (by simp)), ih]
      exact fun j hj => hs j (by simp [hj])
  simp only [quadratic, addDiagonal, regularized, Int.mul_add, sum_add, inner]
  rw [drop_if is (fun _ hi => hi), sum_mul_left]

theorem gram_addDiagonal_pos [DecidableEq I] (is : List I) (rs : List R)
    (u : I → R → Int) (x : I → Int) (δ : Int) (h : is.Nodup) (hδ : 0 < δ)
    (j : I) (hj : j ∈ is) (hx : x j ≠ 0) :
    0 < quadratic is (addDiagonal (gram rs u) δ) x := by
  rw [quadratic_addDiagonal is _ x δ h]
  exact regularized_pos is rs u x δ hδ j hj hx

private theorem sum_map (xs : List α) (g : α → β) (f : β → Int) :
    sumOver (xs.map g) f = sumOver xs (fun i => f (g i)) := by
  induction xs with
  | nil => rfl
  | cons i rest ih => simp [sumOver, ih]

private theorem sum_perm {xs ys : List α} (h : xs.Perm ys) (f : α → Int) :
    sumOver xs f = sumOver ys f := by
  induction h with
  | nil => rfl
  | cons i _ ih => simp [sumOver, ih]
  | swap i j rest => simp [sumOver, Int.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Finite right-translation autocorrelation on a multiplicative group. -/
def correlation (rs : List R) (mul : R → R → R) (w : R → Int) (s : R) : Int :=
  sumOver rs (fun r => w r * w (mul r s))

/-- Translation reindexing makes a Gram entry an autocorrelation at `i⁻¹ * j`.
    The hypotheses are the group cancellation identity and preservation of the finite enumeration. -/
theorem translation_gram_entry (rs : List R) (mul : R → R → R) (inv : R → R)
    (w : R → Int) (i j : R)
    (hcancel : ∀ r, mul (mul r i) (mul (inv i) j) = mul r j)
    (hperm : (rs.map (fun r => mul r i)).Perm rs) :
    gram rs (fun k r => w (mul r k)) i j = correlation rs mul w (mul (inv i) j) := by
  let f := fun r => w r * w (mul r (mul (inv i) j))
  calc
    gram rs (fun k r => w (mul r k)) i j =
        sumOver (rs.map (fun r => mul r i)) f := by
      simp only [gram, sum_map, f, hcancel]
    _ = correlation rs mul w (mul (inv i) j) := sum_perm hperm f

/-- Expansion into the two family indices and the coordinate of the translated weights. -/
theorem translation_triple_sum (is rs : List R) (mul : R → R → R) (inv : R → R)
    (w x : R → Int)
    (hcancel : ∀ r i j, mul (mul r i) (mul (inv i) j) = mul r j)
    (hperm : ∀ i, (rs.map (fun r => mul r i)).Perm rs) :
    sumOver is (fun i => sumOver is (fun j =>
      x i * x j * correlation rs mul w (mul (inv i) j))) =
      sumOver rs (fun r =>
        sumOver is (fun i => x i * w (mul r i)) *
        sumOver is (fun j => x j * w (mul r j))) := by
  simp only [← translation_gram_entry rs mul inv w _ _ (fun r => hcancel r _ _) (hperm _)]
  exact gram_square_sum is rs (fun k r => w (mul r k)) x

#print axioms gram_square_sum
#print axioms gram_nonneg
#print axioms regularized_nonneg
#print axioms regularized_pos
#print axioms quadratic_addDiagonal
#print axioms gram_addDiagonal_pos
#print axioms translation_gram_entry
#print axioms translation_triple_sum

end Goldbach.GramCertificate
