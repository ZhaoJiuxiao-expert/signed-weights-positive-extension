import Std

namespace PositiveWindow

def sumBy (f : Nat → Int) : List Nat → Int
  | [] => 0
  | n :: ns => f n + sumBy f ns

def amplitude (c : Int) (w : Nat → Int) (a : Nat) : Int :=
  if a = 1 then c else w a

/-- The quotient-coordinate kernel, with an optional diagonal offset. -/
def kernel (q : Nat) (S : List Nat) (c : Int) (w : Nat → Int)
    (δ : Int) (k : Nat) : Int :=
  sumBy (fun a =>
    sumBy (fun b => if a % q = (k * b) % q then
      amplitude c w a * amplitude c w b else 0) (1 :: S)) (1 :: S)
  + if k = 1 then δ else 0

private theorem sumBy_congr {f g : Nat → Int} {S : List Nat}
    (h : ∀ a ∈ S, f a = g a) : sumBy f S = sumBy g S := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      simp only [sumBy]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem sumBy_zero (S : List Nat) : sumBy (fun _ => 0) S = 0 := by
  induction S with
  | nil => rfl
  | cons _ S ih => simp [sumBy, ih]

private theorem sumBy_at (S : List Nat) (hS : S.Nodup) (k : Nat) (v : Int) :
    sumBy (fun a => if a = k then v else 0) S = if k ∈ S then v else 0 := by
  induction S with
  | nil => simp [sumBy]
  | cons a S ih =>
      obtain ⟨ha, hTailNodup⟩ := List.nodup_cons.mp hS
      by_cases hak : a = k
      · subst a
        simp [sumBy, ih hTailNodup, ha]
      · have hka : k ≠ a := Ne.symm hak
        simp [sumBy, ih hTailNodup, hak, hka]

private theorem eq_of_mod_iff {X q a b k : Nat} (hX : 2 ≤ X) (hq : X * X < q)
    (ha : a ≤ X) (hb : b ≤ X) (hk : k ≤ X) :
    a % q = (k * b) % q ↔ a = k * b := by
  have hXX : X ≤ X * X := by
    simpa using Nat.mul_le_mul_left X (show 1 ≤ X by omega)
  have haq : a < q := Nat.lt_of_le_of_lt (Nat.le_trans ha hXX) hq
  have hkbq : k * b < q := Nat.lt_of_le_of_lt (Nat.mul_le_mul hk hb) hq
  rw [Nat.mod_eq_of_lt haq, Nat.mod_eq_of_lt hkbq]

/-- Each off-diagonal coordinate in the prescribed window is supplied by one
    ordered pair, namely (k, 1), when k is in the support. -/
theorem kernel_window {X q k : Nat} {S : List Nat} (c : Int) (w : Nat → Int) (δ : Int)
    (hX : 2 ≤ X) (hq : X * X < q) (hS : S.Nodup)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b)
    (hk0 : 2 ≤ k) (hk : k ≤ X) :
    kernel q S c w δ k = if k ∈ S then c * w k else 0 := by
  have hAll (a : Nat) (ha : a ∈ 1 :: S) : a ≤ X := by
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact (hRange a ha).2
  have hPair (a b : Nat) (ha : a ∈ 1 :: S) (hb : b ∈ 1 :: S) :
      a % q = (k * b) % q ↔ a = k ∧ b = 1 := by
    rw [eq_of_mod_iff hX hq (hAll a ha) (hAll b hb) hk]
    constructor
    · intro h
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        simpa using h
      · have hTwo : 2 * b ≤ k * b := Nat.mul_le_mul_right b hk0
        rcases List.mem_cons.mp ha with ha | ha
        · have hB := (hRange b hb).1
          omega
        · have hR := hRatio a ha b hb
          omega
    · rintro ⟨rfl, rfl⟩
      simp
  have hRow (a : Nat) (ha : a ∈ 1 :: S) :
      sumBy (fun b => if a % q = (k * b) % q then
          amplitude c w a * amplitude c w b else 0) (1 :: S) =
        if a = k then c * w k else 0 := by
    rw [sumBy]
    have hTail : sumBy (fun b => if a % q = (k * b) % q then
          amplitude c w a * amplitude c w b else 0) S = 0 := by
      refine Eq.trans (sumBy_congr (g := fun _ => 0) ?_) (sumBy_zero S)
      intro b hb
      have hB := (hRange b hb).1
      simp [hPair a b ha (by simp [hb]), show b ≠ 1 by omega]
    simp only [hTail, Int.add_zero, hPair a 1 ha (by simp)]
    have hk1 : k ≠ 1 := by omega
    by_cases hak : a = k
    · subst a
      simp [amplitude, hk1, Int.mul_comm]
    · simp [hak]
  have hk1 : k ≠ 1 := by omega
  have h1k : 1 ≠ k := Ne.symm hk1
  unfold kernel
  rw [sumBy_congr hRow]
  simp only [if_neg hk1, Int.add_zero, sumBy, if_neg h1k, Int.zero_add]
  exact sumBy_at S hS k (c * w k)

/-- The identity coordinate is the sum of the squares and the offset. -/
theorem kernel_one {X q : Nat} {S : List Nat} (c : Int) (w : Nat → Int) (δ : Int)
    (hX : 2 ≤ X) (hq : X * X < q) (hS : S.Nodup)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X) :
    kernel q S c w δ 1 = c * c + sumBy (fun n => w n * w n) S + δ := by
  have hNot : 1 ∉ S := by
    intro h
    have := (hRange 1 h).1
    omega
  have hNodup : (1 :: S).Nodup := List.nodup_cons.mpr ⟨hNot, hS⟩
  have hAll (a : Nat) (ha : a ∈ 1 :: S) : a ≤ X := by
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · exact (hRange a ha).2
  have hRow (a : Nat) (ha : a ∈ 1 :: S) :
      sumBy (fun b => if a % q = (1 * b) % q then
          amplitude c w a * amplitude c w b else 0) (1 :: S) =
        amplitude c w a * amplitude c w a := by
    calc
      _ = sumBy (fun b => if b = a then amplitude c w a * amplitude c w a else 0)
          (1 :: S) := by
        apply sumBy_congr
        intro b hb
        have hmod : a % q = b % q ↔ a = b := by
          simpa using eq_of_mod_iff (k := 1) hX hq (hAll a ha) (hAll b hb) (by omega)
        simp only [Nat.one_mul, hmod]
        by_cases hab : b = a
        · subst b
          simp
        · simp [hab, Ne.symm hab]
      _ = _ := by rw [sumBy_at _ hNodup, if_pos ha]
  unfold kernel
  rw [sumBy_congr hRow]
  simp only [if_pos rfl, sumBy, amplitude]
  congr 2
  apply sumBy_congr
  intro n hn
  have := (hRange n hn).1
  simp [show n ≠ 1 by omega]

#print axioms kernel_window
#print axioms kernel_one

end PositiveWindow
