import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace Goldbach.FourierWindow

noncomputable section

variable {I : Type*} {R : Type*} [CommMonoid R]

/-- Unnormalized nonnegative weight of one character. -/
def spectralWeight (χ : I → R →* ℂ) (u : ℕ → R) (T : Finset ℕ)
    (A : ℕ → ℝ) (i : I) : ℝ :=
  Complex.normSq (∑ a in T, (A a : ℂ) * χ i (u a))

theorem spectralWeight_nonneg (χ : I → R →* ℂ) (u : ℕ → R) (T : Finset ℕ)
    (A : ℕ → ℝ) (i : I) : 0 ≤ spectralWeight χ u T A i :=
  Complex.normSq_nonneg _

variable [Fintype I]

/-- Expand the squared magnitudes, then apply character orthogonality. -/
theorem spectral_expand (χ : I → R →* ℂ) (u : ℕ → R) (T : Finset ℕ)
    (A : ℕ → ℝ) (k : R) [DecidableEq R] (h : ℂ)
    (hOrth : ∀ a ∈ T, ∀ b ∈ T,
      ∑ i : I, conj (χ i (u a)) * χ i (k * u b) = if u a = k * u b then h else 0) :
    ∑ i : I, (spectralWeight χ u T A i : ℂ) * χ i k =
      h * ∑ a in T, ∑ b in T, if u a = k * u b then (A a : ℂ) * A b else 0 := by
  classical
  have expand (i : I) :
      (spectralWeight χ u T A i : ℂ) * χ i k =
        ∑ a in T, ∑ b in T, ((A a : ℂ) * A b) *
          (conj (χ i (u a)) * χ i (k * u b)) := by
    simp only [spectralWeight, Complex.normSq_eq_conj_mul_self, map_sum, map_mul,
      Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [expand]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hOrth a ha b hb]
  split_ifs <;> ring



/-- The elementary congruence reduces to equality throughout the window. -/
private theorem mod_eq_iff {X q a b k : ℕ} (hX : 2 ≤ X) (hq : X * X < q)
    (ha : a ≤ X) (hb : b ≤ X) (hk : k ≤ X) :
    (a : ZMod q) = (k : ZMod q) * (b : ZMod q) ↔ a = k * b := by
  have hXX : X ≤ X * X := by
    simpa using Nat.mul_le_mul_left X (show 1 ≤ X by omega)
  have haq : a < q := lt_of_le_of_lt (ha.trans hXX) hq
  have hkbq : k * b < q := lt_of_le_of_lt (Nat.mul_le_mul hk hb) hq
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt haq, Nat.mod_eq_of_lt hkbq]

/-- The coefficients in the paper, using amplitude c at 1 and w on S. -/
def dirichletCoeff {q : ℕ} (S : Finset ℕ) (c h : ℝ) (w : ℕ → ℝ)
    (χ : I → DirichletCharacter ℂ q) (i : I) : ℝ :=
  spectralWeight (fun i => (χ i).toMonoidHom) (fun a => (a : ZMod q))
    (insert 1 S) (fun a => if a = 1 then c else w a) i / (c * h)

/-- Prime-modulus real-weight interpolation from the orthogonality of the
    indexed Dirichlet characters. The same weights control all window entries. -/
theorem dirichlet_window_coefficients {X q : ℕ} (S : Finset ℕ) (c h : ℝ)
    (w : ℕ → ℝ) (χ : I → DirichletCharacter ℂ q)
    (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c) (hh : 0 < h)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b)
    (hOrth : ∀ u v : ZMod q, IsUnit u → IsUnit v →
      ∑ i : I, conj (χ i u) * χ i v = if u = v then (h : ℂ) else 0)
    [Fact (Nat.Prime q)] :
    let coeff := dirichletCoeff S c h w χ
    (∀ i, 0 ≤ coeff i) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ X →
        ∑ i : I, (coeff i : ℂ) * χ i (k : ZMod q) =
        if k ∈ S then (w k : ℂ) else 0) ∧
      ∑ i : I, coeff i = c + (∑ n in S, w n * w n) / c := by
  classical
  let T := insert 1 S
  let A : ℕ → ℝ := fun a => if a = 1 then c else w a
  let W := spectralWeight (fun i => (χ i).toMonoidHom) (fun a => (a : ZMod q)) T A
  let coeff : I → ℝ := dirichletCoeff S c h w χ
  change (∀ i, 0 ≤ coeff i) ∧ _
  have h1S : 1 ∉ S := by
    intro hmem
    have := (hRange 1 hmem).1
    omega
  have hBounds (a : ℕ) (ha : a ∈ T) : 1 ≤ a ∧ a ≤ X := by
    rcases Finset.mem_insert.mp ha with rfl | hm
    · omega
    · have := hRange a hm
      omega
  have hUnit (a : ℕ) (ha : 1 ≤ a) (haX : a ≤ X) : IsUnit (a : ZMod q) := by
    have hXq : X < q := lt_of_le_of_lt (by
      simpa using Nat.mul_le_mul_left X (show 1 ≤ X by omega)) hq
    have hne : (a : ZMod q) ≠ 0 := by
      intro he
      have hval := congrArg ZMod.val he
      rw [ZMod.val_natCast_of_lt (haX.trans_lt hXq), ZMod.val_zero] at hval
      omega
    exact isUnit_iff_ne_zero.mpr hne
  have hExpand (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ X) :
      ∑ i : I, (W i : ℂ) * χ i (k : ZMod q) =
        (h : ℂ) * ∑ a in T, ∑ b in T,
          if a = k * b then (A a : ℂ) * A b else 0 := by
    calc
      _ = (h : ℂ) * ∑ a in T, ∑ b in T,
          if (a : ZMod q) = (k : ZMod q) * (b : ZMod q) then (A a : ℂ) * A b else 0 := by
        apply spectral_expand
        intro a ha b hb
        exact hOrth _ _ (hUnit a (hBounds a ha).1 (hBounds a ha).2)
          ((hUnit k hk0 hk).mul (hUnit b (hBounds b hb).1 (hBounds b hb).2))
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        simp only [mod_eq_iff hX hq (hBounds a ha).2 (hBounds b hb).2 hk]
  have hScale (k : ℕ) :
      ∑ i : I, (coeff i : ℂ) * χ i (k : ZMod q) =
        (∑ i : I, (W i : ℂ) * χ i (k : ZMod q)) / ((c : ℂ) * h) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coeff, dirichletCoeff, Complex.ofReal_div, Complex.ofReal_mul]
    ring
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  refine ⟨fun i => div_nonneg (spectralWeight_nonneg ..) (mul_nonneg hc.le hh.le), ?_, ?_⟩
  · intro k hk0 hk
    have hPair (a b : ℕ) (ha : a ∈ T) (hb : b ∈ T) : a = k * b ↔ a = k ∧ b = 1 := by
      constructor
      · intro he
        rcases Finset.mem_insert.mp hb with rfl | hbs
        · simpa using he
        · have hTwo : 2 * b ≤ k * b := Nat.mul_le_mul_right b hk0
          rcases Finset.mem_insert.mp ha with ha1 | has
          · have := (hRange b hbs).1
            omega
          · have := hRatio a has b hbs
            omega
      · rintro ⟨rfl, rfl⟩
        simp
    have hSums :
        (∑ a in T, ∑ b in T, if a = k * b then (A a : ℂ) * A b else 0) =
          if k ∈ S then (w k : ℂ) * c else 0 := by
      have row (a : ℕ) (ha : a ∈ T) :
          (∑ b in T, if a = k * b then (A a : ℂ) * A b else 0) =
            if a = k then (w k : ℂ) * c else 0 := by
        calc
          _ = ∑ b in T, if b = 1 then (if a = k then (w k : ℂ) * c else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            simp only [hPair a b ha hb]
            by_cases hbk : b = 1
            · subst b
              by_cases hak : a = k
              · subst a
                simp [A, show k ≠ 1 by omega]
              · simp [hak]
            · simp [hbk]
          _ = _ := by simp [T]
      calc
        _ = ∑ a in T, if a = k then (w k : ℂ) * c else 0 :=
          Finset.sum_congr rfl row
        _ = _ := by simp [T, show k ≠ 1 by omega]
    rw [hScale, hExpand k (by omega) hk, hSums]
    split_ifs
    · field_simp
      ring
    · simp
  · have hMass :
        (∑ a in T, ∑ b in T, if a = 1 * b then (A a : ℂ) * A b else 0) =
          (c : ℂ) * c + ∑ n in S, (w n : ℂ) * w n := by
      simp only [one_mul]
      have row (a : ℕ) (ha : a ∈ T) :
          (∑ b in T, if a = b then (A a : ℂ) * A b else 0) = (A a : ℂ) * A a := by
        calc
          _ = ∑ b in T, if b = a then (A a : ℂ) * A a else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hba : b = a
            · subst b
              simp
            · simp [hba, Ne.symm hba]
          _ = _ := by simp [ha]
      rw [Finset.sum_congr rfl row]
      rw [show T = insert 1 S from rfl, Finset.sum_insert h1S]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      have := (hRange n hn).1
      simp [A, show n ≠ 1 by omega]
    have he := hScale 1
    simp only [Nat.cast_one, map_one, mul_one] at he
    have hExp := hExpand 1 (by omega) (by omega)
    rw [hMass] at hExp
    simp only [Nat.cast_one, map_one, mul_one] at hExp
    rw [hExp] at he
    have hComplex : (∑ i : I, (coeff i : ℂ)) =
        (c : ℂ) + (∑ n in S, (w n : ℂ) * w n) / (c : ℂ) := by
      rw [he]
      field_simp
      ring
    exact_mod_cast hComplex


/-- Prime-modulus real-weight interpolation from the orthogonality of the
    indexed Dirichlet characters. The same weights control all window entries. -/
theorem dirichlet_window_of_orthogonality {X q : ℕ} (S : Finset ℕ) (c h : ℝ)
    (w : ℕ → ℝ) (χ : I → DirichletCharacter ℂ q)
    (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c) (hh : 0 < h)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b)
    (hOrth : ∀ u v : ZMod q, IsUnit u → IsUnit v →
      ∑ i : I, conj (χ i u) * χ i v = if u = v then (h : ℂ) else 0)
    [Fact (Nat.Prime q)] :
    ∃ coeff : I → ℝ,
      (∀ i, 0 ≤ coeff i) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ X →
        ∑ i : I, (coeff i : ℂ) * χ i (k : ZMod q) =
        if k ∈ S then (w k : ℂ) else 0) ∧
      ∑ i : I, coeff i = c + (∑ n in S, w n * w n) / c := by
  exact ⟨dirichletCoeff S c h w χ,
    dirichlet_window_coefficients S c h w χ hX hq hc hh hRange hRatio hOrth⟩

/-- Conjugate Dirichlet characters receive the same coefficient. -/
theorem dirichletCoeff_star {q : ℕ} (S : Finset ℕ) (c h : ℝ) (w : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    dirichletCoeff S c h w id (star χ) = dirichletCoeff S c h w id χ := by
  let T := insert 1 S
  let A : ℕ → ℝ := fun a => if a = 1 then c else w a
  have hsum : (∑ a in T, (A a : ℂ) * (star χ) (a : ZMod q)) =
      conj (∑ a in T, (A a : ℂ) * χ (a : ZMod q)) := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, MulChar.star_apply]
    rfl
  change Complex.normSq (∑ a in T, (A a : ℂ) * (star χ) (a : ZMod q)) / (c * h) =
    Complex.normSq (∑ a in T, (A a : ℂ) * χ (a : ZMod q)) / (c * h)
  rw [hsum, Complex.normSq_conj]

#print axioms spectral_expand
#print axioms dirichlet_window_coefficients
#print axioms dirichlet_window_of_orthogonality
#print axioms dirichletCoeff_star

end
end Goldbach.FourierWindow
