import FourierWindow
import Orthogonality
import PaperFourier
import Mathlib.NumberTheory.VonMangoldt

open scoped BigOperators

namespace Goldbach.PrimeEndpoint

open FourierWindow PrimeCharacter
attribute [local instance] allCharacters

noncomputable section

/-- The real part of the uncentered character ramp at the two endpoints uses
    only n ≤ X + 1, so one fixed finite sum represents both evaluations. -/
def characterRamp (q X : ℕ) (a : ℕ → ℝ) (χ : DirichletCharacter ℂ q)
    (y : ℝ) : ℝ :=
  ∑ n in Finset.Icc 1 (X + 1), a n * (χ (n : ZMod q)).re * PaperFourier.ramp y n

/-- The centered sum of character ramps with arbitrary linear corrections.
    The principal character additionally contributes the negative y log y term. -/
def centeredSpectralRamp (q X : ℕ) [Fact (Nat.Prime q)]
    (a : ℕ → ℝ) (coeff linear : DirichletCharacter ℂ q → ℝ) (y : ℝ) : ℝ :=
  (∑ χ : DirichletCharacter ℂ q, coeff χ * (characterRamp q X a χ y - linear χ * y)) -
    coeff 1 * (y * Real.log y)

/-- Exact endpoint extraction for any arithmetic weight vanishing at one.
    The spectral coefficients are fixed by the positive-window construction. -/
theorem weighted_endpoint {q X : ℕ} [Fact (Nat.Prime q)]
    (S : Finset ℕ) (c : ℝ) (w a : ℕ → ℝ) (linear : DirichletCharacter ℂ q → ℝ)
    (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c) (ha : a 1 = 0)
    (hRange : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X)
    (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2 * m) :
    let coeff := dirichletCoeff S c ((q - 1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _)
    (∑ n in S, a n * w n) =
      PaperFourier.endpoint X (centeredSpectralRamp q X a coeff linear) +
        coeff 1 * (X : ℝ) * ((X : ℝ) + 1) *
          Real.log (1 + 1 / (X : ℝ)) := by
  let coeff := dirichletCoeff S c ((q - 1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _)
  change _ = PaperFourier.endpoint X (centeredSpectralRamp q X a coeff linear) + _
  have hp : Nat.Prime q := Fact.out
  have hh : 0 < q - 1 := by have := hp.two_le; omega
  have hFourier := dirichlet_window_coefficients S c ((q - 1 : ℕ) : ℝ) w
    (id : DirichletCharacter ℂ q → _) hX hq hc (by exact_mod_cast hh) hRange hRatio
    (fun u v hu hv => by simpa using orthogonality u v hu hv)
  let reconstructed : ℕ → ℝ := fun n =>
    ∑ χ : DirichletCharacter ℂ q, coeff χ * (χ (n : ZMod q)).re
  have hReconstruct (n : ℕ) (hn : 2 ≤ n) (hnX : n ≤ X) :
      reconstructed n = if n ∈ S then w n else 0 := by
    have he := congrArg Complex.re (hFourier.2.1 n hn hnX)
    by_cases hmem : n ∈ S
    · simpa [reconstructed, coeff, hmem, Complex.re_sum, Complex.mul_re] using he
    · simpa [reconstructed, coeff, hmem, Complex.re_sum, Complex.mul_re] using he
  let T := Finset.Icc (1 : ℕ) (X + 1)
  have hT (n : ℕ) (hn : n ∈ T) : 0 < n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hRecover :
      (∑ n in T.filter (fun n => n ≤ X), a n * reconstructed n) =
        ∑ n in S, a n * w n := by
    have hSub : S ⊆ T.filter (fun n => n ≤ X) := by
      intro n hn
      have ⟨hn2, hnX⟩ := hRange n hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hnX⟩
    rw [← Finset.sum_subset hSub (f := fun n => a n * reconstructed n)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [hReconstruct n (hRange n hn).1 (hRange n hn).2, if_pos hn]
    · intro n hn hNot
      have ⟨hnT, hnX⟩ := Finset.mem_filter.mp hn
      by_cases hn1 : n = 1
      · subst n
        simp [ha]
      · rw [hReconstruct n (by have := hT n hnT; omega) hnX, if_neg hNot, mul_zero]
  have hCenter (y : ℝ) :
      (∑ n in T, (a n * reconstructed n) * PaperFourier.ramp y (n : ℝ)) =
        centeredSpectralRamp q X a coeff linear y +
        coeff 1 * (y * Real.log y) +
        (∑ χ : DirichletCharacter ℂ q, coeff χ * linear χ) * y := by
    unfold centeredSpectralRamp characterRamp
    simp only [T, reconstructed, Finset.mul_sum, Finset.sum_mul, mul_sub,
      ← Finset.sum_sub_distrib]
    have hSwap :
        (∑ n in Finset.Icc (1 : ℕ) (X + 1), ∑ χ : DirichletCharacter ℂ q,
          a n * (coeff χ * (χ (n : ZMod q)).re) * PaperFourier.ramp y (n : ℝ)) =
        ∑ χ : DirichletCharacter ℂ q, ∑ n in Finset.Icc (1 : ℕ) (X + 1),
          coeff χ * (a n * (χ (n : ZMod q)).re * PaperFourier.ramp y (n : ℝ)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hSwap, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    ring
  rw [← hRecover]
  exact PaperFourier.centered_ramp_endpoint X (by omega) T
    (fun n => a n * reconstructed n) hT
    (centeredSpectralRamp q X a coeff linear) (coeff 1)
    (∑ χ : DirichletCharacter ℂ q, coeff χ * linear χ) hCenter

/-- The von Mangoldt specialization of the exact endpoint formula. -/
theorem vonMangoldt_endpoint {q X : ℕ} [Fact (Nat.Prime q)]
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (linear : DirichletCharacter ℂ q → ℝ)
    (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c)
    (hRange : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X)
    (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2 * m) :
    let a := ArithmeticFunction.vonMangoldt
    let coeff := dirichletCoeff S c ((q - 1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _)
    (∑ n in S, a n * w n) =
      PaperFourier.endpoint X (centeredSpectralRamp q X a coeff linear) +
        coeff 1 * (X : ℝ) * ((X : ℝ) + 1) *
          Real.log (1 + 1 / (X : ℝ)) :=
  weighted_endpoint S c w ArithmeticFunction.vonMangoldt linear hX hq hc
    ArithmeticFunction.vonMangoldt_apply_one hRange hRatio

#print axioms weighted_endpoint
#print axioms vonMangoldt_endpoint

end
end Goldbach.PrimeEndpoint
