import FourierWindow
import Orthogonality

open scoped BigOperators

namespace Goldbach.PrimeCharacter
noncomputable section
attribute [local instance] allCharacters

/-- Exact signed interpolation, including the complementary zero coordinates,
    by a nonnegative measure on all Dirichlet characters of prime level. -/
theorem positive_window {X q : ℕ} [Fact (Nat.Prime q)] (S : Finset ℕ)
    (c : ℝ) (w : ℕ → ℝ) (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b) :
    ∃ coeff : DirichletCharacter ℂ q → ℝ,
      (∀ χ, 0 ≤ coeff χ) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ X →
        ∑ χ : DirichletCharacter ℂ q, (coeff χ : ℂ) * χ (k : ZMod q) =
        if k ∈ S then (w k : ℂ) else 0) ∧
      ∑ χ : DirichletCharacter ℂ q, coeff χ = c + (∑ n in S, w n * w n) / c := by
  have hp : Nat.Prime q := Fact.out
  have hh : 0 < q - 1 := by have := hp.two_le; omega
  exact FourierWindow.dirichlet_window_of_orthogonality S c ((q - 1 : ℕ) : ℝ)
    w id hX hq hc (by exact_mod_cast hh) hRange hRatio
    (fun u v hu hv => by simpa using orthogonality u v hu hv)

/-- The optimal parameter in this construction realizes twice the Euclidean norm. -/
theorem positive_window_sqrt {X q : ℕ} [Fact (Nat.Prime q)] (S : Finset ℕ)
    (w : ℕ → ℝ) (hX : 2 ≤ X) (hq : X * X < q)
    (hV : 0 < ∑ n in S, w n * w n)
    (hRange : ∀ a ∈ S, 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ a ∈ S, ∀ b ∈ S, a < 2 * b) :
    ∃ coeff : DirichletCharacter ℂ q → ℝ,
      (∀ χ, 0 ≤ coeff χ) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ X →
        ∑ χ : DirichletCharacter ℂ q, (coeff χ : ℂ) * χ (k : ZMod q) =
        if k ∈ S then (w k : ℂ) else 0) ∧
      ∑ χ : DirichletCharacter ℂ q, coeff χ = 2 * Real.sqrt (∑ n in S, w n * w n) := by
  let V := ∑ n in S, w n * w n
  have hpos : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  obtain ⟨a, ha, hk, hm⟩ := positive_window S (Real.sqrt V) w hX hq hpos hRange hRatio
  refine ⟨a, ha, hk, ?_⟩
  rw [hm]
  change Real.sqrt V + V / Real.sqrt V = 2 * Real.sqrt V
  field_simp [hpos.ne']
  nlinarith [Real.sq_sqrt hV.le]

#print axioms positive_window
#print axioms positive_window_sqrt
end
end Goldbach.PrimeCharacter
