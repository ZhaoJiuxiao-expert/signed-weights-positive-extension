import PrimeWindow

open scoped BigOperators

namespace Goldbach.PrimeCharacter
noncomputable section
attribute [local instance] allCharacters

/-- Add the measures for finitely many ratio-separated blocks. For disjoint
    support blocks the target sum in each coordinate has at most one term. -/
theorem block_sum {J X q : ℕ} [Fact (Nat.Prime q)]
    (S : Fin J → Finset ℕ) (w : ℕ → ℝ) (hX : 2 ≤ X) (hq : X * X < q)
    (hRange : ∀ j a, a ∈ S j → 2 ≤ a ∧ a ≤ X)
    (hRatio : ∀ j a, a ∈ S j → ∀ b ∈ S j, a < 2 * b)
    (hV : ∀ j, 0 < ∑ n in S j, w n * w n) :
    ∃ coeff : DirichletCharacter ℂ q → ℝ,
      (∀ χ, 0 ≤ coeff χ) ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ X →
        ∑ χ : DirichletCharacter ℂ q, (coeff χ : ℂ) * χ (k : ZMod q) =
        ∑ j : Fin J, if k ∈ S j then (w k : ℂ) else 0) ∧
      ∑ χ : DirichletCharacter ℂ q, coeff χ ≤
        2 * Real.sqrt J * Real.sqrt (∑ j, ∑ n in S j, w n * w n) := by
  classical
  choose b hpos hrecon hmass using fun j =>
    positive_window_sqrt (S j) w hX hq (hV j) (hRange j) (hRatio j)
  refine ⟨fun χ => ∑ j, b j χ, fun χ => Finset.sum_nonneg (fun j _ => hpos j χ), ?_, ?_⟩
  · intro k hk hkX
    simp only [Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hrecon j k hk hkX)
  · rw [Finset.sum_comm]
    simp_rw [hmass]
    rw [← Finset.mul_sum, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin J))
      (f := fun _ => (1 : ℝ)) (g := fun j => ∑ n in S j, w n * w n)
      (fun _ => zero_le_one) (fun j => (hV j).le)
    simpa using hcs

#print axioms block_sum
end
end Goldbach.PrimeCharacter
