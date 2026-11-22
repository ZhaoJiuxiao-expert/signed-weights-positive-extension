import Orthogonality
import RademacherBound
import Mathlib.NumberTheory.DirichletCharacter.Bounds

open scoped BigOperators

namespace Goldbach.PrimeCharacter

noncomputable section

variable {q : ℕ} [Fact q.Prime]

attribute [local instance] allCharacters

theorem exists_dirichlet_signs_mass_lower_bound
    (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ w : S → ℝ, (∀ n, w n = -1 ∨ w n = 1) ∧
      ∀ a : DirichletCharacter ℂ q → ℝ, (∀ χ, 0 ≤ a χ) →
        (∀ n : S, w n = ∑ χ, a χ * (χ ((n : ℕ) : ZMod q)).re) →
        Real.sqrt ((S.card : ℝ) / (2 * Real.log (2 * ((q - 1 : ℕ) : ℝ)))) ≤
          ∑ χ, a χ := by
  have hS' : 0 < Fintype.card S := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hS
  have hq : 0 < Fintype.card (DirichletCharacter ℂ q) := by
    rw [char_card]
    have hp := (Fact.out : q.Prime).one_lt
    omega
  have H := RademacherBound.exists_signs_mass_lower_bound
    (fun (n : S) (χ : DirichletCharacter ℂ q) => (χ ((n : ℕ) : ZMod q)).re)
    (fun n χ => by
      calc
        _ ≤ ‖χ ((n : ℕ) : ZMod q)‖ := by
          rw [Complex.norm_eq_abs]
          exact Complex.abs_re_le_abs _
        _ ≤ 1 := χ.norm_le_one ((n : ℕ) : ZMod q)) hS' hq
  simpa only [Fintype.card_coe, char_card] using H

#print axioms exists_dirichlet_signs_mass_lower_bound

end
end Goldbach.PrimeCharacter
