import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace Goldbach.PrimeCharacter
noncomputable section
variable {q : ℕ} [Fact q.Prime]

/-- Every character on the units, enumerated via the complex roots of unity. -/
noncomputable def allCharacters (q : ℕ) [Fact q.Prime] : Fintype (DirichletCharacter ℂ q) :=
  Fintype.ofEquiv _ (MulChar.equiv_rootsOfUnity (ZMod q) ℂ).symm.toEquiv

attribute [local instance] allCharacters

theorem char_card :
    Fintype.card (DirichletCharacter ℂ q) = q - 1 := by
  rw [Fintype.card_congr (MulChar.equiv_rootsOfUnity (ZMod q) ℂ).toEquiv,
    Complex.card_rootsOfUnity]
  change Fintype.card (ZMod q)ˣ = q - 1
  rw [Fintype.card_units, ZMod.card]

/-- The dual separates distinct units: embed the cyclic unit group in ℂˣ. -/
private theorem separates (u v : (ZMod q)ˣ) (huv : u ≠ v) :
    ∃ ψ : DirichletCharacter ℂ q, ψ u ≠ ψ v := by
  classical
  let n := MulChar.Monoid.orderUnits (ZMod q)
  let e : (ZMod q)ˣ ≃* rootsOfUnity n ℂ := mulEquivOfCyclicCardEq (by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
    rfl)
  let f : (ZMod q)ˣ →* ℂˣ := (rootsOfUnity n ℂ).subtype.comp e.toMonoidHom
  refine ⟨MulChar.equivToUnitHom.symm f, ?_⟩
  simp only [MulChar.equivToUnitHom_symm_coe]
  intro heq
  apply huv
  apply e.injective
  apply Subtype.ext
  exact Units.ext heq

private theorem conj_mul_self_unit (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ u) * χ u = 1 := by
  change star (χ u) * χ u = 1
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_mul_cancel₀]
  exact (u.isUnit.map χ.toMonoidHom).ne_zero

/-- For the complete actual Dirichlet family at prime level, the Fourier
    columns over units are orthogonal and their squared length is q−1. -/
theorem orthogonality (u v : ZMod q) (hu : IsUnit u) (hv : IsUnit v) :
    ∑ χ : DirichletCharacter ℂ q, conj (χ u) * χ v =
      if u = v then ((q - 1 : ℕ) : ℂ) else 0 := by
  classical
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨v, rfl⟩ := hv
  by_cases heq : u = v
  · subst v
    simp [conj_mul_self_unit, char_card]
  · have huv : (u : ZMod q) ≠ v := fun he => heq (Units.ext he)
    rw [if_neg huv]
    obtain ⟨ψ, hψ⟩ := separates u v heq
    let t : DirichletCharacter ℂ q → ℂ := fun χ => conj (χ u) * χ v
    have hmul (χ : DirichletCharacter ℂ q) : t (ψ * χ) = t ψ * t χ := by
      simp only [t, MulChar.mul_apply, map_mul]
      ring
    have hshift : t ψ * (∑ χ, t χ) = ∑ χ, t χ := by
      rw [Finset.mul_sum]
      simp_rw [← hmul]
      exact (Group.mulLeft_bijective ψ).sum_comp t
    have hne : t ψ ≠ 1 := by
      intro ht
      have h := conj_mul_self_unit ψ u
      have h0 : conj (ψ u) ≠ 0 := left_ne_zero_of_mul (by rw [h]; exact one_ne_zero)
      apply hψ
      apply mul_left_cancel₀ h0
      exact h.trans ht.symm
    change ∑ χ, t χ = 0
    exact (mul_eq_zero.mp (show (t ψ - 1) * (∑ χ, t χ) = 0 by
      rw [sub_mul, one_mul, hshift, sub_self])).resolve_left (sub_ne_zero.mpr hne)

#print axioms orthogonality
end
end Goldbach.PrimeCharacter
