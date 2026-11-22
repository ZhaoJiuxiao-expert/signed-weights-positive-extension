import FourierWindow

open scoped BigOperators

namespace Goldbach.FourierWindow

/-- On prime levels the principal character is one at every support point.
    It therefore contributes the square of the real sum of the amplitudes. -/
theorem principal_mass {q X : ℕ} [Fact (Nat.Prime q)]
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (hX : 2 ≤ X) (hq : X * X < q)
    (hRange : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X) :
    dirichletCoeff S c ((q - 1 : ℕ) : ℝ) w
      (id : DirichletCharacter ℂ q → _) 1 =
        (c + ∑ n in S, w n) ^ 2 / (c * ((q - 1 : ℕ) : ℝ)) := by
  classical
  have hXq : X < q :=
    lt_of_le_of_lt (by simpa using Nat.mul_le_mul_left X (show 1 ≤ X by omega)) hq
  have hNot : 1 ∉ S := by
    intro h
    have := (hRange 1 h).1
    omega
  have hUnit (n : ℕ) (hn : n ∈ S) : IsUnit (n : ZMod q) := by
    have ⟨h2, hle⟩ := hRange n hn
    apply isUnit_iff_ne_zero.mpr
    intro he
    have hval := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hle.trans_lt hXq), ZMod.val_zero] at hval
    omega
  have hSum :
      (∑ n in S, ((if n = 1 then c else w n : ℝ) : ℂ) *
        (1 : DirichletCharacter ℂ q) (n : ZMod q)) = ∑ n in S, (w n : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [MulChar.one_apply (hUnit n hn), mul_one]
    have := (hRange n hn).1
    simp [show n ≠ 1 by omega]
  unfold dirichletCoeff spectralWeight
  simp only [id_eq, MulChar.coe_toMonoidHom]
  rw [Finset.sum_insert hNot, hSum, ← Complex.ofReal_sum]
  simp only [if_true, Nat.cast_one, map_one, mul_one, ← Complex.ofReal_add,
    Complex.normSq_ofReal, pow_two]

/-- The lower bound for the total mass of this parameterized construction. -/
theorem mass_lower_bound (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    2 * Real.sqrt V ≤ c + V / c := by
  have hSq := Real.sq_sqrt hV
  have hIdentity : c + V / c - 2 * Real.sqrt V = (c - Real.sqrt V) ^ 2 / c := by
    field_simp [hc.ne']
    nlinarith
  have hNonneg := div_nonneg (sq_nonneg (c - Real.sqrt V)) hc.le
  linarith

#print axioms principal_mass
#print axioms mass_lower_bound

end Goldbach.FourierWindow
