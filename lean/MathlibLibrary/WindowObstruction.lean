import PaperFourier

namespace Goldbach.WindowObstruction
noncomputable section

/-- A continuous nonpositive function whose adjacent endpoint difference can
    be made arbitrarily large, despite the global zero upper envelope. -/
theorem nonpositive_large_endpoint (X : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ H : ℝ → ℝ, Continuous H ∧ (∀ y, H y ≤ 0) ∧
      PaperFourier.endpoint X H = ((X : ℝ) + 1) * B := by
  let H := fun y : ℝ => -B * max (1 - 2 * |y - (X : ℝ)|) 0
  refine ⟨H, ?_, ?_, ?_⟩
  · dsimp [H]
    fun_prop
  · intro y
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hB) (le_max_right _ _)
  · have hd : ((X : ℝ) + 1) - (X : ℝ) = 1 := by ring
    simp [PaperFourier.endpoint, H, hd]

#print axioms nonpositive_large_endpoint
end
end Goldbach.WindowObstruction
