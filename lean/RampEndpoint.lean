import Std

namespace RampEndpoint

/-- The positive-part ramp, with subtraction truncated in the natural numbers. -/
def ramp (n y : Nat) : Int := ((y - n : Nat) : Int)

/-- The weighted forward difference at the integer endpoint. -/
def endpointDiff (X : Nat) (H : Nat → Int) : Int :=
  (X : Int) * H (X + 1) - ((X : Int) + 1) * H X

theorem endpointDiff_ramp (X n : Nat) :
    endpointDiff X (ramp n) = if n ≤ X then (n : Int) else 0 := by
  by_cases h : n ≤ X
  · have h' : n ≤ X + 1 := by omega
    simp only [endpointDiff, ramp, if_pos h, Int.ofNat_sub h, Int.ofNat_sub h',
      Int.ofNat_add, Int.ofNat_one, Int.mul_sub, Int.mul_add, Int.add_mul,
      Int.mul_one, Int.one_mul]
    omega
  · have h₀ : X - n = 0 := by omega
    have h₁ : X + 1 - n = 0 := by omega
    simp [endpointDiff, ramp, h, h₀, h₁]

private theorem endpointDiff_add (X : Nat) (H G : Nat → Int) :
    endpointDiff X (fun y => H y + G y) = endpointDiff X H + endpointDiff X G := by
  simp only [endpointDiff, Int.mul_add]
  omega

private theorem endpointDiff_mul (X : Nat) (c : Int) (H : Nat → Int) :
    endpointDiff X (fun y => c * H y) = c * endpointDiff X H := by
  simp only [endpointDiff, Int.mul_sub]
  rw [Int.mul_left_comm (X : Int) c, Int.mul_left_comm ((X : Int) + 1) c]

def sumBy {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | n :: ns => f n + sumBy f ns

/-- Repeated indices are counted with their multiplicities; weights may be negative. -/
theorem endpointDiff_weighted_ramps (X : Nat) (ns : List Nat) (weight : Nat → Int) :
    endpointDiff X (fun y => sumBy (fun n => weight n * ramp n y) ns) =
      sumBy (fun n => if n ≤ X then weight n * (n : Int) else 0) ns := by
  induction ns with
  | nil => simp [endpointDiff, sumBy]
  | cons n ns ih =>
      simp only [sumBy]
      rw [endpointDiff_add, endpointDiff_mul, endpointDiff_ramp, ih]
      by_cases h : n ≤ X <;> simp [h]

/-- Each occurrence can carry its own signed weight, even at repeated indices. -/
theorem endpointDiff_weighted_terms (X : Nat) (terms : List (Nat × Int)) :
    endpointDiff X (fun y => sumBy (fun (n, c) => c * ramp n y) terms) =
      sumBy (fun (n, c) => if n ≤ X then c * (n : Int) else 0) terms := by
  induction terms with
  | nil => simp [endpointDiff, sumBy]
  | cons term terms ih =>
      obtain ⟨n, c⟩ := term
      simp only [sumBy]
      rw [endpointDiff_add, endpointDiff_mul, endpointDiff_ramp, ih]
      by_cases h : n ≤ X <;> simp [h]

#print axioms endpointDiff_ramp
#print axioms endpointDiff_weighted_ramps
#print axioms endpointDiff_weighted_terms

end RampEndpoint
