import MultivarIndepFormalize.Definitions

/-!
# Basic properties of A_d and B_d

Algebraic identities and positivity lemmas for the functions `A_d` and `B_d`
defined in `Definitions.lean`.
-/

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open Real

noncomputable section

/-! ## A_d / B_d identities -/

lemma A_d_zero_left (d : ℕ) (μ : ℝ) : A_d d 0 μ = B_d d μ := by unfold A_d B_d; ring

lemma A_d_zero_right (d : ℕ) (η : ℝ) : A_d d η 0 = B_d d η := by unfold A_d B_d; ring

lemma A_d_pos (d : ℕ) (η μ : ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) : 0 < A_d (d + 1) η μ := by
  unfold A_d
  have hd : (d : ℝ) ≥ 0 := Nat.cast_nonneg d
  rw [show (↑(d + 1) : ℝ) = (d : ℝ) + 1 from by push_cast; ring]
  nlinarith [mul_nonneg hη hμ, mul_nonneg hd hη, mul_nonneg hd hμ,
             mul_nonneg hd (mul_nonneg hη hμ)]

lemma B_d_pos (d : ℕ) (η : ℝ) (hη : 0 ≤ η) : 0 < B_d (d + 1) η := by
  unfold B_d; positivity

end
