import MultivarIndepFormalize.Definitions

/-!
# Basic algebraic inequality

**Proposition 3.7** `prop:basic-ineq` (`basic_ineq`)

`(dx+1)^{d+1} (dy+1)^{d+1} ≤ ((d+1)dxy + (d+1)(x+y) + 1)^{2d}`
with equality iff `x = y = 0`.
-/

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open Real

noncomputable section

/--
**Proposition 3.7** `prop:basic-ineq`

Let `d ≥ 1` and `x, y ≥ 0`. Then
`(dx+1)^{d+1} (dy+1)^{d+1} ≤ ((d+1)dxy + (d+1)(x+y) + 1)^{2d}`.
Equality holds if and only if `x = y = 0`.
-/
lemma basic_ineq (d : ℕ) (hd : d ≥ 1) (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) :
    ((d : ℝ) * x + 1) ^ ((d : ℝ) + 1) * ((d : ℝ) * y + 1) ^ ((d : ℝ) + 1) ≤
    ((d + 1 : ℝ) * d * x * y + (d + 1 : ℝ) * (x + y) + 1) ^ (2 * (d : ℝ)) ∧
    (((d : ℝ) * x + 1) ^ ((d : ℝ) + 1) * ((d : ℝ) * y + 1) ^ ((d : ℝ) + 1) =
    ((d + 1 : ℝ) * d * x * y + (d + 1 : ℝ) * (x + y) + 1) ^ (2 * (d : ℝ)) ↔ x = 0 ∧ y = 0) := by
  constructor;
  · norm_cast ; norm_num [ mul_pow ];
    rw [ ← mul_pow ];
    refine' le_trans ( pow_le_pow_left₀ ( by positivity ) ( show ( ( d : ℝ ) * x + 1 ) * ( ( d : ℝ ) * y + 1 ) ≤ ( ( d + 1 ) * ( d : ℝ ) * x * y + ( d + 1 ) * ( x + y ) + 1 ) by nlinarith [ mul_nonneg hx hy, mul_nonneg hx ( sq_nonneg y ), mul_nonneg hy ( sq_nonneg x ) ] ) _ ) _;
    exact pow_le_pow_right₀ ( by nlinarith [ mul_nonneg hx hy, mul_nonneg ( Nat.cast_nonneg d ) hx, mul_nonneg ( Nat.cast_nonneg d ) hy ] ) ( by linarith );
  · constructor;
    · contrapose!;
      intro hxy
      by_cases hx0 : x = 0;
      · rcases d with ( _ | _ | d ) <;> simp_all +decide;
        · norm_num; nlinarith [ mul_self_pos.2 hxy ];
        · norm_cast;
          refine' ne_of_lt ( lt_of_lt_of_le _ ( pow_le_pow_right₀ ( by nlinarith [ show ( 0 : ℝ ) < y by positivity ] ) ( show 2 * ( d + 1 + 1 ) ≥ d + 1 + 1 + 1 by linarith ) ) );
          gcongr ; norm_num;
      · by_cases hy0 : y = 0 <;> simp_all +decide [Real.rpow_add];
        · norm_cast ; norm_num [ pow_mul' ];
          rw [ ← pow_mul' ];
          refine' ne_of_lt ( lt_of_lt_of_le _ ( pow_le_pow_right₀ ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ) ( show d + 1 ≤ 2 * d by linarith ) ) );
          gcongr ; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show x > 0 by positivity ];
        · have h_simp : ((d * x + 1) * (d * y + 1)) ^ (d + 1 : ℝ) < (((d + 1) * d * x * y + (d + 1) * (x + y) + 1) ^ (2 * d : ℝ)) := by
            field_simp;
            have h_simp : ((d * x + 1) * (d * y + 1)) < ((d + 1) * (d * x * y + (x + y)) + 1) := by
              nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show 0 < x * y by positivity, show 0 < x by positivity, show 0 < y by positivity, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) hx, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) hy ];
            exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) h_simp ( by positivity ) ) ( Real.rpow_le_rpow_of_exponent_le ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_nonneg hx hy ] ) ( by norm_cast; linarith ) );
          rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; exact ne_of_lt h_simp;
    · aesop

end
