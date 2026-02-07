-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison
import MultivarIndepFormalize.DualSetMembershipSeparately.xkDerivative

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The derivative of log R_k(s) with respect to s for s > 1.
Matches equation (3.15) on page 11 of the paper:
∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)).
-/

/-
Algebraic expansion of A_d k x x.
-/
lemma helper_A_k_eq (k : ℕ) (x : ℝ) : A_d k x x = k * (k - 1) * x ^ 2 + 2 * k * x + 1 := by
  unfold A_d; ring;

/-
Algebraic expansion of B_d k x.
-/
lemma helper_B_k_eq (k : ℕ) (x : ℝ) : B_d k x = k * x + 1 := by
  rfl

/-
Algebraic identities relating A_{k+1}, A_k, and B_k.
-/
lemma helper_Ak_plus_1_eq_Ak_plus_2xBk (k : ℕ) (x : ℝ) :
    A_d (k + 1) x x = A_d k x x + 2 * x * B_d k x := by
      unfold A_d B_d; ring;
      push_cast; ring;

lemma helper_Ak_plus_1_sub_2Bk_sq (k : ℕ) (x : ℝ) :
    A_d (k + 1) x x - 2 * (B_d k x) ^ 2 = -(A_d k x x - 2 * x) := by
      unfold A_d B_d; ring;
      push_cast; ring

/-
Derivatives of A_{k+1}(x,x) and B_k(x).
-/
lemma helper_A_k_plus_1_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => A_d (k + 1) t t) (2 * (k + 1) * B_d k x) x := by
      convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
      exact fun t => ( k + 1 ) * ( k + 1 - 1 ) * t ^ 2 + ( k + 1 ) * ( t + t ) + 1;
      · convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.const_mul _ ( hasDerivAt_pow 2 x ) ) ( HasDerivAt.const_mul _ ( HasDerivAt.add ( hasDerivAt_id x ) ( hasDerivAt_id x ) ) ) ) ( hasDerivAt_const _ _ ) using 1 ; norm_num [ B_d ] ; ring;
      · filter_upwards [ ] with t using by unfold A_d; norm_num ; ring;

lemma helper_B_k_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => B_d k t) k x := by
      convert HasDerivAt.add ( HasDerivAt.const_mul ( k : ℝ ) ( hasDerivAt_id x ) ) ( hasDerivAt_const _ _ ) using 1 ; norm_num [ B_d ]

/-
Positivity of B_k and A_{k+1} for non-negative x.
-/
lemma helper_B_k_pos (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) : 0 < B_d k x := by
  exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one

lemma helper_A_k_plus_1_pos (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) : 0 < A_d (k + 1) x x := by
  unfold A_d;
  norm_num ; positivity

/-
Derivative of log R_k(x) with respect to x.
-/
lemma helper_deriv_log_Rk_x (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t => Real.log ((B_d k t) ^ (1 / (k : ℝ)) / (A_d (k + 1) t t) ^ (1 / ((k : ℝ) + 1))))
      (-(A_d k x x - 2 * x) / (B_d k x * A_d (k + 1) x x)) x := by
        convert HasDerivAt.log ( HasDerivAt.div ( HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ ) _ ) _ using 1 <;> norm_num [ B_d, A_d ];
        field_simp;
        any_goals first | positivity | norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        · unfold B_d; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring;
          rw [ show ( - ( ( k : ℝ ) * ( 1 + k : ℝ ) ⁻¹ ) ) = ( 1 + k : ℝ ) ⁻¹ - 1 by linarith [ inv_mul_cancel₀ ( by positivity : ( 1 + k : ℝ ) ≠ 0 ) ] ] ; rw [ Real.rpow_sub_one ( by positivity ) ] ; ring;
          field_simp;
          rw [ show ( - ( k : ℝ ) + 1 ) / k = 1 / k - 1 by rw [ div_sub_one ] ; ring ; positivity ] ; rw [ Real.rpow_sub_one ( by positivity ) ] ; ring;
          field_simp
          ring;
        · exact DifferentiableAt.add ( differentiableAt_id.const_mul _ ) ( differentiableAt_const _ );
        · exact Or.inl ( by positivity );
        · exact Or.inl ( by positivity );
        · exact ⟨ by positivity, by positivity ⟩

/-
Algebraic identities for the final simplification of the derivative.
-/
lemma helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk (k : ℕ) (x s : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) (hH : H_k k x = s ^ k) :
    A_d (k + 1) x x = (s ^ k + 2 * x) * B_d k x := by
      -- Substitute hH into the equation to get A_d k x x = s^k * B_d k x.
      have h_sub : A_d k x x = s ^ k * B_d k x := by
        rw [ ← hH, H_k ];
        rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) ) ];
      convert helper_Ak_plus_1_eq_Ak_plus_2xBk k x using 1 ; rw [ h_sub ] ; ring

lemma helper_Ak_minus_x_eq (k : ℕ) (x : ℝ) :
    A_d k x x - x = ((k - 1) * x + 1) * B_d k x := by
      unfold A_d B_d; ring;

lemma helper_identity_for_log_deriv (k : ℕ) (x s : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) (hH : H_k k x = s ^ k) :
    (A_d k x x - 2 * x) / B_d k x = 2 * (k - 1) * x + 2 - s ^ k := by
      -- Substitute hH into the expression for A_d k x x.
      have hA : A_d k x x = s^k * B_d k x := by
        rw [ ← hH, H_k ];
        rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) ) ];
      rw [ div_eq_iff ] <;> cases k <;> norm_num [ B_d, A_d ] at * <;> nlinarith

/-
The denominator term in the derivative of x_k is positive.
-/
lemma helper_denom_pos (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (x : ℝ) (hx : 0 ≤ x)
    (hH : H_k k x = s ^ k) (hks : k = 1 → s < 2) :
    2 * (k - 1) * x + 2 - s ^ k > 0 := by
      rcases k with ( _ | _ | k ) <;> norm_num at *;
      · linarith;
      · unfold H_k at hH;
        rw [ div_eq_iff ] at hH <;> norm_num [ A_d, B_d ] at *;
        · nlinarith [ sq_nonneg ( x - 1 ), mul_nonneg hx ( Nat.cast_nonneg k ) ];
        · positivity

/-
Algebraic simplification of the product of derivatives.
-/
lemma helper_product_derivs (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (x : ℝ) (hx : 0 ≤ x)
    (hH : H_k k x = s ^ k) (hks : k = 1 → s < 2) :
    let D_x := -(A_d k x x - 2 * x) / (B_d k x * A_d (k + 1) x x)
    let D_s := s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)
    D_x * D_s = -s ^ (k - 1) / (s ^ k + 2 * x) := by
      -- Substitute the expression for $A_{k+1}(x,x)$ from `helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk`.
      have hAkp1 : A_d (k + 1) x x = (s ^ k + 2 * x) * B_d k x := by
        convert helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk k x s hk hx hH using 1;
      -- Substitute the expression for $A_k(x,x) - 2x$ from `helper_identity_for_log_deriv`.
      have hAk_minus_2x : A_d k x x - 2 * x = (2 * (k - 1) * x + 2 - s ^ k) * B_d k x := by
        rw [ ← hH ];
        rw [ show H_k k x = A_d k x x / B_d k x from rfl ];
        rw [ sub_mul, div_mul_cancel₀ ] <;> norm_num [ B_d ];
        · unfold A_d; ring;
        · positivity;
      by_cases h : B_d k x = 0 <;> by_cases h' : 2 * ( ( k : ℝ ) - 1 ) * x + 2 - s ^ k = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · exact absurd h ( ne_of_gt ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) );
      · exact absurd hAkp1 ( ne_of_gt ( helper_A_k_plus_1_pos k x hk hx ) );
      · exact absurd h' ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show s ^ k > 2 * ( k - 1 ) * x + 2 by exact absurd ( helper_denom_pos k hk s hs x hx hH hks ) ( by linarith ) ] );
      · exact Or.inl ( mul_div_cancel₀ _ h' )

/-
Helper lemma: H_k(x_k(s)) = s^k.
-/
lemma helper_Hk_eq_sk (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    H_k k (x_k k hk s hs hks) = s ^ k := by
      have h_exp : (H_k k (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) = s := by
        exact ( Classical.choose_spec ( exists_unique_x_k k hk s hs hks |> ExistsUnique.exists ) ) |>.2;
      convert congr_arg ( · ^ k ) h_exp using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( show 0 ≤ H_k k ( x_k k hk s hs hks ) from _ ), one_div_mul_cancel ( by positivity ), Real.rpow_one ];
      exact div_nonneg ( by rw [ show A_d k ( x_k k hk s hs hks ) ( x_k k hk s hs hks ) = k * ( k - 1 ) * ( x_k k hk s hs hks ) ^ 2 + 2 * k * ( x_k k hk s hs hks ) + 1 by exact? ] ; exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( sq_nonneg _ ) ) ( mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( show 0 ≤ x_k k hk s hs hks from by linarith [ x_k_spec k hk s hs ‹_› ] ) ) ) zero_le_one ) ( by rw [ show B_d k ( x_k k hk s hs hks ) = k * ( x_k k hk s hs hks ) + 1 by exact? ] ; exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ x_k k hk s hs hks from by linarith [ x_k_spec k hk s hs ‹_› ] ) ) zero_le_one )

lemma log_Rk_diff (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let log_Rk_ext : ℝ → ℝ := fun t => if ht: (1 ≤ t) ∧ (k = 1 → t < 2) then
        Real.log (R_k k hk t ht.1 ht.2)
      else
        0
    let x := x_k k hk s hs.le hks
    HasDerivAt log_Rk_ext
      (-s ^ (k - 1) / (s ^ k + 2 * x)) s := by
  /-
  PROOF STRATEGY:
  1. Expand log R_k(s) = (1/k) * log (B_k(x)) - (1/(k+1)) * log (A_{k+1}(x))
     where x = x_k(s)[cite: 986].
  2. Apply the Chain Rule: d/ds [log R_k(s)] = (d/dx [log R_k(x)] * dx/ds)[cite: 987].
  3. Use 'deriv_x_k' for the dx/ds term.
  4. Use the identity A_{k+1}(x) = (s^k + 2x)B_k(x) to simplify the
     d/dx term to (s^k - 2(k-1)x - 2) / ((s^k + 2x) * B_k(x))[cite: 693, 988].
  5. Multiplying the two terms leads to a cancellation of (2(k-1)x + 2 - s^k),
     leaving the target expression -s^(k-1) / (s^k + 2x)[cite: 991, 992].
  -/
  apply_rules [ HasDerivAt.congr_of_eventuallyEq ];
  convert HasDerivAt.comp s ( helper_deriv_log_Rk_x k hk _ _ ) ( deriv_x_k k hk s hs hks ) using 1;
  any_goals tauto;
  · split_ifs <;> simp_all +decide [ ne_of_gt, le_of_lt ];
    convert Eq.symm ( helper_product_derivs k hk s hs ( x_k k hk s hs.le hks ) ( x_k_spec k hk s hs.le hks |>.1 ) ( helper_Hk_eq_sk k hk s hs.le hks ) hks ) using 1;
    ring;
  · split_ifs <;> [ exact x_k_spec _ _ _ _ _ |>.1; exact le_rfl ];
  · filter_upwards [ lt_mem_nhds hs ] with t ht;
    unfold R_k;
    unfold B_d A_d; aesop;

/--
Monotonicity of R_k(s): R_{d+1}(s) ≤ R_d(s) for Δ ≥ d.
Matches the logic leading to equation (3.15) on page 11.
-/
lemma R_k_monotonicity (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (hds : d = 1 → s < 2) :
    R_k (d + 1) (by linarith) s hs (by intro h; linarith) ≤ R_k d hd s hs hds := by
  /-
  PROOF STRATEGY:
  1. Compute R_k(1) = 1 for all k ≥ 1.
  2. Use log_Rk_diff (Part A): ∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)).
  3. Use x_k_comparison (Part B): x_{d+1}(s) ≤ s * x_d(s).
  4. Combine these to show ∂_s log R_{d+1}(s) ≤ ∂_s log R_d(s).
  5. Since R_{d+1}(1) = R_d(1) = 1 (at x=0), integration/monotonicity
     implies R_{d+1}(s) ≤ R_d(s) for all s ≥ 1.
  -/
  sorry
