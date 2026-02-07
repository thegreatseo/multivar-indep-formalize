-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison
import MultivarIndepFormalize.DualSetMembershipSeparately.xkDerivative
import MultivarIndepFormalize.DualSetMembershipSeparately.RkMonotone

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

/--
The relationship between the base weight w₀ and the slope weight w₁
in terms of the invariant ratio s. Matches page 11.
-/
lemma weight_ratio_relation (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    let x := x_k k hk s hs hks
    let w₁ := (B_d k x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))
    let w₀ := (A_d k x x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))
    w₀ = w₁ * s := by
  /-
  PROOF STRATEGY:
  1. Use x_k_spec to get (H_k k x)^(1/k) = s.
  2. Substitute H_k k x = A_d k x x / B_d k x.
  3. Simplify the power (A_d / B_d)^(1/k) = s to A_d^(1/k) = s * B_d^(1/k).
  4. Divide both sides by A_{k+1}^{1/(k+1)} to match the definitions of w₀ and w₁.
  -/
  have h_xk : (A_d k (x_k k hk s hs hks) (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) = s * (B_d k (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) := by
    -- Substitute x_k into H_k and use the definition of H_k to relate A_d and B_d.
    have h_Hk : (A_d k (x_k k hk s hs hks) (x_k k hk s hs hks)) / (B_d k (x_k k hk s hs hks)) = s ^ k := by
      convert congr_arg ( · ^ k ) ( x_k_spec k hk s hs hks |>.2 ) using 1 ; norm_num [ H_k ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( div_nonneg ( ?_ ) ( ?_ ) ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ];
      · unfold A_d;
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show 0 ≤ ( k : ℝ ) * x_k k hk s hs hks by exact mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec k hk s hs hks |>.1 ), show 0 ≤ ( ( k : ℝ ) - 1 ) * x_k k hk s hs hks by exact mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ( x_k_spec k hk s hs hks |>.1 ) ];
      · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec k hk s hs hks |>.1 ) ) zero_le_one;
    rw [ div_eq_iff ] at h_Hk;
    · rw [ h_Hk, Real.mul_rpow ( by positivity ) ( by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ x_k k hk s hs hks by exact x_k_spec k hk s hs hks |>.1 ) ) zero_le_one ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ];
    · intro h; rw [ h ] at h_Hk; norm_num at h_Hk; linarith [ pow_pos ( zero_lt_one.trans_le hs ) k ] ;
  grind

/--
The degree d plane dominates the tangent plane at α.
Matches page 10.
-/
lemma degree_d_plane_dominance (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (s : ℝ) (hs : 1 ≤ s) (hks : d = 1 → s < 2) :
    let w₁ := (R_k d hd s hs hks) ^ (Δ : ℝ)
    let w₀ := w₁ * s ^ (Δ : ℝ)
    let a₁ := (R_k Δ (by linarith) s hs (by intro h; linarith)) ^ (Δ : ℝ)
    let a₀ := a₁ * s ^ (Δ : ℝ)
    w₀ ≥ a₀ ∧ w₁ ≥ a₁ := by
  /-
  PROOF STRATEGY:
  1. Apply R_k_monotonicity repeatedly to show R_Δ(s) ≤ R_d(s).
  2. Since x^Δ is increasing for x ≥ 0, R_Δ(s)^Δ ≤ R_d(s)^Δ, which gives w₁ ≥ a₁.
  3. Since s ≥ 1, multiplying both sides by s^Δ gives w₁ * s^Δ ≥ a₁ * s^Δ, so w₀ ≥ a₀.
  -/
  have h_Rk_monotonic : R_k d hd s hs hks ≥ R_k Δ (by linarith) s hs (by
  aesop_cat) := by
    all_goals generalize_proofs at *;
    -- By induction on $Δ - d$, we can show that $R_k d hd s hs hks ≥ R_k Δ (by linarith) s hs (by sorry)$.
    induction' hd_le with d hd ih;
    · rfl;
    · rcases d with ( _ | _ | d ) <;> simp_all +decide;
      · interval_cases d ; norm_num at *;
        exact?;
      · exact le_trans ( by simpa using R_k_monotonicity ( d + 2 ) ( by linarith ) s hs ( by aesop ) ) ih
  have hΔs : Δ = 1 → s < 2 := by intro hΔ₁; exact hks ( le_antisymm (le_of_le_of_eq hd_le hΔ₁) hd )
  refine' ⟨ mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ) <| by positivity, Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ⟩;
  iterate 2 exact le_of_lt (helper_R_k_pos Δ _ s hs hΔs)


-- Part C: Lemma 3.3 Symmetric Case
/--
Lemma 3.3 in the case where η = μ (symmetric case).
Matches the goal on page 10: (A_d^p / A_{d+1}^q, B_d^p / A_{d+1}^q, B_d^p / A_{d+1}^q) ∈ S_Δ.
-/
lemma SΔ_membership_symmetric (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (η : ℝ) (hη : η ≥ 0) :
    let p := (Δ : ℝ) / (d : ℝ)
    let q := (Δ : ℝ) / ((d : ℝ) + 1)
    let Ad := A_d d η η
    let Bd := B_d d η
    let Ad_next := A_d (d + 1) η η
    (Ad ^ p / Ad_next ^ q, Bd ^ p / Ad_next ^ q, Bd ^ p / Ad_next ^ q) ∈ S_d Δ := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. RATIO INITIALIZATION:
     - Define s := (H_k d η) ^ (1 / d).
     - Show s ≥ 1 using 'H_k_strictMonoOn' and the base case H_k(0) = 1.
     - For the special case d = 1, prove s < 2 using 'H_1_tendsto'.

  2. WEIGHT REPRESENTATION (Applying weight_ratio_relation):
     - Let x_d := x_k d hd s hs hks.
     - By 'weight_ratio_relation', show that the weight triple (w₀, w₁, w₁)
       satisfies: w₀ = w₁ * s^Δ.
     - Express w₁ explicitly as (R_k d hd s hs hks)^Δ.

  3. LOCAL PLANE DOMINANCE (Applying degree_d_plane_dominance):
     - Let a₁ := (R_k Δ (by linarith) s hs (by aesop))^Δ and a₀ := a₁ * s^Δ.
     - Apply 'degree_d_plane_dominance' to show that our weights satisfy:
       w₀ ≥ a₀ and w₁ ≥ a₁.
     - This effectively moves the problem from the degree d triple to the
       degree Δ triple (the tangent plane).

  4. BOUNDARY MEMBERSHIP AND UPPER SET:
     - Identify (a₀, a₁, a₁) as the tangent plane to z = A_{Δ+1}^{1/(Δ+1)}
       at the point (α, α), where α := x_k Δ ...
     - Use 'boundary_membership' (Lemma 3.1) to confirm (a₀, a₁, a₁) ∈ S_d Δ.
     - Invoke the 'upper_set' property of S_d Δ: since (w₀, w₁, w₁) is
       pointwise greater than a membership triple, it is also in S_d Δ.
  -/
  sorry
