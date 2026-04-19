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
        exact R_k_monotonicity 1 (by linarith) s hs hks;
      · exact le_trans ( by simpa using R_k_monotonicity ( d + 2 ) ( by linarith ) s hs ( by aesop ) ) ih
  have hΔs : Δ = 1 → s < 2 := by intro hΔ₁; exact hks ( le_antisymm (le_of_le_of_eq hd_le hΔ₁) hd )
  refine' ⟨ mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ) <| by positivity, Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ⟩;
  iterate 2 exact le_of_lt (helper_R_k_pos Δ _ s hs hΔs)


-- Part C: Lemma 3.3 Symmetric Case
noncomputable section AristotleLemmas

lemma s_properties (d : ℕ) (hd : 1 ≤ d) (η : ℝ) (hη : 0 ≤ η) :
    let s := (H_k d η) ^ (1 / (d : ℝ))
    1 ≤ s ∧ (d = 1 → s < 2) := by
      constructor;
      · have h_H_ge_one : 1 ≤ H_k d η := by
          exact le_trans ( by norm_num [ H_k_eq ] ) ( H_k_strictMonoOn d hd |> StrictMonoOn.le_iff_le |> fun h => h ( show 0 ∈ Set.Ici 0 by norm_num ) ( show η ∈ Set.Ici 0 by assumption ) |>.2 hη );
        exact Real.one_le_rpow h_H_ge_one ( by positivity );
      · intro hd_eq_one;
        subst hd_eq_one;
        unfold H_k;
        unfold A_d B_d; norm_num; rw [ div_lt_iff₀ ] <;> nlinarith;

lemma tangent_plane_coeffs_identity (Δ : ℕ) (hΔ : Δ ≥ 2) (s : ℝ) (hs : 1 ≤ s) :
    let α := x_k Δ (by linarith) s hs (by intro h; linarith)
    let k := Δ + 1
    let a₁_calc := (R_k Δ (by linarith) s hs (by intro h; linarith)) ^ (Δ : ℝ)
    let a₀_calc := a₁_calc * s ^ (Δ : ℝ)
    let a₁_deriv := (A_d k α α) ^ (1 / (k : ℝ) - 1) * ((k - 1) * α + 1)
    let a₀_deriv := (A_d k α α) ^ (1 / (k : ℝ)) - 2 * a₁_deriv * α
    a₁_calc = a₁_deriv ∧ a₀_calc = a₀_deriv := by
      field_simp;
      constructor;
      · unfold R_k A_d B_d; norm_num ; ring;
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by nlinarith [ show ( 0 :ℝ ) ≤ x_k Δ ( by linarith ) s hs ( by aesop ) by exact ( x_k_spec Δ ( by linarith ) s hs ( by aesop ) ) |>.1 ] ) ] ; norm_num [ show ( Δ :ℝ ) ≠ 0 by positivity ] ; ring;
        rw [ Real.rpow_neg ( by nlinarith [ show ( 0 : ℝ ) ≤ x_k Δ ( by linarith ) s hs ( by intros; linarith ) by exact ( x_k_spec Δ ( by linarith ) s hs ( by intros; linarith ) ) |>.1 ] ) ] ; rw [ inv_pow ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by nlinarith [ show ( 0 : ℝ ) ≤ x_k Δ ( by linarith ) s hs ( by intros; linarith ) by exact ( x_k_spec Δ ( by linarith ) s hs ( by intros; linarith ) ) |>.1 ] ) ] ; ring;
      · -- Substitute the expression for R_k Δ into the left-hand side.
        have h_lhs : (R_k Δ (by linarith) s hs (by intro h; linarith)) ^ (Δ : ℝ) * s ^ (Δ : ℝ) = (A_d Δ (x_k Δ (by linarith) s hs (by intro h; linarith)) (x_k Δ (by linarith) s hs (by intro h; linarith))) ^ (1 : ℝ) / (A_d (Δ + 1) (x_k Δ (by linarith) s hs (by intro h; linarith)) (x_k Δ (by linarith) s hs (by intro h; linarith))) ^ (Δ / (Δ + 1) : ℝ) := by
          unfold R_k;
          rw [ Real.div_rpow, ← Real.rpow_mul ];
          · rw [ ← Real.rpow_mul ( by exact le_of_lt ( by exact helper_A_k_plus_1_pos _ _ ( by linarith ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intro h; linarith ) ] ) ) ) ] ; ring_nf ; norm_num [ show Δ ≠ 0 by linarith ];
            rw [ show A_d Δ ( x_k Δ ( by linarith ) s hs ( by intro h; linarith ) ) ( x_k Δ ( by linarith ) s hs ( by intro h; linarith ) ) = s ^ Δ * B_d Δ ( x_k Δ ( by linarith ) s hs ( by intro h; linarith ) ) by
                  have := helper_Hk_eq_sk Δ ( by linarith ) s hs ( by intros; linarith );
                  rw [ ← this, H_k ];
                  rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intros; linarith ) ] ) ) zero_lt_one ) ) ] ] ; ring;
          · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec _ ( by linarith ) _ hs _ |>.1 ) ) zero_le_one;
          · exact Real.rpow_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intro; linarith ) ] ) ) zero_le_one ) _;
          · apply_rules [ Real.rpow_nonneg ];
            unfold A_d;
            field_simp;
            exact add_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec _ ( by linarith ) _ hs ( by intro; linarith ) |>.1 ) ) ( add_nonneg ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ( x_k_spec _ ( by linarith ) _ hs ( by intro; linarith ) |>.1 ) ) ( by norm_num ) ) ) zero_le_one;
        rw [ h_lhs ];
        rw [ div_eq_iff ];
        · norm_num [ sub_div, ne_of_gt ( by positivity : 0 < ( Δ : ℝ ) + 1 ) ];
          rw [ neg_div, Real.rpow_neg ( by exact le_of_lt ( by exact helper_A_k_plus_1_pos _ _ ( by linarith ) ( by exact ( x_k_spec _ ( by linarith ) _ ( by linarith ) ( by intro h; linarith ) ) |>.1 ) ) ) ];
          rw [ inv_mul_eq_div, div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div', div_mul_cancel₀ ];
          · rw [ ← Real.rpow_add' ] <;> norm_num;
            · field_simp;
              rw [ show ( 1 + ( Δ : ℝ ) ) / ( Δ + 1 ) = 1 by rw [ div_eq_iff ] <;> linarith ] ; norm_num [ A_d ] ; ring;
            · exact le_of_lt ( helper_A_k_plus_1_pos _ _ ( by linarith ) ( by exact ( x_k_spec _ ( by linarith ) _ ( by linarith ) ( by intro h; linarith ) ) |>.1 ) );
            · positivity;
          · refine' ne_of_gt ( Real.rpow_pos_of_pos _ _ );
            exact helper_A_k_plus_1_pos _ _ ( by linarith ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intro h; linarith ) ] );
          · refine' ne_of_gt ( Real.rpow_pos_of_pos _ _ );
            exact helper_A_k_plus_1_pos _ _ ( by linarith ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intro h; linarith ) ] );
        · refine' ne_of_gt ( Real.rpow_pos_of_pos _ _ );
          exact helper_A_k_plus_1_pos _ _ ( by linarith ) ( by linarith [ x_k_spec Δ ( by linarith ) s hs ( by intro h; linarith ) ] )

lemma Ad_partial_derivs_inequality (k : ℕ) (hk : 2 ≤ k) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let A := A_d k x y
    let Ax := k * ((k - 1) * y + 1)
    let Ay := k * ((k - 1) * x + 1)
    2 * Ax * Ay ≥ (k : ℝ)^2 * A := by
      -- By expanding both sides and comparing coefficients, we can see that the inequality holds for all non-negative x and y when k ≥ 2.
      have h_expand : ∀ k : ℕ, 2 ≤ k → ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 2 * (k * ((k - 1) * y + 1)) * (k * ((k - 1) * x + 1)) ≥ k^2 * (k * (k - 1) * x * y + k * x + k * y + 1) := by
        intro k hk x y hx hy;
        rcases k with ( _ | _ | k ) <;> norm_num at *;
        field_simp;
        nlinarith [ sq_nonneg ( x - y ), mul_nonneg hx hy, mul_nonneg hx ( sq_nonneg ( k : ℝ ) ), mul_nonneg hy ( sq_nonneg ( k : ℝ ) ) ];
      convert h_expand k hk x y hx hy using 1;
      unfold A_d; ring;

lemma quadratic_concavity_condition (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (_hα : 0 ≤ α) (u v : ℝ) (t : ℝ) (_ht : 0 ≤ t) (h_pos : 0 ≤ α + t * u ∧ 0 ≤ α + t * v) :
    let x := α + t * u
    let y := α + t * v
    let A := A_d k x y
    let Ax := k * ((k - 1) * y + 1)
    let Ay := k * ((k - 1) * x + 1)
    let Axy := k * (k - 1)
    let A_val := A
    let A_prime := Ax * u + Ay * v
    let A_double_prime := 2 * Axy * u * v
    k * A_val * A_double_prime ≤ (k - 1) * (A_prime) ^ 2 := by
      -- Cancel k-1 (since k ≥ 2):
      suffices h_cancel : 2 * k^2 * A_d k (α + t * u) (α + t * v) * u * v ≤ (k * ((k - 1) * (α + t * v) + 1) * u + k * ((k - 1) * (α + t * u) + 1) * v)^2 by
        cases k <;> norm_num [ Nat.succ_mul ] at * ; nlinarith;
      -- Case 2: uv < 0.
      by_cases huv_neg : u * v < 0;
      · norm_num [ A_d ];
        nlinarith [ show 0 < ( k : ℝ ) ^ 2 * ( k * ( k - 1 ) * ( α + t * u ) * ( α + t * v ) + k * ( α + t * u + ( α + t * v ) ) + 1 ) by exact mul_pos ( by positivity ) ( by nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, mul_nonneg ( show ( k : ℝ ) ≥ 0 by positivity ) ( show ( k - 1 : ℝ ) ≥ 0 by exact sub_nonneg_of_le ( by norm_cast; linarith ) ), mul_nonneg h_pos.1 h_pos.2 ] ) ];
      · -- Since $uv \geq 0$, we can apply the inequality $k^2 A \leq 2 Ax Ay$ from `Ad_partial_derivs_inequality`.
        have h_ineq : k^2 * A_d k (α + t * u) (α + t * v) ≤ 2 * (k * ((k - 1) * (α + t * v) + 1)) * (k * ((k - 1) * (α + t * u) + 1)) := by
          exact Ad_partial_derivs_inequality k hk ( α + t * u ) ( α + t * v ) h_pos.1 h_pos.2;
        nlinarith [ sq_nonneg ( ( k : ℝ ) * ( ( k - 1 ) * ( α + t * v ) + 1 ) * u - ( k : ℝ ) * ( ( k - 1 ) * ( α + t * u ) + 1 ) * v ) ]

lemma Ad_composition_concavity_ineq (k : ℕ) (hk : 2 ≤ k) (x y u v : ℝ) (t : ℝ) (_ht : 0 ≤ t) (h_pos : 0 ≤ x + t * u ∧ 0 ≤ y + t * v) :
    let g := A_d k (x + t * u) (y + t * v)
    let g' := k * ((k - 1) * (y + t * v) + 1) * u + k * ((k - 1) * (x + t * u) + 1) * v
    let g'' := 2 * k * (k - 1) * u * v
    k * g * g'' ≤ (k - 1) * g' ^ 2 := by
      unfold A_d;
      by_cases huv : u * v ≥ 0;
      · -- By the properties of the quadratic function, we know that $k^2 A \leq 2 A_x A_y$.
        have h_quad : k^2 * ((k * (k - 1) * (x + t * u) * (y + t * v) + k * (x + t * u + y + t * v) + 1)) ≤ 2 * (k * ((k - 1) * (y + t * v) + 1)) * (k * ((k - 1) * (x + t * u) + 1)) := by
          convert Ad_partial_derivs_inequality k hk ( x + t * u ) ( y + t * v ) h_pos.1 h_pos.2 using 1 ; ring;
          unfold A_d; ring;
        nlinarith [ sq_nonneg ( ( k : ℝ ) * ( ( k - 1 ) * ( y + t * v ) + 1 ) * u - ( k : ℝ ) * ( ( k - 1 ) * ( x + t * u ) + 1 ) * v ), show ( k : ℝ ) ≥ 2 by norm_cast ];
      · refine' le_trans ( mul_nonpos_of_nonneg_of_nonpos _ _ ) _;
        · exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by norm_num; linarith ) ) h_pos.1 ) h_pos.2 ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg h_pos.1 h_pos.2 ) ) ) zero_le_one );
        · nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, mul_le_mul_of_nonneg_left ( show ( k : ℝ ) ≥ 2 by norm_cast ) ( show ( 0 : ℝ ) ≤ k by positivity ) ];
        · exact mul_nonneg ( sub_nonneg.2 <| Nat.one_le_cast.2 <| by linarith ) <| sq_nonneg _

lemma concave_1d_of_hessian_condition (k : ℕ) (hk : 2 ≤ k) (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ x + u) (hv : 0 ≤ y + v) :
    let f := fun t => (A_d k (x + t * u) (y + t * v)) ^ (1 / (k : ℝ))
    ConcaveOn ℝ (Set.Icc 0 1) f := by
      apply_rules [ concaveOn_of_deriv2_nonpos ];
      · exact convex_Icc _ _;
      · refine' ContinuousOn.rpow_const _ _;
        · exact Continuous.continuousOn ( by unfold A_d; continuity );
        · exact fun t ht => Or.inr <| by positivity;
      · refine' DifferentiableOn.rpow ( Differentiable.differentiableOn _ ) ( differentiableOn_const _ ) _ <;> norm_num [ A_d ];
        exact fun t ht₁ ht₂ => by exact ne_of_gt <| add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| by nlinarith ) <| by nlinarith ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| by nlinarith ) zero_lt_one;
      · refine' DifferentiableOn.congr _ _;
        use fun t => ( 1 / ( k : ℝ ) ) * ( A_d k ( x + t * u ) ( y + t * v ) ) ^ ( 1 / ( k : ℝ ) - 1 ) * ( k * ( ( k - 1 ) * ( y + t * v ) + 1 ) * u + k * ( ( k - 1 ) * ( x + t * u ) + 1 ) * v );
        · unfold A_d;
          apply_rules [ DifferentiableOn.mul, DifferentiableOn.rpow ] <;> norm_num;
          · fun_prop;
          · exact fun t ht₁ ht₂ => by exact ne_of_gt <| add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| by nlinarith ) <| by nlinarith ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| by nlinarith ) zero_lt_one;
          · fun_prop;
        · intro t ht; rw [ deriv_rpow_const ] <;> norm_num [ A_d ] ; ring;
          exact Or.inl <| ne_of_gt <| add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| by nlinarith [ Set.mem_Icc.mp <| interior_subset ht ] ) <| by nlinarith [ Set.mem_Icc.mp <| interior_subset ht ] ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| by nlinarith [ Set.mem_Icc.mp <| interior_subset ht ] ) zero_lt_one;
      · -- Let's calculate the second derivative of $f(t)$.
        have h_second_deriv : ∀ t ∈ Set.Ioo 0 1, deriv^[2] (fun t => (A_d k (x + t * u) (y + t * v)) ^ (1 / (k : ℝ))) t = (1 / (k : ℝ) ^ 2) * (A_d k (x + t * u) (y + t * v)) ^ (1 / (k : ℝ) - 2) * (-(k - 1) * (deriv (fun t => A_d k (x + t * u) (y + t * v)) t) ^ 2 + k * (A_d k (x + t * u) (y + t * v)) * (deriv^[2] (fun t => A_d k (x + t * u) (y + t * v)) t)) := by
          intro t ht;
          convert HasDerivAt.deriv ( _ ) using 1;
          convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
          use fun t => ( 1 / ( k : ℝ ) ) * ( A_d k ( x + t * u ) ( y + t * v ) ) ^ ( ( 1 / ( k : ℝ ) ) - 1 ) * deriv ( fun t => A_d k ( x + t * u ) ( y + t * v ) ) t;
          · convert HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ ) ) ( hasDerivAt_deriv_iff.mpr _ ) using 1 <;> norm_num;
            · rw [ show ( ( k : ℝ ) ⁻¹ - 1 - 1 ) = ( ( k : ℝ ) ⁻¹ - 2 ) by ring, show ( ( k : ℝ ) ⁻¹ - 1 ) = ( ( k : ℝ ) ⁻¹ - 2 ) + 1 by ring ] ; rw [ Real.rpow_add_one ] <;> ring ; norm_num [ show k ≠ 0 by linarith ];
              · simp +decide [ sq, mul_assoc, ne_of_gt ( zero_lt_two.trans_le hk ) ];
              · exact ne_of_gt ( add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( by nlinarith [ ht.1, ht.2 ] ) ) ( by nlinarith [ ht.1, ht.2 ] ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by nlinarith [ ht.1, ht.2 ] ) ) ) zero_lt_one );
            · unfold A_d; norm_num [ mul_assoc, mul_comm u, mul_comm v ] ;
            · unfold A_d;
              exact Or.inl <| by nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, show ( k : ℝ ) * ( k - 1 ) ≥ 0 by nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast ], show ( x + t * u ) * ( y + t * v ) ≥ 0 by exact mul_nonneg ( by nlinarith [ ht.1, ht.2 ] ) ( by nlinarith [ ht.1, ht.2 ] ), show ( x + t * u ) ≥ 0 by nlinarith [ ht.1, ht.2 ], show ( y + t * v ) ≥ 0 by nlinarith [ ht.1, ht.2 ] ] ;
            · unfold A_d; norm_num [ mul_comm u, mul_comm v ] ;
              unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv, mul_comm u, mul_comm v ];
          · filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with t ht;
            rw [ deriv_rpow_const ] <;> norm_num;
            · ring;
            · unfold A_d; norm_num [ mul_comm u, mul_comm v ] ;
            · exact Or.inl <| ne_of_gt <| add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) <| by nlinarith [ ht.1, ht.2 ] ) <| by nlinarith [ ht.1, ht.2 ] ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| by nlinarith [ ht.1, ht.2 ] ) zero_lt_one;
        -- By combining the results from the second derivative formula and the concavity inequality, we conclude that the second derivative is non-positive.
        intros t ht
        have h_nonpos : -(k - 1) * (deriv (fun t => A_d k (x + t * u) (y + t * v)) t) ^ 2 + k * (A_d k (x + t * u) (y + t * v)) * (deriv^[2] (fun t => A_d k (x + t * u) (y + t * v)) t) ≤ 0 := by
          have h_second_deriv_nonpos : ∀ t ∈ Set.Ioo 0 1, let g := fun t => A_d k (x + t * u) (y + t * v); let g' := fun t => deriv g t; let g'' := fun t => deriv^[2] g t; k * g t * g'' t ≤ (k - 1) * (g' t) ^ 2 := by
            intros t ht;
            convert Ad_composition_concavity_ineq k hk x y u v t ht.1.le ( by constructor <;> nlinarith [ ht.1, ht.2 ] ) using 1;
            norm_num [ A_d ];
            unfold deriv ; norm_num [ fderiv_apply_one_eq_deriv ] ; ring;
          linarith [ h_second_deriv_nonpos t <| by simpa using ht ];
        convert mul_nonpos_of_nonneg_of_nonpos ( mul_nonneg ( by positivity : 0 ≤ ( 1 : ℝ ) / k ^ 2 ) ( Real.rpow_nonneg ( show 0 ≤ A_d k ( x + t * u ) ( y + t * v ) from ?_ ) _ ) ) h_nonpos using 1;
        convert h_second_deriv t ( by simpa using ht ) using 1;
        exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( by nlinarith [ Set.mem_Icc.mp ( interior_subset ht ) ] ) ) ( by nlinarith [ Set.mem_Icc.mp ( interior_subset ht ) ] ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by nlinarith [ Set.mem_Icc.mp ( interior_subset ht ) ] ) ) ) zero_le_one

lemma concave_1d_of_hessian_condition_v2 (k : ℕ) (hk : 2 ≤ k) (x y u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ x + u) (hv : 0 ≤ y + v) :
    let f := fun t => (A_d k (x + t * u) (y + t * v)) ^ (1 / (k : ℝ))
    ConcaveOn ℝ (Set.Icc 0 1) f := by
      convert ( concave_1d_of_hessian_condition k hk x y u v hx hy hu hv ) using 1

lemma tangent_plane_inequality (Δ : ℕ) (hΔ : Δ ≥ 2) (α : ℝ) (hα : 0 ≤ α) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let k := Δ + 1
    let a₁ := (A_d k α α) ^ (1 / (k : ℝ) - 1) * ((k - 1) * α + 1)
    let a₀ := (A_d k α α) ^ (1 / (k : ℝ)) - 2 * a₁ * α
    a₀ + a₁ * x + a₁ * y ≥ (A_d k x y) ^ (1 / (k : ℝ)) := by
      set k := Δ + 1
      set a₁ := (A_d k α α) ^ (1 / (k : ℝ) - 1) * ((k - 1) * α + 1)
      set a₀ := (A_d k α α) ^ (1 / (k : ℝ)) - 2 * a₁ * α
      set f := fun t : ℝ => (A_d k (α + t * (x - α)) (α + t * (y - α))) ^ (1 / (k : ℝ));
      -- By concavity, $f(1) \leq f(0) + f'(0)$.
      have h_concave : f 1 ≤ f 0 + deriv f 0 := by
        have h_concave : ConcaveOn ℝ (Set.Icc 0 1) f := by
          apply_rules [ concave_1d_of_hessian_condition_v2 ];
          · grind;
          · linarith;
          · linarith;
        have h_concave : ∀ t ∈ Set.Ioo 0 1, (f t - f 0) / t ≥ f 1 - f 0 := by
          intros t ht
          have h_slope : (f t - f 0) / t ≥ (f 1 - f 0) / 1 := by
            have := h_concave.2;
            have := @this 0 ( by norm_num ) 1 ( by norm_num ) ( 1 - t ) t ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ; norm_num at *;
            rw [ div_add', le_div_iff₀ ] <;> nlinarith;
          aesop;
        have h_deriv : Filter.Tendsto (fun t => (f t - f 0) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (deriv f 0)) := by
          have h_deriv : HasDerivAt f (deriv f 0) 0 := by
            simp +zetaDelta at *;
            apply_rules [ DifferentiableAt.rpow, DifferentiableAt.add, DifferentiableAt.mul, differentiableAt_id, differentiableAt_const ];
            unfold A_d; norm_num; positivity;
          simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
        exact le_of_not_gt fun h => absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv <| Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ by norm_num, by norm_num ⟩ ) fun t ht => h_concave t ht ) ( by linarith );
      convert h_concave.ge using 1 ; ring!;
      · rw [ deriv_rpow_const ] <;> norm_num ; ring!;
        · unfold A_d; norm_num [ mul_comm α, mul_comm x, mul_comm y ] ; ring;
          -- Combine like terms and simplify the expression.
          field_simp
          ring;
        · unfold A_d; norm_num;
        · exact Or.inl <| ne_of_gt <| by unfold A_d; norm_num; positivity;
      · aesop

lemma tangent_plane_in_Sd (Δ : ℕ) (hΔ : Δ ≥ 2) (s : ℝ) (hs : 1 ≤ s) :
    let _α := x_k Δ (by linarith) s hs (by intro h; linarith)
    let a₁ := (R_k Δ (by linarith) s hs (by intro h; linarith)) ^ (Δ : ℝ)
    let a₀ := a₁ * s ^ (Δ : ℝ)
    (a₀, a₁, a₁) ∈ S_d Δ := by
      unfold S_d;
      norm_num at *;
      refine' ⟨ _, _, _ ⟩;
      · exact mul_pos ( pow_pos ( by exact helper_R_k_pos _ ( by linarith ) _ hs ( by intro h; linarith ) ) _ ) ( pow_pos ( by linarith ) _ );
      · exact pow_pos ( helper_R_k_pos _ ( by linarith ) _ hs ( by intros; linarith ) ) _;
      · -- Apply the tangent plane inequality to conclude the proof.
        have := tangent_plane_inequality Δ hΔ (x_k Δ (by linarith) s hs (by intro h; linarith)) (by
        exact x_k_spec _ _ _ _ _ |>.1);
        have := tangent_plane_coeffs_identity Δ hΔ s hs; aesop;

lemma Sd_upper_set (d : ℕ) (v w : ℝ × ℝ × ℝ) (hv : v ∈ S_d d) (h : w.1 ≥ v.1 ∧ w.2.1 ≥ v.2.1 ∧ w.2.2 ≥ v.2.2) : w ∈ S_d d := by
  obtain ⟨hv₁, hv₂, hv, hv⟩ := hv;
  exact ⟨ by linarith, by linarith, by linarith, fun x y hx hy => by have := hv x y hx hy; nlinarith ⟩

lemma eta_eq_xk (d : ℕ) (hd : 1 ≤ d) (η : ℝ) (hη : 0 ≤ η) :
    let s := (H_k d η) ^ (1 / (d : ℝ))
    have hs : 1 ≤ s ∧ (d = 1 → s < 2) := s_properties d hd η hη
    η = x_k d hd s hs.1 hs.2 := by
      convert Classical.not_not.1 ( show ¬ ( η ≠ x_k d hd _ _ _ ) from ?_ ) using 1;
      intro h;
      exact h <| ExistsUnique.unique ( exists_unique_x_k d hd _ ( s_properties d hd η hη |>.1 ) ( s_properties d hd η hη |>.2 ) ) ( by
        grind ) ( by
        exact x_k_spec d hd _ _ _ )

lemma symmetric_weights_eq (Δ d : ℕ) (_hΔ : Δ ≥ 2) (hd : 1 ≤ d) (_hd_le : d ≤ Δ)
    (η : ℝ) (hη : 0 ≤ η) :
    let s := (H_k d η) ^ (1 / (d : ℝ))
    let p := (Δ : ℝ) / (d : ℝ)
    let q := (Δ : ℝ) / ((d : ℝ) + 1)
    let Ad := A_d d η η
    let Bd := B_d d η
    let Ad_next := A_d (d + 1) η η
    let W₁ := Bd ^ p / Ad_next ^ q
    let W₀ := Ad ^ p / Ad_next ^ q
    have hs : 1 ≤ s ∧ (d = 1 → s < 2) := s_properties d hd η hη
    let R := R_k d hd s hs.1 hs.2
    W₁ = R ^ (Δ : ℝ) ∧ W₀ = W₁ * s ^ (Δ : ℝ) := by
      constructor;
      · unfold R_k
        generalize_proofs at *;
        rw [ ← eta_eq_xk d hd η hη ];
        rw [ Real.div_rpow ( by exact Real.rpow_nonneg ( by exact le_of_lt ( by exact helper_B_k_pos d η hd hη ) ) _ ) ( by exact Real.rpow_nonneg ( by exact le_of_lt ( by exact helper_A_k_plus_1_pos d η hd hη ) ) _ ), ← Real.rpow_mul ( by exact le_of_lt ( by exact helper_B_k_pos d η hd hη ) ), ← Real.rpow_mul ( by exact le_of_lt ( by exact helper_A_k_plus_1_pos d η hd hη ) ) ] ; ring;
      · unfold H_k;
        rw [ Real.div_rpow ];
        · rw [ Real.div_rpow ( by exact Real.rpow_nonneg ( by exact le_of_lt ( show 0 < A_d d η η from by
                                                                                unfold A_d;
                                                                                field_simp;
                                                                                exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ) ) zero_lt_one ) ) _ ) ( by exact Real.rpow_nonneg ( by exact le_of_lt ( show 0 < B_d d η from by
                                                                                                                                                                            exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_lt_one ) ) _ ) ];
          rw [ ← Real.rpow_mul, ← Real.rpow_mul ] <;> ring;
          · rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( show 0 < B_d d η from by unfold B_d; positivity ) _ ) ) ];
          · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_le_one;
          · unfold A_d;
            bound;
        · exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hd ) ) ) hη ) hη ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg hη hη ) ) ) zero_le_one;
        · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_le_one

end AristotleLemmas

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
  obtain ⟨W₁, W₀, hW⟩ : ∃ W₁ W₀ : ℝ, (W₀, W₁, W₁) = (A_d d η η ^ (Δ / (d : ℝ)) / A_d (d + 1) η η ^ (Δ / ((d : ℝ) + 1)), B_d d η ^ (Δ / (d : ℝ)) / A_d (d + 1) η η ^ (Δ / ((d : ℝ) + 1)), B_d d η ^ (Δ / (d : ℝ)) / A_d (d + 1) η η ^ (Δ / ((d : ℝ) + 1))) ∧ W₀ ≥ (R_k Δ (by linarith) ((H_k d η) ^ (1 / (d : ℝ))) (s_properties d hd η hη).1 (by intro h; linarith)) ^ (Δ : ℝ) * ((H_k d η) ^ (1 / (d : ℝ))) ^ (Δ : ℝ) ∧ W₁ ≥ (R_k Δ (by linarith) ((H_k d η) ^ (1 / (d : ℝ))) (s_properties d hd η hη).1 (by intro h; linarith)) ^ (Δ : ℝ) := by
    convert symmetric_weights_eq Δ d hΔ hd hd_le η hη using 1;
    constructor <;> intro h;
    · convert symmetric_weights_eq Δ d hΔ hd hd_le η hη using 1;
    · unfold A_d B_d at *;
      convert degree_d_plane_dominance Δ d hΔ hd hd_le ( H_k d η ^ ( 1 / ( d : ℝ ) ) ) ( s_properties d hd η hη |>.1 ) ( s_properties d hd η hη |>.2 ) using 1;
      grind;
  convert Sd_upper_set Δ _ _ ( tangent_plane_in_Sd Δ hΔ ( ( H_k d η ) ^ ( 1 / ( d : ℝ ) ) ) ( s_properties d hd η hη |>.1 ) ) _ using 1;
  grind
