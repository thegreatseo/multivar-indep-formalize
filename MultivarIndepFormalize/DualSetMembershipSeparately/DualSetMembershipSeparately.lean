-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison
import MultivarIndepFormalize.DualSetMembershipSeparately.DualSetMembershipSymmetric

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Real (exp log sqrt)

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/--
The multivariate weight triple (w₀, w₁, w₂).
Matches Equation (3.9) on page 9 of the paper.
-/
def weight_triple (Δ d : ℕ) (η μ : ℝ) : ℝ × ℝ × ℝ :=
  let p : ℝ := (Δ : ℝ) / (d : ℝ)
  let q : ℝ := (Δ : ℝ) / ((d : ℝ) + 1)
  let Ad := A_d d η μ
  let Bdμ := B_d d μ
  let Bdη := B_d d η
  let Ad_next := A_d (d + 1) η μ
  (Ad ^ p / Ad_next ^ q, Bdμ ^ p / Ad_next ^ q, Bdη ^ p / Ad_next ^ q)

/--
The derivative of the difference f(t) = w₀(t) - (w₁(t) + w₂(t))/Δ.
Matches the logic on page 10.
-/
lemma deriv_weight_difference (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (K : ℝ) (hK : K > 0) (D : ℝ) (hD : D > 0) (t : ℝ) :
    let p := (Δ : ℝ) / (d : ℝ)
    let B := K * exp t
    let C := K * exp (-t)
    let A := ((d - 1) * K ^ 2 + B + C - 1) / d
    let f := λ u =>
      let Bu := K * exp u
      let Cu := K * exp (-u)
      let Au := ((d - 1) * K ^ 2 + Bu + Cu - 1) / d
      (Au ^ p - (Bu ^ p + Cu ^ p) / Δ) * D ^ (-(Δ : ℝ) / (d + 1))
    HasDerivAt f ((d : ℝ)⁻¹ * (p * (B - C) * A ^ (p - 1) - (B ^ p - C ^ p)) * D ^ (- (Δ : ℝ) / (d + 1))) t := by
  /-
  PROOF STRATEGY:
  1. Use 'HasDerivAt' rules for exponentials and powers.
  2. Differentiate A(t) with respect to t: dA/dt = (B - C) / d. [cite: 202, 650]
  3. Differentiate (B^p + C^p) with respect to t: d(B^p + C^p)/dt = p(B^p - C^p). [cite: 202, 650]
  4. Combine using the Chain Rule to obtain the target derivative expression. [cite: 203, 652]
  -/
  refine HasDerivAt.mul_const ?_ (D ^ (- (Δ : ℝ) / (d + 1)))
  sorry

/--
The derivative f'(t) is non-negative for t ≥ 0, since A ≥ B ≥ C.
Matches the logic on page 10.
-/
lemma weight_difference_nonnegative (p : ℝ) (hp : p ≥ 1) (A B C : ℝ) (hABC : A ≥ B ∧ B ≥ C ∧ C > 0) :
    p * (B - C) * A ^ (p - 1) ≥ B ^ p - C ^ p := by
  /-
  PROOF STRATEGY:
  1. Express the difference B^p - C^p as the integral of p * ζ^(p-1) from C to B.
  2. Since A ≥ B, then for all ζ ∈ [C, B], we have A ≥ ζ.
  3. Because p ≥ 1, the function ζ^(p-1) is non-decreasing, so A^(p-1) ≥ ζ^(p-1).
  4. Therefore, (B - C) * p * A^(p-1) ≥ ∫_C^B p * ζ^(p-1) dζ = B^p - C^p.
  -/
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc C B, B^p - C^p = p * c^(p-1) * (B - C) := by
    by_cases hB : B = C;
    · aesop;
    · have := exists_deriv_eq_slope ( f := fun x => x ^ p ) ( show B > C from lt_of_le_of_ne hABC.2.1 ( Ne.symm hB ) );
      exact this ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( by exact fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ hx.1, hx.2 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, Set.Ioo_subset_Icc_self hc₁, by rw [ eq_div_iff ( sub_ne_zero_of_ne hB ) ] at hc₂; norm_num [ show c ≠ 0 by linarith [ hc₁.1, hc₁.2 ] ] at hc₂ ⊢; linarith ⟩;
  nlinarith [ show 0 ≤ p * ( B - C ) by exact mul_nonneg ( by positivity ) ( by linarith ), show c ^ ( p - 1 ) ≤ A ^ ( p - 1 ) by exact Real.rpow_le_rpow ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] ) ( by linarith ) ]

/--
Converts the geometric mean B-value K back to the fugacity parameter η.
Based on B_d(η) = dη + 1. Matches page 10 logic.
-/
def K_to_η (d : ℕ) (K : ℝ) : ℝ :=
  (K - 1) / (d : ℝ)

lemma B_d_K_to_η (d : ℕ) (hd : 1 ≤ d) (K : ℝ) :
    B_d d (K_to_η d K) = K := by
  unfold B_d K_to_η
  field_simp
  ring

lemma A_d_K_to_η (d : ℕ) (hd : 1 ≤ d) (K : ℝ) :
    A_d d (K_to_η d K) (K_to_η d K) = ((d - 1) * K ^ 2 + 2 * K - 1) / d := by
  unfold A_d K_to_η
  field_simp
  ring

lemma weight_diff_inequalities (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hdΔ : d ≤ Δ)
    (K : ℝ) (hK : K > 0) (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.log K)) :
    let p := (Δ : ℝ) / (d : ℝ)
    let B := K * Real.exp t
    let C := K * Real.exp (-t)
    let A := ((d - 1) * K ^ 2 + B + C - 1) / d
    p ≥ 1 ∧ A ≥ B ∧ B ≥ C ∧ C ≥ 1 := by
      refine' ⟨ _, _, _, _ ⟩ <;> norm_num;
      · rw [ le_div_iff₀ ] <;> norm_cast ; linarith;
      · rw [ Real.exp_neg ];
        have := Real.exp_le_exp.mpr ht.2;
        field_simp;
        rw [ Real.exp_log hK ] at this;
        nlinarith [ mul_le_mul_of_nonneg_left this hK.le, Real.exp_pos t, Real.add_one_le_exp t, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) hK.le, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) ( Real.exp_nonneg t ) ];
      · exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by linarith [ ht.1, ht.2 ] ) ) hK.le;
      · rw [ ← Real.exp_log hK ];
        rw [ ← Real.exp_add ] ; exact Real.one_le_exp ( by linarith [ ht.1, ht.2 ] )

/--
Lemma 3.3 Reduction: The function f(t) = w₀ - (w₁ + w₂)/Δ is non-decreasing for t ≥ 0.
Matches the derivative analysis on page 10[cite: 203, 652].
-/
lemma weight_diff_monotone (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hdΔ : d ≤ Δ) (K D : ℝ) (hK : K > 0) (hD : D > 0) :
    let p := (Δ : ℝ) / (d : ℝ)
    let f := λ t =>
      let B := K * exp t
      let C := K * exp (-t)
      let A := ((d - 1) * K ^ 2 + B + C - 1) / d
      (A ^ p - (B ^ p + C ^ p) / Δ) * D ^ (-Δ / (d + 1 : ℝ))
    MonotoneOn f (Set.Icc 0 (log K)) := by
  /-
  PROOF STRATEGY:
  1. Calculate the derivative f'(t) as shown in 'deriv_weight_difference'. [cite: 203, 652]
  2. Use the fact that A ≥ B ≥ C for t ≥ 0 to show the derivative is non-negative. [cite: 204, 654]
  3. The core inequality p(B-C)A^{p-1} ≥ B^p - C^p follows from the Mean Value Theorem
     applied to ζ^p on the interval [C, B]. [cite: 204, 654]
  4. Conclude that f(t) ≥ f(0) for all t ≥ 0.
  -/
  apply_rules [ monotoneOn_of_deriv_nonneg ];
  · exact convex_Icc _ _;
  · refine' ContinuousOn.mul _ _;
    · refine' ContinuousOn.sub _ _;
      · exact ContinuousOn.rpow ( ContinuousOn.div_const ( Continuous.continuousOn ( by continuity ) ) _ ) continuousOn_const ( by intro t ht; exact Or.inr <| by positivity );
      · exact ContinuousOn.div_const ( ContinuousOn.add ( ContinuousOn.rpow ( continuousOn_const.mul ( Real.continuousOn_exp ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by positivity ) ( ContinuousOn.rpow ( continuousOn_const.mul ( Real.continuous_exp.comp_continuousOn <| continuousOn_id.neg ) ) continuousOn_const <| by intro t ht; exact Or.inr <| by positivity ) ) _;
    · exact continuousOn_const;
  · refine' DifferentiableOn.mul _ _;
    · refine' DifferentiableOn.sub _ _;
      · refine' DifferentiableOn.rpow_const _ _;
        · fun_prop (disch := norm_num);
        · exact fun x hx => Or.inr ( by rw [ le_div_iff₀ ] <;> norm_cast ; linarith );
      · exact DifferentiableOn.div_const ( DifferentiableOn.add ( DifferentiableOn.rpow ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.differentiableOn ) ) ( differentiableOn_const _ ) ( by intro t ht; exact ne_of_gt ( mul_pos hK ( Real.exp_pos _ ) ) ) ) ( DifferentiableOn.rpow ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.comp_differentiableOn ( differentiableOn_id.neg ) ) ) ( differentiableOn_const _ ) ( by intro t ht; exact ne_of_gt ( mul_pos hK ( Real.exp_pos _ ) ) ) ) ) _;
    · exact differentiableOn_const _;
  · intro t ht;
    convert HasDerivAt.deriv ( deriv_weight_difference Δ d hΔ hd K hK D hD t ) |> fun h => h.symm ▸ mul_nonneg ?_ ?_ using 1;
    · refine' mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) _;
      have := weight_diff_inequalities Δ d hΔ hd hdΔ K hK t ( interior_subset ht );
      convert sub_nonneg_of_le ( weight_difference_nonnegative _ this.1 _ _ _ _ ) using 1;
      grind;
    · positivity


/-
Algebraic identity relating A_{d+1} to the product of B_d's.
-/
lemma Ad_plus_one_eq_of_prod_Bd (d : ℕ) (hd : 1 ≤ d) (η μ : ℝ) :
  A_d (d + 1) η μ = ((d + 1 : ℝ) / d) * (B_d d η * B_d d μ - 1) + 1 := by
    unfold A_d B_d; ring;
    simpa [ sq, pow_three, mul_assoc, ne_of_gt ( zero_lt_one.trans_le hd ) ] using by ring;

/-
The weight difference function is even.
-/
def weight_diff_fun (Δ d : ℕ) (K D : ℝ) (t : ℝ) : ℝ :=
  let p := (Δ : ℝ) / (d : ℝ)
  let B := K * Real.exp t
  let C := K * Real.exp (-t)
  let A := ((d - 1) * K ^ 2 + B + C - 1) / d
  (A ^ p - (B ^ p + C ^ p) / Δ) * D ^ (-(Δ : ℝ) / (d + 1))

lemma weight_diff_fun_even (Δ d : ℕ) (K D : ℝ) (t : ℝ) :
  weight_diff_fun Δ d K D t = weight_diff_fun Δ d K D (-t) := by
    unfold weight_diff_fun; ring;

/-
Inequalities for A, B, C in the weight difference function.
-/
lemma weight_diff_fun_aux_ineqs (d : ℕ) (hd : 1 ≤ d) (K : ℝ) (t : ℝ)
    (ht_nonneg : 0 ≤ t) (hC : K * Real.exp (-t) ≥ 1) :
    let B := K * Real.exp t
    let C := K * Real.exp (-t)
    let A := ((d - 1) * K ^ 2 + B + C - 1) / d
    1 ≤ C ∧ C ≤ B ∧ B ≤ A := by
      -- By combining the inequalities from the provided solution �,� we can conclude that the weight difference function is even.
      apply And.intro hC (And.intro (by
      exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by linarith ) ) ( by nlinarith [ Real.exp_pos ( -t ) ] )) (by
      rw [ le_div_iff₀ ( by positivity ) ];
      -- Since $K \geq 1$ and $e^t \leq K$, we have $K e^t \leq K^2$.
      have h_Ket_le_K2 : K * Real.exp t ≤ K ^ 2 := by
        rw [ Real.exp_neg ] at hC;
        nlinarith [ inv_pos.mpr ( Real.exp_pos t ), mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t ];
      nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, Real.exp_pos t, Real.exp_pos ( -t ), mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) ( Real.exp_nonneg t ), mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) ( Real.exp_nonneg ( -t ) ) ]))

/-
The derivative factor of the weight difference function is non-negative.
-/
lemma weight_diff_deriv_factor_nonneg (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (K : ℝ) (hK : K ≥ 1) (t : ℝ) (ht : 0 ≤ t) (hC : K * Real.exp (-t) ≥ 1) :
    let p := (Δ : ℝ) / (d : ℝ)
    let B := K * Real.exp t
    let C := K * Real.exp (-t)
    let A := ((d - 1) * K ^ 2 + B + C - 1) / d
    p * (B - C) * A ^ (p - 1) - (B ^ p - C ^ p) ≥ 0 := by
      -- Apply the weight_difference_nonnegative lemma with p = Δ/d, A ≥ B ≥ C, and B ≥ C > 0.
      have := weight_difference_nonnegative ((Δ : ℝ) / (d : ℝ)) (by
      exact one_le_div ( by positivity ) |>.2 ( mod_cast hd_le )) (((d - 1) * K ^ 2 + K * Real.exp t + K * Real.exp (-t) - 1) / d) (K * Real.exp t) (K * Real.exp (-t));
      convert sub_nonneg_of_le ( this ⟨ _, _, _ ⟩ ) using 1;
      · exact weight_diff_fun_aux_ineqs d hd K t ht hC |>.2.2;
      · gcongr ; linarith;
      · positivity

/-
The weight difference function is minimized at t=0.
-/
lemma weight_diff_fun_min (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (K D : ℝ) (hK : K ≥ 1) (hD : D > 0) (t : ℝ) (ht : K * Real.exp (-|t|) ≥ 1) :
    weight_diff_fun Δ d K D t ≥ weight_diff_fun Δ d K D 0 := by
      -- By the properties of the weight difference function, we know that its derivative is non-negative for $t \geq 0$.
      have h_deriv_nonneg : ∀ t : ℝ, 0 ≤ t → K * Real.exp (-t) ≥ 1 → deriv (weight_diff_fun Δ d K D) t ≥ 0 := by
        intros t ht_nonneg ht_ineq
        have h_deriv : deriv (weight_diff_fun Δ d K D) t = (d : ℝ)⁻¹ * (let p := (Δ : ℝ) / (d : ℝ)
          let B := K * Real.exp t
          let C := K * Real.exp (-t)
          let A := ((d - 1) * K ^ 2 + B + C - 1) / d
          (p * (B - C) * A ^ (p - 1) - (B ^ p - C ^ p)) * D ^ (- (Δ : ℝ) / (d + 1))) := by
            convert HasDerivAt.deriv ( deriv_weight_difference Δ d hΔ hd K ( by positivity ) D ( by positivity ) t ) using 1;
            ring;
        rw [h_deriv];
        apply_rules [ mul_nonneg, inv_nonneg.mpr, Real.rpow_nonneg ] <;> norm_num;
        · have := weight_diff_deriv_factor_nonneg Δ d hΔ hd hd_le K hK t ht_nonneg ht_ineq;
          linarith;
        · positivity;
      -- Apply the mean value theorem to the interval $[0, |t|]$.
      have h_mvt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → K * Real.exp (-b) ≥ 1 → weight_diff_fun Δ d K D b ≥ weight_diff_fun Δ d K D a := by
        intros a b ha hb hbK;
        by_contra h_contra;
        have := exists_deriv_eq_slope ( weight_diff_fun Δ d K D ) ( show a < b from lt_of_le_of_ne hb ( by aesop_cat ) );
        apply_mod_cast absurd ( this _ _ ) _;
        · refine' ContinuousOn.mul _ _;
          · refine' ContinuousOn.sub _ _;
            · exact ContinuousOn.rpow ( ContinuousOn.div_const ( Continuous.continuousOn ( by continuity ) ) _ ) continuousOn_const ( by intro x hx; exact Or.inr <| by positivity );
            · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.add ( ContinuousAt.rpow ( continuousAt_const.mul ( Real.continuous_exp.continuousAt ) ) continuousAt_const <| Or.inr <| by positivity ) ( ContinuousAt.rpow ( continuousAt_const.mul ( Real.continuous_exp.continuousAt.comp <| ContinuousAt.neg continuousAt_id ) ) continuousAt_const <| Or.inr <| by positivity ) ) continuousAt_const <| by positivity;
          · exact continuousOn_const;
        · apply_rules [ DifferentiableOn.sub, DifferentiableOn.mul, DifferentiableOn.rpow, differentiableOn_id, differentiableOn_const ];
          · exact DifferentiableOn.add ( DifferentiableOn.add ( differentiableOn_const _ ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.differentiableOn ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.comp_differentiableOn ( differentiableOn_id.neg ) ) );
          · intro x hx; exact ne_of_gt ( div_pos ( by nlinarith [ Real.add_one_le_exp x, Real.add_one_le_exp ( -x ), show ( d : ℝ ) ≥ 1 by norm_cast ] ) ( by positivity ) ) ;
          · exact DifferentiableOn.add ( DifferentiableOn.rpow ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.differentiableOn ) ) ( differentiableOn_const _ ) ( by intro x hx; positivity ) ) ( DifferentiableOn.rpow ( DifferentiableOn.mul ( differentiableOn_const _ ) ( Real.differentiable_exp.comp_differentiableOn ( differentiableOn_id.neg ) ) ) ( differentiableOn_const _ ) ( by intro x hx; positivity ) );
          · exact fun x hx => ne_of_gt hD;
        · exact fun ⟨ c, hc₁, hc₂ ⟩ => by have := h_deriv_nonneg c ( by linarith [ hc₁.1 ] ) ( by exact le_trans hbK ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by linarith [ hc₁.2 ] ) ) ( by linarith ) ) ) ; rw [ eq_div_iff ] at hc₂ <;> nlinarith [ hc₁.1, hc₁.2 ] ;
      convert h_mvt le_rfl ( show 0 ≤ |t| by positivity ) ht |> le_trans <| _ using 1;
      cases abs_cases t <;> simp +decide [ * ];
      exact le_of_eq ( by rw [ ← weight_diff_fun_even ] )

/-
Algebraic identity expressing A_d in terms of B_d.
-/
lemma A_d_eq_of_Bd (d : ℕ) (hd : d ≠ 0) (η μ : ℝ) :
  A_d d η μ = ((d - 1) * (B_d d η * B_d d μ) + B_d d η + B_d d μ - 1) / d := by
    unfold A_d B_d; ring;
    -- Combine like terms and simplify the expression.
    field_simp
    ring

/-
The weight difference expression equals the weight difference function.
-/
lemma weight_triple_diff_eq_fun (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := Real.sqrt s
    let t := (1 / 2) * Real.log (B_d d μ / B_d d η)
    let D := A_d (d + 1) η μ
    let w := weight_triple Δ d η μ
    w.1 - (w.2.1 + w.2.2) / Δ = weight_diff_fun Δ d K D t := by
      unfold weight_triple weight_diff_fun B_d A_d; ring;
      rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos ];
      · rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos ];
        · rw [ Real.rpow_def_of_pos ] <;> norm_num;
          · rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( by positivity ) ] ; ring;
            norm_num [ ← Real.exp_add, ← Real.exp_neg, ← Real.exp_nat_mul ] ; ring;
            rw [ show ( d : ℝ ) * μ * ( 1 + d * η ) ⁻¹ + ( 1 + d * η ) ⁻¹ = ( 1 + d * μ ) / ( 1 + d * η ) by ring ] ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring;
            rw [ show ( 1 + ( d : ℝ ) * η + ( d : ℝ ) * μ + ( d : ℝ ) ^ 2 * η * μ ) = ( 1 + ( d : ℝ ) * η ) * ( 1 + ( d : ℝ ) * μ ) by ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring;
            norm_num [ ← Real.exp_add, ← Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hd ) ] ; ring;
            rw [ Real.exp_add, Real.exp_log ( by positivity ), Real.exp_log ( by positivity ) ] ; ring;
            grind;
          · field_simp;
            nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show ( Real.sqrt ( 1 + d * η + d * μ + d ^ 2 * η * μ ) ) ≥ 1 by exact Real.le_sqrt_of_sq_le ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_nonneg hη hμ ] ), Real.exp_pos ( Real.log ( ( d * μ + 1 ) / ( 1 + d * η ) ) / 2 ), Real.exp_pos ( - ( Real.log ( ( d * μ + 1 ) / ( 1 + d * η ) ) / 2 ) ), Real.add_one_le_exp ( Real.log ( ( d * μ + 1 ) / ( 1 + d * η ) ) / 2 ), Real.add_one_le_exp ( - ( Real.log ( ( d * μ + 1 ) / ( 1 + d * η ) ) / 2 ) ) ];
        · positivity;
        · norm_num ; nlinarith [ mul_nonneg hη hμ, mul_nonneg hη ( Nat.cast_nonneg d ), mul_nonneg hμ ( Nat.cast_nonneg d ) ];
        · positivity;
      · positivity;
      · positivity;
      · norm_num ; nlinarith [ mul_nonneg hη hμ, mul_nonneg hη ( Nat.cast_nonneg d ), mul_nonneg hμ ( Nat.cast_nonneg d ) ];
      · nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show ( d : ℝ ) * η ≥ 0 by positivity, show ( d : ℝ ) * μ ≥ 0 by positivity, show ( d : ℝ ) ^ 2 * η * μ ≥ 0 by positivity ]

/-
The symmetric weight difference equals the weight difference function at t=0.
-/
lemma symmetric_weight_diff_eq_fun_zero (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := Real.sqrt s
    let η_sym := K_to_η d K
    let D := A_d (d + 1) η μ
    let w_sym := weight_triple Δ d η_sym η_sym
    w_sym.1 - (w_sym.2.1 + w_sym.2.2) / Δ = weight_diff_fun Δ d K D 0 := by
      unfold weight_triple weight_diff_fun K_to_η B_d A_d; ring;
      field_simp;
      rw [ Real.rpow_neg_eq_inv_rpow ] ; norm_num ; ring;
      field_simp;
      rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring;
      rw [ ← Real.sqrt_eq_rpow ] ; rw [ Real.sq_sqrt <| by positivity ] ; ring;
      rw [ Real.inv_rpow ( by positivity ) ] ; ring;
      norm_num [ sq, pow_three, mul_assoc, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hd ) ] ; ring

/-
The condition K * exp(-|t|) >= 1 holds for the parameters derived from η and μ.
-/
lemma K_exp_neg_abs_t_ge_one (d : ℕ) (hd : 1 ≤ d) (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := Real.sqrt s
    let t := (1 / 2) * Real.log (B_d d μ / B_d d η)
    K * Real.exp (-|t|) ≥ 1 := by
      cases abs_cases ( 1 / 2 * Real.log ( B_d d μ / B_d d η ) ) <;> simp_all +decide [ Real.exp_neg ];
      · rw [ abs_of_nonneg ‹_› ];
        field_simp;
        rw [ Real.sqrt_eq_rpow, Real.le_rpow_iff_log_le ] <;> norm_num;
        · rw [ Real.log_div, Real.log_mul ] <;> ring <;> norm_num [ B_d ];
          · exact Real.log_nonneg ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] );
          · positivity;
          · positivity;
          · positivity;
          · positivity;
        · positivity;
        · exact mul_pos ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_lt_one ) ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hμ ) zero_lt_one );
      · rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ] <;> norm_num at *;
        · rw [ ← Real.exp_add, Real.log_mul ] <;> norm_num;
          · rw [ Real.log_div ] <;> norm_num;
            · linarith [ Real.log_nonneg ( show 1 ≤ B_d d μ from by unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ), Real.log_nonneg ( show 1 ≤ B_d d η from by unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ) ];
            · unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ;
            · exact ne_of_gt ( by unfold B_d; positivity );
          · exact ne_of_gt ( by unfold B_d; positivity );
          · unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ;
        · exact mul_pos ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_lt_one ) ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hμ ) zero_lt_one )

/--
The multivariate weight triple is bounded below by the symmetric case
due to the monotonicity of the dual gap. Matches page 10.
-/
lemma dual_gap_minimized_at_symmetry (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := Real.sqrt s
    let w₀ := (weight_triple Δ d η μ).1
    let w₁ := (weight_triple Δ d η μ).2.1
    let w₂ := (weight_triple Δ d η μ).2.2
    let w₀_sym := (weight_triple Δ d (K_to_η d K) (K_to_η d K)).1
    let w₁_sym := (weight_triple Δ d (K_to_η d K) (K_to_η d K)).2.1
    w₀ - (w₁ + w₂) / Δ ≥ w₀_sym - (2 * w₁_sym) / Δ := by
  simp only [weight_triple_diff_eq_fun Δ d hΔ hd η μ hη hμ]
  #check symmetric_weight_diff_eq_fun_zero Δ d hΔ hd (K_to_η d √(B_d d η * B_d d μ)) (K_to_η d √(B_d d η * B_d d μ))
  -- Use weight_triple_diff_eq_fun Δ d hΔ hd η μ hη hμ and symmetric_weight_diff_eq_fun_zero
  -- Conclude using weight_diff_fun_min
  sorry



/--
The gap w₀ - Φ_Δ(w₁, w₂) is bounded below by the symmetric gap.
Matches page 10.
-/
lemma multivariate_reduction_to_symmetric (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let w := weight_triple Δ d η μ
    let K := (B_d d η * B_d d μ).sqrt
    let w_sym := weight_triple Δ d (K_to_η d K) (K_to_η d K)
    w.1 - Φ_Δ Δ w.2.1 w.2.2 ≥ w_sym.1 - Φ_Δ Δ w_sym.2.1 w_sym.2.2 := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. GEOMETRIC MEAN INVARIANT:
     - Let B := B_d d μ and C := B_d d η. Fix the product BC = K²[cite: 198, 647].
     - Note that w.2.1 * w.2.2 depends only on K, so the product of the weights
       is invariant under the transformation Keᵗ and Ke⁻ᵗ.

  2. GAP ANALYSIS VIA DERIVATIVES:
     - Define the gap function f(t) = w₀ - (w₁ + w₂)/Δ as in 'deriv_weight_difference'.
     - Invoke 'weight_diff_monotone' to establish that f(t) is non-decreasing
       for t ≥ 0[cite: 203, 652].
     - Since the multivariate state corresponds to some t ≥ 0 and symmetry to t = 0,
       conclude that the gap is minimized at symmetry: f(t) ≥ f(0)[cite: 205, 655].

  3. BOUNDARY REDUCTION VIA LEMMA 3.5:
     - Use 'Phi_upper_bound' (Lemma 3.5) to bound the dual function Φ_Δ:
       Φ_Δ Δ w.2.1 w.2.2 ≤ Ψ_Δ Δ (w.2.1 * w.2.2) + (w.2.1 + w.2.2) / Δ[cite: 196, 645].
     - This implies the inequality:
       w.1 - Φ_Δ Δ w.2.1 w.2.2 ≥ w.1 - (w.2.1 + w.2.2) / Δ - Ψ_Δ Δ (w.2.1 * w.2.2)[cite: 205, 656].

  4. SYMMETRIC MATCHING:
     - Invoke 'dual_gap_minimized_at_symmetry' to show the RHS is exactly
       minimized when B = C, which is achieved by (K_to_η d K)[cite: 199, 648].
     - Use the 'moreover' equality case of Lemma 3.5 for a₁ = a₂ to show that
       at symmetry, Φ_Δ Δ w_sym.1 w_sym.2 matches the bound exactly[cite: 184, 616].

  5. FINAL COMPARISON:
     - Combine the functional minimum from Step 2 with the boundary equality
       from Step 4 to close the goal[cite: 206, 658].
  -/
  sorry

/--
**Lemma 3.3** `lem:Sn-membership-separately`
"Something separated" is in S_Δ.

**Statement**
Let \(\Delta\ge2\) and \(1\le d\le \Delta\) be integers. Let \(\lambda,\mu\ge0\). Then
\[
  \biggl(
  \frac{A_{d}(\lambda,\mu)^{\frac{\Delta}{d}}}{A_{d+1}(\lambda,\mu)^{\frac{\Delta}{d+1}}},\,
  \frac{B_{d}(\mu)^{\frac{\Delta}{d}}}{A_{d+1}(\lambda,\mu)^{\frac{\Delta}{d+1}}},\,
  \frac{B_{d}(\lambda)^{\frac{\Delta}{d}}}{A_{d+1}(\lambda,\mu)^{\frac{\Delta}{d+1}}}
  \biggr) \in \calS_\Delta.
\]
-/
lemma SΔ_membership_separately (Δ : ℕ) (hΔ : Δ ≥ 2) (d : ℕ) (hd : 1 ≤ d) (hdΔ : d ≤ Δ)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let Ad := A_d d η μ
    let Bdμ := B_d d μ
    let Bdη := B_d d η
    let Ad_next := A_d (d + 1) η μ
    let p : ℝ := (Δ : ℝ) / (d : ℝ)
    let q : ℝ := (Δ : ℝ) / ((d : ℝ) + 1)
    (Ad ^ p / Ad_next ^ q, Bdμ ^ p / Ad_next ^ q, Bdη ^ p / Ad_next ^ q) ∈ S_d Δ := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. BOUNDARY CASE:
     - Check if η = 0 and μ = 0.
     - If so, the triple becomes (1, 1, 1). Prove this is in S_Δ by showing
       (1+x+y)^(Δ+1) ≥ A_{Δ+1}(x,y) for all x,y ≥ 0. [cite: 193, 194]

  2. DEFINE THE INVARIANT PRODUCT:
     - For η, μ > 0, let B := B_d d μ and C := B_d d η.
     - Let K := sqrt (B * C). This K represents the symmetric state where η = μ
       while maintaining the same product of weights (w₁ * w₂). [cite: 198, 206]

  3. INVOKE MULTIVARIATE REDUCTION:
     - Apply 'multivariate_reduction_to_symmetric' to the weight triple w.
     - This uses 'dual_gap_minimized_at_symmetry' and the derivative analysis of f(t)
       to show that the gap w₀ - Φ_Δ(w₁, w₂) is minimized at the symmetric point
       defined by K_to_η d K. [cite: 196, 205]

  4. SYMMETRIC MEMBERSHIP:
     - Let η_sym := K_to_η d K. Apply 'SΔ_membership_symmetric' to prove the
       resulting symmetric weight triple w_sym is in S_Δ. [cite: 207, 1039]
     - This implies the symmetric gap is non-negative: w_sym.0 ≥ Φ_Δ Δ w_sym.1 w_sym.1.

  5. CONCLUSION OF MEMBERSHIP:
     - Combine the reduction result (Step 3) with the symmetric membership (Step 4).
     - Since the multivariate gap dominates the symmetric gap, and the symmetric
       gap is non-negative, conclude that w₀ ≥ Φ_Δ Δ w₁.1 w₁.2. [cite: 207, 1040]
     - This confirms (w₀, w₁, w₂) ∈ S_Δ by the variational definition of the dual set.
  -/
  sorry
