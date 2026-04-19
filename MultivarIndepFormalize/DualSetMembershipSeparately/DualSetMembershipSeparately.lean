-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison
import MultivarIndepFormalize.DualSetMembershipSeparately.DualSetMembershipSymmetric
import MultivarIndepFormalize.DualSetBoundary

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

noncomputable section AristotleLemmas

/--
The derivative of the difference f(t) = w₀(t) - (w₁(t) + w₂(t))/Δ.
Matches the logic on page 10.
-/
lemma deriv_weight_difference (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
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
  have hp_ge_1 : 1 ≤  (Δ : ℝ) / d := by field_simp; exact Nat.cast_le.mpr hd_le
  field_simp;
  convert HasDerivAt.div_const ( HasDerivAt.mul ( HasDerivAt.sub ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.rpow_const ( HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.const_mul _ ( hasDerivAt_const _ _ ) ) ( Real.hasDerivAt_exp _ ) ) ( HasDerivAt.exp ( hasDerivAt_neg _ ) ) ) ) ( hasDerivAt_const _ _ ) ) _ ) _ ) ) ( HasDerivAt.add ( HasDerivAt.rpow_const ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_exp _ ) ) _ ) ( HasDerivAt.rpow_const ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.exp ( hasDerivAt_neg _ ) ) ) _ ) ) ) ( hasDerivAt_const _ _ ) ) _ using 1 ; norm_num ; ring_nf;
  · field_simp;
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
    norm_num [ Real.rpow_sub hK, Real.rpow_sub ( Real.exp_pos _ ), Real.rpow_sub ( Real.exp_pos _ ) ] ; ring_nf;
    norm_num [ Real.exp_neg, Real.exp_log hK, ne_of_gt ( zero_lt_one.trans_le hd ) ] ; ring_nf;
    norm_num [ mul_assoc, mul_comm K, hK.ne', Real.exp_ne_zero ] ; ring_nf;
    norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.exp_ne_zero ];
  · exact Or.inr hp_ge_1;
  · exact Or.inl <| ne_of_gt <| mul_pos hK <| Real.exp_pos _;
  · exact Or.inr hp_ge_1

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

lemma weight_diff_inequalities (Δ d : ℕ) (_hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
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
lemma weight_diff_monotone (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ) (K D : ℝ) (hK : K > 0) (hD : D > 0) :
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
    convert HasDerivAt.deriv ( deriv_weight_difference Δ d hΔ hd hd_le K hK D hD t ) |> fun h => h.symm ▸ mul_nonneg ?_ ?_ using 1;
    · refine' mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) _;
      have := weight_diff_inequalities Δ d hΔ hd hd_le K hK t ( interior_subset ht );
      convert sub_nonneg_of_le ( weight_difference_nonnegative _ this.1 _ _ _ _ ) using 1;
      grind;
    · positivity


/-
Algebraic identity relating A_{d+1} to the product of B_d's.
-/
lemma Ad_plus_one_eq_of_prod_Bd (d : ℕ) (hd : 1 ≤ d) (η μ : ℝ) :
  A_d (d + 1) η μ = ((d + 1 : ℝ) / d) * (B_d d η * B_d d μ - 1) + 1 := by
    unfold A_d B_d; ring_nf;
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
    unfold weight_diff_fun; ring_nf;

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
lemma weight_diff_deriv_factor_nonneg (Δ d : ℕ) (_hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
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
            convert HasDerivAt.deriv ( deriv_weight_difference Δ d hΔ hd hd_le K ( by positivity ) D ( by positivity ) t ) using 1;
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
    unfold A_d B_d; ring_nf;
    -- Combine like terms and simplify the expression.
    field_simp
    ring

/-
The weight difference expression equals the weight difference function.
-/
lemma weight_triple_diff_eq_fun (Δ d : ℕ) (_hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := Real.sqrt s
    let t := (1 / 2) * Real.log (B_d d μ / B_d d η)
    let D := A_d (d + 1) η μ
    let w := weight_triple Δ d η μ
    w.1 - (w.2.1 + w.2.2) / Δ = weight_diff_fun Δ d K D t := by
      unfold weight_triple weight_diff_fun B_d A_d; ring_nf;
      rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos ];
      · rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos, Real.rpow_def_of_pos ];
        · rw [ Real.rpow_def_of_pos ] <;> norm_num;
          · rw [ Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf;
            norm_num [ ← Real.exp_add, ← Real.exp_neg, ← Real.exp_nat_mul ] ; ring_nf;
            rw [ show ( d : ℝ ) * μ * ( 1 + d * η ) ⁻¹ + ( 1 + d * η ) ⁻¹ = ( 1 + d * μ ) / ( 1 + d * η ) by ring ] ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] ; ring_nf;
            rw [ show ( 1 + ( d : ℝ ) * η + ( d : ℝ ) * μ + ( d : ℝ ) ^ 2 * η * μ ) = ( 1 + ( d : ℝ ) * η ) * ( 1 + ( d : ℝ ) * μ ) by ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf;
            norm_num [ ← Real.exp_add, ← Real.exp_neg, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hd ) ] ; ring_nf;
            rw [ Real.exp_add, Real.exp_log ( by positivity ), Real.exp_log ( by positivity ) ] ; ring_nf;
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
      unfold weight_triple weight_diff_fun K_to_η B_d A_d; ring_nf;
      field_simp;
      rw [ Real.rpow_neg_eq_inv_rpow ] ; norm_num ; ring_nf;
      field_simp;
      rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      rw [ ← Real.sqrt_eq_rpow ] ; rw [ Real.sq_sqrt <| by positivity ] ; ring_nf;
      rw [ Real.inv_rpow ( by positivity ) ] ; ring_nf;
      norm_num [ sq, pow_three, mul_assoc, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hd ) ] ; ring_nf

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
        · rw [ Real.log_div, Real.log_mul ] <;> ring_nf <;> norm_num [ B_d ];
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
  have := @weight_diff_fun_min Δ d hΔ hd hd_le (Real.sqrt (B_d d η * B_d d μ)) (A_d (d + 1) η μ) ?_ ?_ (1 / 2 * Real.log (B_d d μ / B_d d η)) ?_ <;> norm_num at *;
  · convert add_le_add_right this ( 2 * ( weight_triple Δ d ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ).2.1 / ( Δ : ℝ ) ) using 1;
    rw [ show weight_diff_fun Δ d ( Real.sqrt ( B_d d η * B_d d μ ) ) ( A_d ( d + 1 ) η μ ) 0 = ( weight_triple Δ d ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ).1 - ( 2 * ( weight_triple Δ d ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ).2.1 ) / ( Δ : ℝ ) from ?_ ];
    · ring;
    · convert symmetric_weight_diff_eq_fun_zero Δ d hΔ hd η μ hη hμ using 1;
      · exact Eq.symm (symmetric_weight_diff_eq_fun_zero Δ d hΔ hd η μ hη hμ);
      · convert symmetric_weight_diff_eq_fun_zero Δ d hΔ hd η μ hη hμ using 1;
        unfold weight_triple; ring;
    · ring
  · exact one_le_mul_of_one_le_of_one_le ( by unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ) ( by unfold B_d; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] );
  · unfold A_d; ring_nf; norm_num [ hd ];
    nlinarith [ mul_nonneg ( Nat.cast_nonneg d ) hη, mul_nonneg ( Nat.cast_nonneg d ) hμ, mul_nonneg hη hμ ];
  · convert K_exp_neg_abs_t_ge_one d hd η μ hη hμ using 1;
    norm_num [ abs_mul, abs_of_nonneg ]

/-- A_d(d+1) is invariant under K-symmetrization: A_d(d+1, η_sym, η_sym) = A_d(d+1, η, μ)
where η_sym = K_to_η d (sqrt(B_d d η * B_d d μ)). -/
lemma Ad_next_sym_eq (d : ℕ) (hd : 1 ≤ d) (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    A_d (d + 1) (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) = A_d (d + 1) η μ := by
  have h1 := Ad_plus_one_eq_of_prod_Bd d hd (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))
  have h2 := Ad_plus_one_eq_of_prod_Bd d hd η μ
  have h3 := B_d_K_to_η d hd (Real.sqrt (B_d d η * B_d d μ))
  have hBn : B_d d η * B_d d μ ≥ 0 := by
    apply mul_nonneg <;> (unfold B_d; nlinarith [show (d : ℝ) ≥ 1 from Nat.one_le_cast.mpr hd])
  rw [h1, h3, Real.mul_self_sqrt hBn.le, h2]

/-
Weight triple product invariance: w.2.1 * w.2.2 = w_sym.2.1 ^ 2.
-/
lemma weight_prod_sym_eq (Δ d : ℕ) (hd : 1 ≤ d) (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let K := Real.sqrt (B_d d η * B_d d μ)
    let w := weight_triple Δ d η μ
    let w_sym := weight_triple Δ d (K_to_η d K) (K_to_η d K)
    w.2.1 * w.2.2 = w_sym.2.1 ^ 2 := by
  -- By definition of weight_triple, we have:
  unfold weight_triple;
  simp +zetaDelta at *;
  rw [ sq, div_mul_div_comm, div_mul_div_comm ];
  rw [ B_d_K_to_η ];
  · rw [ ← Real.mul_rpow ( Real.sqrt_nonneg _ ) ( Real.sqrt_nonneg _ ), Real.mul_self_sqrt ( mul_nonneg ( show 0 ≤ B_d d η by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_le_one ) ( show 0 ≤ B_d d μ by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hμ ) zero_le_one ) ) ];
    rw [ Ad_next_sym_eq d hd η μ hη hμ, Real.mul_rpow ( by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hη ) zero_le_one ) ( by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) hμ ) zero_le_one ) ] ; ring;
  · linarith

/-
The weight triple components are positive when η, μ ≥ 0.
-/
lemma weight_triple_pos (Δ d : ℕ) (_hΔ : Δ ≥ 2) (hd : 1 ≤ d) (_hd_le : d ≤ Δ)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    (weight_triple Δ d η μ).2.1 > 0 ∧ (weight_triple Δ d η μ).2.2 > 0 := by
  unfold weight_triple;
  unfold A_d B_d;
  simp +zetaDelta at *;
  exact ⟨ by positivity, by positivity ⟩

/-
The weight triple product < 1 when η + μ > 0.
-/
lemma weight_prod_lt_one (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (_hd_le : d ≤ Δ)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) (hpos : η + μ > 0) :
    (weight_triple Δ d η μ).2.1 * (weight_triple Δ d η μ).2.2 < 1 := by
  unfold weight_triple;
  unfold B_d A_d; norm_num;
  field_simp;
  rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
  rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
  refine' lt_of_lt_of_le _ ( Real.rpow_le_rpow_of_exponent_le _ <| show ( Δ : ℝ ) * ( 1 + d : ℝ ) ⁻¹ * 2 ≥ ( Δ : ℝ ) * ( d : ℝ ) ⁻¹ from _ );
  · exact Real.rpow_lt_rpow ( by positivity ) ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_nonneg hη hμ ] ) ( by positivity );
  · nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_nonneg hη hμ ];
  · field_simp;
    norm_cast ; linarith

/-
When η = 0 and μ = 0, K_to_η d K = 0 where K = sqrt(B_d d 0 * B_d d 0).
-/
lemma K_to_η_zero (d : ℕ) (_hd : 1 ≤ d) :
    K_to_η d (Real.sqrt (B_d d 0 * B_d d 0)) = 0 := by
  unfold K_to_η B_d; norm_num;

/-
The gap w₀ - Φ_Δ(w₁, w₂) is bounded below by the symmetric gap.
Matches page 10.
-/
lemma multivariate_reduction_to_symmetric (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let w := weight_triple Δ d η μ
    let K := (B_d d η * B_d d μ).sqrt
    let w_sym := weight_triple Δ d (K_to_η d K) (K_to_η d K)
    w.1 - Φ_Δ Δ w.2.1 w.2.2 ≥ w_sym.1 - Φ_Δ Δ w_sym.2.1 w_sym.2.2 := by
  by_cases h₃ : η + μ > 0 <;> simp_all +decide [weight_triple];
  · -- By definition of $w_sym$, we know that $w_sym.1 = w.1$ and $w_sym.2.1 = w.2.1$.
    have hw_sym : (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.1 * (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.2 = (weight_triple Δ d η μ).2.1 * (weight_triple Δ d η μ).2.2 := by
      convert weight_prod_sym_eq Δ d hd η μ hη hμ |> Eq.symm using 1;
      unfold weight_triple; ring;
    have hw_sym_eq : Φ_Δ Δ (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.1 (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.2 = Psi_Delta Δ hΔ ( (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.1 * (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.2 ) (by
    exact hw_sym.symm ▸ mul_pos ( weight_triple_pos Δ d hΔ hd hd_le η μ hη hμ |>.1 ) ( weight_triple_pos Δ d hΔ hd hd_le η μ hη hμ |>.2 )) (by
    exact hw_sym.symm ▸ weight_prod_lt_one Δ d hΔ hd hd_le η μ hη hμ h₃) + ( (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.1 + (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.2 ) / Δ := by
      apply (Phi_upper_bound Δ hΔ (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.1 (weight_triple Δ d (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ)))).2.2 (by
      exact weight_triple_pos Δ d hΔ hd hd_le _ _ ( by
        exact div_nonneg ( sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by unfold B_d; nlinarith [ mul_nonneg ( Nat.cast_nonneg d ) hη, mul_nonneg ( Nat.cast_nonneg d ) hμ ] ) <| Nat.cast_nonneg _; ) ( by
        exact div_nonneg ( sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by unfold B_d; nlinarith [ mul_nonneg ( Nat.cast_nonneg d ) hη, mul_nonneg ( Nat.cast_nonneg d ) hμ ] ) <| Nat.cast_nonneg _; ) |>.1) (by
      apply (weight_triple_pos Δ d hΔ hd hd_le (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (K_to_η d (Real.sqrt (B_d d η * B_d d μ))) (by
      exact div_nonneg ( sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by unfold B_d; nlinarith [ mul_nonneg ( Nat.cast_nonneg d ) hη, mul_nonneg ( Nat.cast_nonneg d ) hμ ] ) <| Nat.cast_nonneg _;) (by
      exact div_nonneg ( sub_nonneg.2 <| Real.le_sqrt_of_sq_le <| by unfold B_d; nlinarith [ mul_nonneg ( Nat.cast_nonneg d ) hη, mul_nonneg ( Nat.cast_nonneg d ) hμ ] ) <| Nat.cast_nonneg _;)).right) (by
      exact hw_sym.symm ▸ weight_prod_lt_one Δ d hΔ hd hd_le η μ hη hμ h₃)).right
      generalize_proofs at *;
      unfold weight_triple; aesop;
    generalize_proofs at *;
    have hw_sym_eq : Φ_Δ Δ (weight_triple Δ d η μ).2.1 (weight_triple Δ d η μ).2.2 ≤ Psi_Delta Δ hΔ ( (weight_triple Δ d η μ).2.1 * (weight_triple Δ d η μ).2.2 ) (by
    linarith) (by
    linarith) + ( (weight_triple Δ d η μ).2.1 + (weight_triple Δ d η μ).2.2 ) / Δ := by
      apply (Phi_upper_bound Δ hΔ (weight_triple Δ d η μ).2.1 (weight_triple Δ d η μ).2.2 (by
      exact weight_triple_pos Δ d hΔ hd hd_le η μ hη hμ |>.1) (by
      exact weight_triple_pos Δ d hΔ hd hd_le η μ hη hμ |>.2) (by
      linarith)).left
    generalize_proofs at *;
    have := dual_gap_minimized_at_symmetry Δ d hΔ hd hd_le η μ hη hμ; simp_all +decide [ weight_triple ] ;
    grind;
  · norm_num [ show η = 0 by linarith, show μ = 0 by linarith, A_d, B_d, K_to_η ]

/-
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
noncomputable section AristotleLemmas

/-
If a vector is in S_d, its first component dominates the potential function Φ_Δ.
-/
lemma Phi_le_of_mem_S_d (d : ℕ) (v : ℝ × ℝ × ℝ) (h : v ∈ S_d d) :
  v.1 ≥ Φ_Δ d v.2.1 v.2.2 := by
    -- By definition of $S_d$, we know that for all $x, y \geq 0$, $v.1 + v.2.1 * x + v.2.2 * y \geq (A_d (d + 1) x y) ^ (1 / (d + 1))$.
    have h_ineq : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → v.1 + v.2.1 * x + v.2.2 * y ≥ (A_d (d + 1) x y) ^ (1 / (d + 1 : ℝ)) := by
      exact h.2.2.2;
    refine' ciSup_le fun x => _;
    rw [ @ciSup_eq_ite ];
    split_ifs <;> norm_num;
    · refine' ciSup_le fun y => _;
      rw [ @ciSup_eq_ite ];
      split_ifs <;> norm_num at * ; linarith [ h_ineq x y ‹_› ‹_› ];
      exact le_of_lt ( h.1 );
    · exact le_of_lt h.1

/-
A function of the form x^p - ax with 0 < p < 1 and a > 0 is bounded above on [0, ∞).
-/
lemma sub_linear_growth_bounded (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a : ℝ) (ha : a > 0) :
  BddAbove {y | ∃ x ≥ 0, y = x ^ p - a * x} := by
    -- The function $f(x) = x^p - ax$ is continuous on $[0, \infty)$ and tends to $-\infty$ as $x \to \infty$, so it must attain a maximum.
    have h_cont : ContinuousOn (fun x : ℝ => x^p - a * x) (Set.Ici 0) := by
      exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.sub ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inr <| by linarith ) ( continuousAt_const.mul continuousAt_id );
    -- Since $f(x) \to -\infty$ as $x \to \infty$, there exists some $M > 0$ such that $f(x) < 0$ for all $x > M$.
    obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x > M, x^p - a * x < 0 := by
      -- Since $p < 1$, we have $\lim_{x \to \infty} \frac{x^p}{x} = 0$.
      have h_lim : Filter.Tendsto (fun x : ℝ => x^p / x) Filter.atTop (nhds 0) := by
        have h_lim : Filter.Tendsto (fun x : ℝ => x ^ (p - 1)) Filter.atTop (nhds 0) := by
          simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( p - 1 ) ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
        refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.rpow_sub_one hx.ne' ] );
      exact Filter.eventually_atTop.mp ( h_lim.eventually ( gt_mem_nhds <| show 0 < a by positivity ) ) |> fun ⟨ M, hM ⟩ ↦ ⟨ Max.max M 1, by positivity, fun x hx ↦ by have := hM x ( le_of_lt <| lt_of_le_of_lt ( le_max_left _ _ ) hx ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ le_max_right M 1 ] ⟩;
    -- Since $f(x)$ is continuous on $[0, M]$ and tends to $-\infty$ as $x \to \infty$, it must attain a maximum on this interval.
    have h_max : ∃ m ∈ Set.Icc 0 M, ∀ x ∈ Set.Icc 0 M, x^p - a * x ≤ m^p - a * m := by
      exact ( IsCompact.exists_isMaxOn ( CompactIccSpace.isCompact_Icc ) ⟨ 0, Set.left_mem_Icc.mpr hM.1.le ⟩ <| h_cont.mono <| Set.Icc_subset_Ici_self );
    obtain ⟨ m, hm₁, hm₂ ⟩ := h_max; exact ⟨ Max.max ( m ^ p - a * m ) 0, by rintro x ⟨ y, hy₁, rfl ⟩ ; exact if hy₂ : y ≤ M then by linarith [ hm₂ y ⟨ hy₁, hy₂ ⟩, le_max_left ( m ^ p - a * m ) 0, le_max_right ( m ^ p - a * m ) 0 ] else by linarith [ hM.2 y ( not_le.mp hy₂ ), le_max_left ( m ^ p - a * m ) 0, le_max_right ( m ^ p - a * m ) 0 ] ⟩ ;

/-
The potential function terms are bounded above for d ≥ 2.
-/
lemma Phi_expression_bounded (d : ℕ) (hd : d ≥ 2) (a₁ a₂ : ℝ) (ha₁ : a₁ > 0) (ha₂ : a₂ > 0) :
  BddAbove { z | ∃ x y, x ≥ 0 ∧ y ≥ 0 ∧ z = (A_d (d + 1) x y) ^ (1 / ((d : ℝ) + 1)) - a₁ * x - a₂ * y } := by
    -- By definition of $A_d$, we know that $A_d (d + 1) x y \leq C (x + y + 1)^2$ for some constant $C$.
    obtain ⟨C, hC⟩ : ∃ C > 0, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → A_d (d + 1) x y ≤ C * (x + y + 1)^2 := by
      refine ⟨ ( d + 1 ) * ( d + 1 ) + 1, by positivity, fun x y hx hy => ?_ ⟩ ; unfold A_d ; ring_nf;
      norm_num ; nlinarith [ sq_nonneg ( x - y ), mul_nonneg hx hy, mul_nonneg hx ( sq_nonneg ( d : ℝ ) ), mul_nonneg hy ( sq_nonneg ( d : ℝ ) ) ];
    -- Using the bound on $A_d$, we can show that the function $g(u) = C' * u^p - A * u$ is bounded above.
    have h_g_bounded : ∃ C' > 0, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (A_d (d + 1) x y) ^ (1 / (d + 1 : ℝ)) - a₁ * x - a₂ * y ≤ C' * (x + y + 1) ^ (2 / (d + 1 : ℝ)) - a₁ * x - a₂ * y := by
      refine' ⟨ C ^ ( 1 / ( d + 1 : ℝ ) ), Real.rpow_pos_of_pos hC.1 _, fun x y hx hy => _ ⟩;
      gcongr;
      convert Real.rpow_le_rpow ( show 0 ≤ A_d ( d + 1 ) x y from ?_ ) ( hC.2 x y hx hy ) ( show ( 0 : ℝ ) ≤ 1 / ( d + 1 ) by positivity ) using 1 ; rw [ Real.mul_rpow ( by linarith ) ( by positivity ) ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf;
      exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ) ( by positivity ) ) ( by positivity ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( by positivity ) ( by positivity ) ) ) ) zero_le_one;
    -- Using the bound on $g(u)$, we can show that the function $f(x, y)$ is bounded above.
    obtain ⟨C', hC', h_bound⟩ := h_g_bounded
    have h_f_bounded : ∃ M : ℝ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → C' * (x + y + 1) ^ (2 / (d + 1 : ℝ)) - a₁ * x - a₂ * y ≤ M := by
      have h_g_bounded : ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → C' * u ^ (2 / (d + 1 : ℝ)) - min a₁ a₂ * u ≤ M := by
        have h_g_bounded : ∃ M : ℝ, ∀ u : ℝ, 0 ≤ u → u ^ (2 / (d + 1 : ℝ)) - (min a₁ a₂ / C') * u ≤ M := by
          have := @sub_linear_growth_bounded ( 2 / ( d + 1 : ℝ ) ) ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith ) ( Min.min a₁ a₂ / C' ) ( by exact div_pos ( lt_min ha₁ ha₂ ) hC' );
          exact ⟨ this.choose, fun u hu => this.choose_spec ⟨ u, hu, rfl ⟩ ⟩;
        exact ⟨ h_g_bounded.choose * C', fun u hu => by nlinarith [ h_g_bounded.choose_spec u hu, mul_div_cancel₀ ( Min.min a₁ a₂ ) hC'.ne' ] ⟩;
      obtain ⟨ M, hM ⟩ := h_g_bounded; use M + min a₁ a₂; intros x y hx hy; specialize hM ( x + y + 1 ) ( by linarith ) ; cases min_cases a₁ a₂ <;> nlinarith;
    exact ⟨ h_f_bounded.choose, by rintro _ ⟨ x, y, hx, hy, rfl ⟩ ; exact le_trans ( h_bound x y hx hy ) ( h_f_bounded.choose_spec x y hx hy ) ⟩

/-
Sufficient condition for membership in S_d using Φ_Δ, for d ≥ 2.
-/
lemma mem_S_d_of_Phi_le (d : ℕ) (hd : d ≥ 2) (v : ℝ × ℝ × ℝ) (h_pos : v.1 > 0 ∧ v.2.1 > 0 ∧ v.2.2 > 0) (h_le : v.1 ≥ Φ_Δ d v.2.1 v.2.2) : v ∈ S_d d := by
  -- By definition of $S_d$, we need to show that for all $x, y \geq 0$, $v.1 + v.2.1 * x + v.2.2 * y \geq (A_d (d + 1) x y)^(1/(d + 1))$.
  have h_ineq : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → v.1 + v.2.1 * x + v.2.2 * y ≥ (A_d (d + 1) x y)^(1/(d + 1 : ℝ)) := by
    intro x y hx hy; contrapose! h_le; simp_all +decide [ div_eq_mul_inv ] ;
    refine' lt_of_lt_of_le _ ( le_ciSup _ x );
    · rw [ @ciSup_pos ] <;> norm_num [ hx, hy ];
      refine' lt_of_lt_of_le _ ( le_ciSup _ y ) <;> norm_num [ hx, hy ] ; linarith!;
      -- The set of values of the function is bounded above by the supremum of the set.
      have h_bdd_above : BddAbove { z | ∃ y : ℝ, y ≥ 0 ∧ z = (A_d (d + 1) x y) ^ ((d + 1 : ℝ)⁻¹) - v.2.1 * x - v.2.2 * y } := by
        have h_bdd_above : BddAbove { z | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z = (A_d (d + 1) x y) ^ (1 / ((d : ℝ) + 1)) - v.2.1 * x - v.2.2 * y } := by
          convert Phi_expression_bounded d hd v.2.1 v.2.2 h_pos.2.1 h_pos.2.2 using 1
        generalize_proofs at *; exact (by
        exact ⟨ h_bdd_above.choose, fun z hz => by obtain ⟨ y, hy, rfl ⟩ := hz; exact h_bdd_above.choose_spec ⟨ x, y, hx, hy, by norm_num ⟩ ⟩)
      generalize_proofs at *; exact (by
      obtain ⟨ M, hM ⟩ := h_bdd_above; use Max.max M 0; rintro _ ⟨ y, rfl ⟩ ; by_cases hy : 0 ≤ y <;> simp +decide [hy] ;
      exact Or.inl ( by linarith [ hM ⟨ y, hy, rfl ⟩ ] ));
    · -- By definition of $A_d$, we know that $A_d (d + 1) x y$ is bounded above for $x, y \geq 0$.
      have h_A_d_bdd_above : BddAbove { z | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z = (A_d (d + 1) x y) ^ (1 / ((d : ℝ) + 1)) - v.2.1 * x - v.2.2 * y } := by
        convert Phi_expression_bounded d hd v.2.1 v.2.2 h_pos.2.1 h_pos.2.2 using 1;
      obtain ⟨ M, hM ⟩ := h_A_d_bdd_above;
      refine' ⟨ Max.max M 0, Set.forall_mem_range.2 fun x => _ ⟩ ; by_cases hx : 0 ≤ x <;> simp_all +decide [ upperBounds ] ;
      refine' Or.inl ( ciSup_le fun y => _ ) ; by_cases hy : 0 ≤ y <;> simp_all +decide [ sub_sub ];
      · linarith [ hM x hx y hy rfl ];
      · contrapose! hM;
        refine' ⟨ _, 0, by norm_num, 0, by norm_num, rfl, _ ⟩ ; norm_num [ A_d ] ; linarith [ show ( d : ℝ ) ≥ 2 by norm_cast ] ;
  generalize_proofs at *; exact ⟨h_pos.left, h_pos.right.left, h_pos.right.right, h_ineq⟩;

end AristotleLemmas

lemma SΔ_membership_separately (Δ : ℕ) (hΔ : Δ ≥ 2) (d : ℕ) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
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
  apply_rules [ mem_S_d_of_Phi_le ];
  · refine' ⟨ div_pos _ _, div_pos _ _, div_pos _ _ ⟩;
    all_goals apply_rules [ Real.rpow_pos_of_pos, add_pos_of_nonneg_of_pos, mul_nonneg, hη, hμ ];
    all_goals norm_num; try positivity;
    exact add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hd ) ) ) hη ) hμ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg hη hμ ) );
  · have := @multivariate_reduction_to_symmetric;
    specialize this Δ d hΔ hd hd_le η μ hη hμ;
    have := @SΔ_membership_symmetric;
    specialize this Δ d hΔ hd hd_le ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ( by
      exact div_nonneg ( sub_nonneg_of_le <| Real.le_sqrt_of_sq_le <| by nlinarith [ show 1 ≤ B_d d η * B_d d μ by exact one_le_mul_of_one_le_of_one_le ( by exact le_add_of_nonneg_left <| by positivity ) ( by exact le_add_of_nonneg_left <| by positivity ) ] ) <| by positivity; );
    have := @Phi_le_of_mem_S_d Δ ( weight_triple Δ d ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ( K_to_η d ( Real.sqrt ( B_d d η * B_d d μ ) ) ) ) this;
    unfold weight_triple at *; linarith;