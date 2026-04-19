/-
**Lemma 3.5** `lem:Phi-upper-bound` (Phi_upper_bound)
Φ_Δ(a₁, a₂) is essentially upper bounded in terms of a₁a₂.

**Claim 3.6** (xi_unique_zero)
f has a unique zero ξ on (1,∞).
-/

import MultivarIndepFormalize.Concavity

set_option linter.mathlibStandardSet false
set_option linter.style.longLine false

open scoped Real

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

/--
The polynomial f(X) = (Δ+1)sX^{2Δ} - ΔX^{Δ+1} - 1.
Used in Claim 3.6 to define the unique zero ξ_Δ(s).
-/
def f_poly (Δ : ℕ) (s : ℝ) (X : ℝ) : ℝ :=
  (Δ + 1 : ℝ) * s * X ^ (2 * (Δ : ℝ)) - (Δ : ℝ) * X ^ ((Δ : ℝ) + 1) - 1

/-
Auxiliary function h(X) = (Δ+1)s X^{Δ-1} - X^{-(Δ+1)}. Used to transform the equation f(X)=0 into h(X)=Δ.
-/
def h_aux (Δ : ℕ) (s : ℝ) (X : ℝ) : ℝ :=
  (Δ + 1 : ℝ) * s * X ^ ((Δ : ℝ) - 1) - 1 / X ^ ((Δ : ℝ) + 1)

/-
Equivalence between f(X)=0 and h(X)=Δ for X > 0.
Proof: Divide f(X)=0 by X^(Δ+1) and rearrange terms.
-/
lemma f_poly_eq_h_aux_iff (Δ : ℕ) (s X : ℝ) (hX : 0 < X) :
    f_poly Δ s X = 0 ↔ h_aux Δ s X = Δ := by
      unfold f_poly h_aux;
      rw [ sub_div', div_eq_iff ] <;> first | positivity | ring_nf;
      norm_num [ Real.rpow_add hX, Real.rpow_neg_one ] ; ring_nf;
      norm_cast ; simp +decide [mul_assoc, mul_comm, mul_left_comm, hX.ne'];
      constructor <;> intro h <;> linear_combination h

/-
h(X) is strictly increasing on (0, ∞) because it is the difference of an increasing function and a decreasing function (or sum of two increasing functions).
The first term (Δ+1)s X^(Δ-1) is increasing because 2 ≤ Δ implies Δ-1 > 0.
The second term -1/X^(Δ+1) is increasing because 1/X^(Δ+1) is decreasing (exponent Δ+1 > 0).
-/
lemma h_aux_strict_mono (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs : 0 < s) :
    StrictMonoOn (h_aux Δ s) (Set.Ioi 0) := by
      intro x hx y hy hxy;
      rcases Δ with ( _ | _ | Δ ) <;> norm_num [ h_aux ] at *;
      gcongr

/-
h(1) < Δ given s < 1.
Proof: h(1) = (Δ+1)s - 1. Since s < 1, (Δ+1)s < Δ+1, so (Δ+1)s - 1 < Δ.
-/
lemma h_aux_one_lt_Delta (Δ : ℕ) (s : ℝ) (hs : s < 1) :
    h_aux Δ s 1 < Δ := by
      unfold h_aux;
      rcases Δ with ( _ | _ | Δ ) <;> norm_num at *
      · linarith
      · linarith
      · nlinarith

/-
Limit of h(X) as X -> infinity is infinity.
Proof: The first term tends to infinity because the exponent is positive. The second term tends to 0.
-/
lemma h_aux_tendsto_atTop (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (h_aux Δ s) Filter.atTop Filter.atTop := by
      -- The first term $(Δ+1)s X^{Δ-1}$ tends to infinity as $X$ tends to infinity because $Δ-1 > 0$ and $s > 0$.
      have h_term1 : Filter.Tendsto (fun X : ℝ => (Δ + 1 : ℝ) * s * X ^ ((Δ : ℝ) - 1)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_rpow_atTop ( by norm_num; linarith ) );
      -- The second term $-1/X^{Δ+1}$ tends to 0 as $X$ tends to infinity because $Δ+1 > 0$.
      have h_term2 : Filter.Tendsto (fun X : ℝ => -1 / X ^ ((Δ : ℝ) + 1)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by positivity ) );
      convert h_term1.atTop_add h_term2 using 1 ; ring_nf;
      ext; unfold h_aux; ring_nf


/--
**Claim 3.6**
f has a unique zero ξ on (1,∞).

**Statement**
For \(0< s <1\), $f(X)$ has a unique zero \(\xi_\Delta (s)\) on \((1,\infty)\).

f(X) is f_poly and defined as (Δ+1)a_1a_2 X^{2Δ} - Δ X^{Δ+1} - 1
-/
lemma xi_unique_zero (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    ∃! X : ℝ, X > 1 ∧ f_poly Δ s X = 0 := by
  -- By `f_poly_eq_h_aux_iff`, for X > 0, f_poly(X) = 0 is equivalent to h_aux(X) = Δ.
  have h_unique : ∃! X : ℝ, X > 1 ∧ h_aux Δ s X = Δ := by
    -- By `h_aux_strict_mono`, there exists a unique $X \in (1, \infty)$ such that $h_aux Δ s X = Δ$.
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X > 1 ∧ h_aux Δ s X = Δ := by
      -- By the Intermediate Value Theorem, since $h(1) < \Delta$ and $h(X) \to \infty$ as $X \to \infty$, there exists some $b > 1$ such that $h(b) > \Delta$.
      obtain ⟨b, hb₁, hb₂⟩ : ∃ b > 1, h_aux Δ s b > Δ := by
        have := h_aux_tendsto_atTop Δ hΔ s hs₀;
        exact Filter.eventually_atTop.mp ( this.eventually_gt_atTop ( Δ : ℝ ) ) |> fun ⟨ b, hb ⟩ ↦ ⟨ Max.max b 2, by norm_num, hb _ ( le_max_left _ _ ) ⟩;
      -- By the Intermediate Value Theorem, since $h(1) < \Delta$ and $h(X) \to \infty$ as $X \to \infty$, there exists some $c \in (1, b)$ such that $h(c) = \Delta$.
      obtain ⟨c, hc₁, hc₂⟩ : ∃ c ∈ Set.Ioo 1 b, h_aux Δ s c = Δ := by
        apply_rules [ intermediate_value_Ioo ];
        · linarith;
        · exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.sub ( ContinuousAt.mul continuousAt_const <| ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1 ] ) <| ContinuousAt.div continuousAt_const ( ContinuousAt.rpow continuousAt_id continuousAt_const <| Or.inl <| by linarith [ hx.1 ] ) <| ne_of_gt <| Real.rpow_pos_of_pos ( by linarith [ hx.1 ] ) _;
        · exact ⟨ h_aux_one_lt_Delta Δ s hs₁, hb₂ ⟩;
      exact ⟨ c, hc₁.1, hc₂ ⟩;
    refine' ⟨ X, hX, fun Y hY => _ ⟩;
    exact StrictMonoOn.injOn ( h_aux_strict_mono Δ hΔ s hs₀ ) ( show 0 < Y by linarith [ hY.1 ] ) ( show 0 < X by linarith [ hX.1 ] ) <| by linarith [ hY.2, hX.2 ] ;
  convert h_unique using 2;
  exact ⟨ fun h => ⟨ h.1, by rw [ f_poly_eq_h_aux_iff Δ s _ ( by linarith ) ] at h; exact h.2 ⟩, fun h => ⟨ h.1, by rw [ f_poly_eq_h_aux_iff Δ s _ ( by linarith ) ] ; exact h.2 ⟩ ⟩

/--
The unique zero ξ_Δ(s) of f(X) = (Δ+1)sX^{2Δ} - ΔX^{Δ+1} - 1 on (1, ∞).
-/
def xi_Δ (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) : ℝ :=
  (xi_unique_zero Δ hΔ s hs₀ hs₁).choose

/--
The auxiliary function Ψ_Δ(s) = ξ_Δ(s) - (2/Δ) * s * ξ_Δ(s)^Δ.
Matches source definition.
-/
def Psi_Delta (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) : ℝ :=
  let ξ := xi_Δ Δ hΔ s hs₀ hs₁
  ξ - (2 / (Δ : ℝ)) * s * ξ ^ (Δ : ℝ)


/--
The critical point (x_*, y_*) defined in (3.8) satisfies A_{Δ+1}(x_*, y_*) = ξ^{Δ+1}
and lies within the convex domain Ω. Matches page 9.
-/
lemma critical_point_in_Ω (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (_ha₂ : 0 < a₂)
    (ξ : ℝ) (hξ : 1 < ξ) (h_root : (Δ + 1 : ℝ) * (a₁ * a₂) * ξ ^ (2 * Δ) - Δ * ξ ^ (Δ + 1) - 1 = 0) :
    let x_star := (a₂ * ξ ^ Δ - 1) / Δ
    let y_star := (a₁ * ξ ^ Δ - 1) / Δ
    let Ω := {p : ℝ × ℝ | A_d (Δ + 1) p.1 p.2 > 0 ∧ p.2 > -1 / Δ}
    (x_star, y_star) ∈ Ω ∧ A_d (Δ + 1) x_star y_star = ξ ^ (Δ + 1) := by
  /-
  PROOF STRATEGY:
  1. Substitute x_star and y_star into the definition of A_{Δ+1}(x,y).
  2. Simplify the expression using the characteristic root identity h_root. [cite: 173, 604]
  3. Prove (x_star, y_star) ∈ Ω by showing y_star > -1/Δ (from ξ > 1) and A_{Δ+1} > 0.
  -/
  field_simp;
  constructor <;> norm_num [ A_d ] at *;
  · constructor <;> norm_num [ mul_assoc, mul_div_cancel₀, show Δ ≠ 0 by positivity ];
    · field_simp;
      ring_nf at *;
      nlinarith [ show ( Δ : ℝ ) * ξ > 0 by positivity, show ( ξ ^ Δ : ℝ ) > 1 by exact one_lt_pow₀ hξ ( by positivity ) ];
    · positivity;
  · -- Substitute the given root condition into the expression.
    have h_sub : (Δ + 1) * (a₁ * a₂) * ξ ^ (2 * Δ) = Δ * ξ ^ (Δ + 1) + 1 := by
      linarith;
    field_simp;
    linear_combination' h_sub

/-
The value at the critical point provides an upper bound for the variation of A_{Δ+1}^{1/(Δ+1)}.
Matches page 9, Equation 3.7.
-/
noncomputable section AristotleLemmas

/-
Gradient inequality for concave functions: f(y) ≤ f(x) + ∇f(x)·(y-x).
-/
lemma concave_gradient_inequality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) {f : E → ℝ} (hf : ConcaveOn ℝ S f)
    {x y : E} (hx : x ∈ interior S) (hy : y ∈ S)
    (hdiff : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) := by
      have h_subgradient : ∀ u ∈ S, f u ≤ f x + (fderiv ℝ f x) (u - x) := by
        intro u hu;
        have h_subgradient : ∀ t : ℝ, 0 < t → t < 1 → f (x + t • (u - x)) ≥ (1 - t) * f x + t * f u := by
          intro t ht₁ ht₂
          have h_convex : x + t • (u - x) ∈ S := by
            have := hS ( show x ∈ S from interior_subset hx ) hu;
            convert this ( show 0 ≤ 1 - t by linarith ) ( show 0 ≤ t by linarith ) ( by linarith ) using 1 ; simp +decide [ sub_smul, smul_sub ] ; abel_nf;
          have := hf.2;
          specialize this ( show x ∈ S from interior_subset hx ) hu ( show 0 ≤ 1 - t by linarith ) ( show 0 ≤ t by linarith ) ( by linarith ) ; simp_all +decide [add_comm,
            smul_sub];
          convert this using 2 ; rw [ show x + ( t • u - t • x ) = t • u + ( 1 - t ) • x by rw [ sub_smul, one_smul ] ; abel1 ];
        -- By definition of the derivative, we know that
        have h_deriv : Filter.Tendsto (fun t : ℝ => (f (x + t • (u - x)) - f x) / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((fderiv ℝ f x) (u - x))) := by
          have h_deriv : HasDerivAt (fun t : ℝ => f (x + t • (u - x))) ((fderiv ℝ f x) (u - x)) 0 := by
            have h_deriv : HasFDerivAt (fun t : ℝ => f (x + t • (u - x))) (fderiv ℝ f x ∘L (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (u - x))) 0 := by
              have h_chain : HasFDerivAt (fun t : ℝ => x + t • (u - x)) (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (u - x)) 0 := by
                rw [ hasFDerivAt_iff_tendsto ];
                simp +decide
              exact HasFDerivAt.comp 0 ( show HasFDerivAt f ( fderiv ℝ f x ) ( x + 0 • ( u - x ) ) from by simpa using hdiff.hasFDerivAt ) h_chain;
            simpa using h_deriv.hasDerivAt;
          simpa [ div_eq_inv_mul ] using h_deriv.tendsto_slope_zero_right;
        -- By definition of the derivative, we know that for $t$ close to $0$, $(f (x + t • (u - x)) - f x) / t$ is close to $(fderiv ℝ f x) (u - x)$.
        have h_deriv_close : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), (f (x + t • (u - x)) - f x) / t ≥ f u - f x := by
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with t ht using by rw [ ge_iff_le ] ; rw [ le_div_iff₀ ht.1 ] ; linarith [ h_subgradient t ht.1 ht.2 ] ;
        exact le_of_not_gt fun h => absurd ( le_of_tendsto_of_tendsto tendsto_const_nhds h_deriv h_deriv_close ) ( by linarith );
      exact h_subgradient y hy

/-
The gradient of A_{Δ+1}^{1/(Δ+1)} at the critical point (x_*, y_*) is (a₁, a₂).
Proof sketch:
1. Calculate partial derivatives of A_{Δ+1}(x,y).
2. Use chain rule for f(x,y) = A(x,y)^{1/(Δ+1)}.
3. Substitute x_*, y_* and simplify using the definitions.
4. Verify differentiability since A(x_*, y_*) = ξ^{Δ+1} > 0.
-/
lemma A_d_gradient_at_critical (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (_ha₁ : 0 < a₁) (_ha₂ : 0 < a₂)
    (ξ : ℝ) (hξ : 1 < ξ)
    (x_star y_star : ℝ)
    (hx_star : x_star = (a₂ * ξ ^ Δ - 1) / Δ)
    (hy_star : y_star = (a₁ * ξ ^ Δ - 1) / Δ)
    (h_root : (Δ + 1 : ℝ) * (a₁ * a₂) * ξ ^ (2 * Δ) - Δ * ξ ^ (Δ + 1) - 1 = 0) :
    let f := fun p : ℝ × ℝ => (A_d (Δ + 1) p.1 p.2) ^ (1 / (Δ + 1 : ℝ))
    DifferentiableAt ℝ f (x_star, y_star) ∧
    ∀ u v : ℝ, fderiv ℝ f (x_star, y_star) (u, v) = a₁ * u + a₂ * v := by
      norm_num [ A_d ] at *;
      constructor;
      · apply_rules [ DifferentiableAt.rpow, DifferentiableAt.add, DifferentiableAt.mul, differentiableAt_id, differentiableAt_const ] <;> norm_num;
        subst_vars;
        field_simp;
        ring_nf at *;
        nlinarith [ show ( Δ : ℝ ) * ξ * ξ ^ Δ > 0 by positivity ];
      · -- Let's simplify the expression for the derivative.
        have h_deriv : deriv (fun x => ((Δ + 1) * Δ * x * y_star + (Δ + 1) * (x + y_star) + 1) ^ (1 / (Δ + 1 : ℝ))) x_star = a₁ := by
          have h_deriv_x : deriv (fun x => ((Δ + 1) * Δ * x * y_star + (Δ + 1) * (x + y_star) + 1) ^ (1 / (Δ + 1 : ℝ))) x_star = (1 / (Δ + 1 : ℝ)) * ((Δ + 1) * Δ * x_star * y_star + (Δ + 1) * (x_star + y_star) + 1) ^ ((1 / (Δ + 1 : ℝ)) - 1) * ((Δ + 1) * Δ * y_star + (Δ + 1)) := by
            convert HasDerivAt.deriv ( HasDerivAt.rpow_const ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id' x_star ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.add ( hasDerivAt_id' x_star ) ( hasDerivAt_const _ _ ) ) ) ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num ; ring;
            refine' Or.inl _;
            rw [ hx_star, hy_star ];
            field_simp;
            ring_nf at *;
            nlinarith [ show ( Δ : ℝ ) * ξ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ * a₂ > 0 by positivity ];
          -- Substitute the expression for the derivative into the goal.
          rw [h_deriv_x];
          -- Substitute the expression for the derivative into the goal and simplify.
          have h_simp : ((Δ + 1) * Δ * x_star * y_star + (Δ + 1) * (x_star + y_star) + 1) = ξ ^ (Δ + 1) := by
            rw [ hx_star, hy_star ] ; ring_nf;
            field_simp;
            grind;
          rw [ h_simp ];
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), Nat.cast_add_one, mul_sub, mul_one, mul_div_cancel₀ _ ( by positivity ) ] ; norm_num;
          field_simp [hy_star]
          ring_nf;
          rw [ hy_star ] ; linarith [ mul_div_cancel₀ ( a₁ * ξ ^ Δ - 1 ) ( by positivity : ( Δ : ℝ ) ≠ 0 ) ];
        have h_deriv_y : deriv (fun y => ((Δ + 1) * Δ * x_star * y + (Δ + 1) * (x_star + y) + 1) ^ (1 / (Δ + 1 : ℝ))) y_star = a₂ := by
          convert HasDerivAt.deriv ( HasDerivAt.rpow_const ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ) ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num;
          · field_simp [hx_star, hy_star];
            rw [ hx_star, hy_star ];
            rw [ mul_div_cancel₀ _ ( by positivity ) ] ; ring_nf;
            rw [ show ( 1 + a₂ * ξ ^ ( Δ * 2 ) * ( Δ : ℝ ) * a₁ * ( Δ : ℝ ) ⁻¹ + a₂ * ξ ^ ( Δ * 2 ) * a₁ * ( Δ : ℝ ) ⁻¹ + ( - ( ( Δ : ℝ ) * ( Δ : ℝ ) ⁻¹ ) - ( Δ : ℝ ) ⁻¹ ) ) = ( ξ ^ ( Δ + 1 ) ) by
                  field_simp;
                  ring_nf at * ; linarith ];
            norm_num [ Real.rpow_def_of_pos ( by positivity : 0 < ξ ^ ( Δ + 1 ) ) ];
            rw [ show ( ( Δ : ℝ ) + 1 ) * Real.log ξ * ( ( Δ : ℝ ) * ( 1 + ( Δ : ℝ ) ) ⁻¹ ) = Real.log ξ * Δ by nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( 1 + ( Δ : ℝ ) ) ≠ 0 ) ( Real.log ξ ) ] ] ; rw [ Real.exp_neg, Real.exp_mul, Real.exp_log ( by positivity ) ] ; norm_cast;
            rw [ mul_assoc, mul_inv_cancel₀ ( by positivity ), mul_one ];
          · left;
            rw [ hx_star, hy_star ];
            field_simp;
            ring_nf at *;
            nlinarith [ show ( Δ : ℝ ) * ξ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ * a₂ > 0 by positivity ];
        have h_deriv_x : deriv (fun x => ((Δ + 1) * Δ * x * y_star + (Δ + 1) * (x + y_star) + 1) ^ (1 / (Δ + 1 : ℝ))) x_star = (fderiv ℝ (fun p : ℝ × ℝ => ((Δ + 1) * Δ * p.1 * p.2 + (Δ + 1) * (p.1 + p.2) + 1) ^ (1 / (Δ + 1 : ℝ))) (x_star, y_star)) (1, 0) := by
          rw [ deriv ];
          rw [ show ( fun x : ℝ => ( ( Δ + 1 : ℝ ) * Δ * x * y_star + ( Δ + 1 : ℝ ) * ( x + y_star ) + 1 ) ^ ( 1 / ( Δ + 1 : ℝ ) ) ) = ( fun p : ℝ × ℝ => ( ( Δ + 1 : ℝ ) * Δ * p.1 * p.2 + ( Δ + 1 : ℝ ) * ( p.1 + p.2 ) + 1 ) ^ ( 1 / ( Δ + 1 : ℝ ) ) ) ∘ ( fun x : ℝ => ( x, y_star ) ) by ext; simp +decide, fderiv_comp ] <;> norm_num;
          · rw [ show deriv ( fun x : ℝ => ( x, y_star ) ) x_star = ( 1, 0 ) from HasDerivAt.deriv ( by simpa using HasDerivAt.prodMk ( hasDerivAt_id x_star ) ( hasDerivAt_const _ _ ) ) ];
          · apply_rules [ DifferentiableAt.rpow, DifferentiableAt.add, DifferentiableAt.mul, differentiableAt_id, differentiableAt_const ] <;> norm_num;
            rw [ hx_star, hy_star ];
            field_simp;
            ring_nf at *;
            nlinarith [ show ( Δ : ℝ ) * ξ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₁ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ * a₂ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) * a₁ * a₂ > 0 by positivity ];
        have h_deriv_y : deriv (fun y => ((Δ + 1) * Δ * x_star * y + (Δ + 1) * (x_star + y) + 1) ^ (1 / (Δ + 1 : ℝ))) y_star = (fderiv ℝ (fun p : ℝ × ℝ => ((Δ + 1) * Δ * p.1 * p.2 + (Δ + 1) * (p.1 + p.2) + 1) ^ (1 / (Δ + 1 : ℝ))) (x_star, y_star)) (0, 1) := by
          rw [ deriv ];
          rw [ show ( fun y : ℝ => ( ( Δ + 1 : ℝ ) * Δ * x_star * y + ( Δ + 1 : ℝ ) * ( x_star + y ) + 1 ) ^ ( 1 / ( Δ + 1 : ℝ ) ) ) = ( fun p : ℝ × ℝ => ( ( Δ + 1 : ℝ ) * Δ * p.1 * p.2 + ( Δ + 1 : ℝ ) * ( p.1 + p.2 ) + 1 ) ^ ( 1 / ( Δ + 1 : ℝ ) ) ) ∘ ( fun y : ℝ => ( x_star, y ) ) by ext; simp +decide, fderiv_comp ] <;> norm_num;
          · rw [ show deriv ( fun y : ℝ => ( x_star, y ) ) y_star = ( 0, 1 ) from HasDerivAt.deriv ( by simpa using HasDerivAt.prodMk ( hasDerivAt_const _ _ ) ( hasDerivAt_id y_star ) ) ];
          · apply_rules [ DifferentiableAt.rpow, DifferentiableAt.add, DifferentiableAt.mul, differentiableAt_id, differentiableAt_const ] <;> norm_num;
            rw [ hx_star, hy_star ];
            field_simp;
            ring_nf at *;
            nlinarith [ show ( Δ : ℝ ) * ξ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * ξ ^ ( Δ * 2 ) > 0 by positivity, show ( Δ : ℝ ) * a₂ * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * a₂ * ξ ^ ( Δ * 2 ) > 0 by positivity, show ( Δ : ℝ ) * a₁ * ξ ^ Δ > 0 by positivity, show ( Δ : ℝ ) * a₁ * ξ ^ ( Δ * 2 ) > 0 by positivity ];
          · exact differentiableAt_const _ |> DifferentiableAt.prodMk <| differentiableAt_id;
        intro u v; rw [ ← h_deriv, ← ‹deriv ( fun y => ( ( Δ + 1 : ℝ ) * Δ * x_star * y + ( Δ + 1 : ℝ ) * ( x_star + y ) + 1 ) ^ ( 1 / ( Δ + 1 : ℝ ) ) ) y_star = a₂› ] ; rw [ h_deriv_x, h_deriv_y ] ; ring_nf;
        rw [ show ( u, v ) = u • ( 1, 0 ) + v • ( 0, 1 ) by ext <;> simp +decide ] ; rw [ map_add, map_smul, map_smul ] ; ring_nf;
        norm_num [ mul_comm ]

/-
Algebraic identity: ξ - a₁x_* - a₂y_* = Ψ_Δ(s) + (a₁+a₂)/Δ.
Proof: Substitute x_*, y_* and simplify.
ξ - a₁((a₂ξ^Δ - 1)/Δ) - a₂((a₁ξ^Δ - 1)/Δ)
= ξ - (sξ^Δ - a₁)/Δ - (sξ^Δ - a₂)/Δ
= ξ - 2sξ^Δ/Δ + (a₁+a₂)/Δ
= Ψ_Δ(s) + (a₁+a₂)/Δ.
-/
lemma variational_algebraic_identity (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (_ha₁ : 0 < a₁) (_ha₂ : 0 < a₂)
    (ξ : ℝ) (_hξ : 1 < ξ)
    (x_star y_star : ℝ)
    (hx_star : x_star = (a₂ * ξ ^ Δ - 1) / Δ)
    (hy_star : y_star = (a₁ * ξ ^ Δ - 1) / Δ)
    (s : ℝ) (hs : s = a₁ * a₂)
    (hs₀ : 0 < s) (hs₁ : s < 1)
    (h_xi_def : ξ = xi_Δ Δ hΔ s hs₀ hs₁) :
    ξ - a₁ * x_star - a₂ * y_star = Psi_Delta Δ hΔ s hs₀ hs₁ + (a₁ + a₂) / Δ := by
      unfold Psi_Delta; ring_nf;
      rw [ ← h_xi_def ] ; rw [ hx_star, hy_star, hs ] ; ring_nf;
      norm_cast ; ring

lemma domain_convex (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    Convex ℝ {p : ℝ × ℝ | p.1 > -1 / (Δ : ℝ) ∧ p.2 > -1 / (Δ : ℝ) ∧ A_d (Δ + 1) p.1 p.2 > 0} := by
      -- Let $u = x + 1/\Delta$ and $v = y + 1/\Delta$.
      set S' := {p : ℝ × ℝ | p.1 > 0 ∧ p.2 > 0 ∧ A_d (Δ + 1) (p.1 - 1 / Δ) (p.2 - 1 / Δ) > 0} with hS'_def
      have h_convex_S' : Convex ℝ S' := by
        -- The set $S'$ is convex because it is the superlevel set of the convex function $f(u,v) = uv$ on the positive quadrant.
        have h_convex_f : Convex ℝ {p : ℝ × ℝ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 * p.2 > 1 / (Δ^2 * (Δ + 1) : ℝ)} := by
          field_simp;
          refine' convex_iff_forall_pos.mpr _;
          simp +zetaDelta at *;
          intro a b ha hb hab a' b' ha' hb' hab' x y hx hy hxy
          have h_pos : 0 < x * a + y * a' ∧ 0 < x * b + y * b' := by
            exact ⟨ by positivity, by positivity ⟩
          have h_ineq : (x * a + y * a') * (x * b + y * b') ≥ (x * Real.sqrt (a * b) + y * Real.sqrt (a' * b')) ^ 2 := by
            rw [ Real.sqrt_mul ha.le, Real.sqrt_mul ha'.le ];
            rw [ ← Real.sq_sqrt ha.le, ← Real.sq_sqrt hb.le, ← Real.sq_sqrt ha'.le, ← Real.sq_sqrt hb'.le ] ; ring_nf;
            rw [ Real.sqrt_sq ( by positivity ), Real.sqrt_sq ( by positivity ), Real.sqrt_sq ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; nlinarith [ sq_nonneg ( Real.sqrt a * Real.sqrt b' - Real.sqrt a' * Real.sqrt b ), mul_pos hx hy ] ;
          have h_sqrt : x * Real.sqrt (a * b) + y * Real.sqrt (a' * b') > 1 / (Real.sqrt (Δ^2 * (Δ + 1))) := by
            have h_sqrt : Real.sqrt (a * b) > 1 / Real.sqrt (Δ^2 * (Δ + 1)) ∧ Real.sqrt (a' * b') > 1 / Real.sqrt (Δ^2 * (Δ + 1)) := by
              exact ⟨ Real.lt_sqrt_of_sq_lt <| by rw [ div_pow, Real.sq_sqrt <| by positivity ] ; rw [ div_lt_iff₀ <| by positivity ] ; linarith, Real.lt_sqrt_of_sq_lt <| by rw [ div_pow, Real.sq_sqrt <| by positivity ] ; rw [ div_lt_iff₀ <| by positivity ] ; linarith ⟩;
            nlinarith [ show 0 < x * Real.sqrt ( a * b ) by positivity, show 0 < y * Real.sqrt ( a' * b' ) by positivity ]
          have h_final : (x * a + y * a') * (x * b + y * b') > 1 / (Δ^2 * (Δ + 1)) := by
            field_simp;
            rw [ gt_iff_lt, div_lt_iff₀ ] at h_sqrt <;> nlinarith [ show 0 < Real.sqrt ( Δ ^ 2 * ( Δ + 1 ) ) by positivity, Real.mul_self_sqrt ( show 0 ≤ ( Δ : ℝ ) ^ 2 * ( Δ + 1 ) by positivity ) ]
          exact ⟨h_pos.left, h_pos.right, by
            rw [ gt_iff_lt, div_lt_iff₀ ] at h_final <;> first | positivity | linarith;⟩;
        convert h_convex_f using 1;
        ext ⟨x, y⟩; simp [S', A_d];
        field_simp;
        exact fun hx hy => ⟨ fun h => by nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ], fun h => by nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ] ⟩;
      field_simp;
      convert h_convex_S'.translate ( - ( 1 / Δ : ℝ ), - ( 1 / Δ : ℝ ) ) using 1;
      ext ⟨x, y⟩; simp [S'];
      exact ⟨ fun h => ⟨ by nlinarith [ inv_mul_cancel₀ ( by positivity : ( Δ : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ], by nlinarith [ inv_mul_cancel₀ ( by positivity : ( Δ : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ], h.2.2 ⟩, fun h => ⟨ by nlinarith [ inv_mul_cancel₀ ( by positivity : ( Δ : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ], by nlinarith [ inv_mul_cancel₀ ( by positivity : ( Δ : ℝ ) ≠ 0 ), ( by norm_cast : ( 1 : ℝ ) ≤ Δ ) ], h.2.2 ⟩ ⟩

end AristotleLemmas

lemma variational_upper_bound (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (ha₁ : a₁ > 0) (ha₂ : a₂ > 0) (ha₁a₂ : a₁ * a₂ < 1)
    (x_star y_star : ℝ) (ξ : ℝ) (_h_A : A_d (Δ + 1) x_star y_star = ξ ^ (Δ + 1)) :
    let s := a₁ * a₂
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := ha₁a₂
    (∀ x y, x ≥ 0 → y ≥ 0 → A_d (Δ + 1) x y ^ (1 / (Δ + 1 : ℝ)) - a₁ * x - a₂ * y ≤
      Psi_Delta Δ hΔ s hs₀ hs₁ + (a₁ + a₂) / Δ) := by
  /-
  PROOF STRATEGY:
  1. Invoke Lemma 3.1: A_{Δ+1}^{1/(Δ+1)} is concave on the convex set Ω. [cite: 126, 531, 543]
  2. Show that at (x_star, y_star), the partial derivatives match a₁ and a₂. [cite: 165, 595, 597]
  3. Conclude the tangent plane bound: f(x,y) ≤ f(x_*, y_*) + ∇f(x_*, y_*) · (x-x_*, y-y_*).
  4. Use algebra to simplify this to the definition of Psi_Delta. [cite: 181, 613]
  -/
  intro s hs₀ hs₁ x y hx hy;
  -- By definition of $f_poly$, we know that there exists a unique $\xi > 1$ such that $f_poly Δ s ξ = 0$.
  obtain ⟨ξ, hξ_pos, hξ_unique⟩ : ∃! ξ : ℝ, ξ > 1 ∧ f_poly Δ s ξ = 0 := by
    convert xi_unique_zero Δ hΔ s hs₀ hs₁ using 1;
  -- By definition of $f_poly$, we know that $A_{Δ+1}(x_*, y_*) = \xi^{Δ+1}$ and $(x_*, y_*) \in Ω$.
  obtain ⟨x_star, y_star, hx_star, hy_star, h_critical⟩ : ∃ x_star y_star : ℝ, x_star = (a₂ * ξ ^ Δ - 1) / Δ ∧ y_star = (a₁ * ξ ^ Δ - 1) / Δ ∧ (x_star, y_star) ∈ {p : ℝ × ℝ | p.1 > -1 / (Δ : ℝ) ∧ p.2 > -1 / (Δ : ℝ) ∧ A_d (Δ + 1) p.1 p.2 > 0} ∧ A_d (Δ + 1) x_star y_star = ξ ^ (Δ + 1) := by
    refine' ⟨ _, _, rfl, rfl, _, _ ⟩;
    · refine' ⟨ _, _, _ ⟩;
      · rw [ gt_iff_lt, div_lt_div_iff_of_pos_right ] <;> norm_num <;> nlinarith [ pow_le_pow_right₀ hξ_pos.1.le ( show Δ ≥ 1 by linarith ) ];
      · rw [ gt_iff_lt, div_lt_div_iff_of_pos_right ] <;> norm_num <;> nlinarith [ pow_le_pow_right₀ hξ_pos.1.le ( show Δ ≥ 1 by linarith ) ];
      · unfold A_d;
        field_simp;
        norm_num [ f_poly ] at *;
        norm_cast at *;
        norm_num [ pow_mul' ] at *;
        nlinarith [ show 0 < ( Δ : ℝ ) * a₁ * a₂ by positivity, show 0 < ( Δ : ℝ ) * a₁ by positivity, show 0 < ( Δ : ℝ ) * a₂ by positivity, show 0 < ( Δ : ℝ ) * ξ ^ Δ by exact mul_pos ( by positivity ) ( pow_pos ( by linarith ) _ ), show 0 < ( Δ : ℝ ) * ξ ^ ( Δ + 1 ) by exact mul_pos ( by positivity ) ( pow_pos ( by linarith ) _ ) ];
    · convert critical_point_in_Ω Δ hΔ a₁ a₂ ha₁ ha₂ ξ hξ_pos.1 _ |>.2 using 1;
      convert hξ_pos.2 using 1;
      unfold f_poly; norm_cast;
  -- By definition of $f_poly$, we know that $A_{Δ+1}(x, y)^{1/(Δ+1)} \leq A_{Δ+1}(x_*, y_*)^{1/(Δ+1)} + \nabla A_{Δ+1}(x_*, y_*) \cdot ((x, y) - (x_*, y_*))$.
  have h_ineq : (A_d (Δ + 1) x y) ^ (1 / ((Δ : ℝ) + 1)) ≤ (A_d (Δ + 1) x_star y_star) ^ (1 / ((Δ : ℝ) + 1)) + a₁ * (x - x_star) + a₂ * (y - y_star) := by
    have h_ineq : ConcaveOn ℝ {p : ℝ × ℝ | p.1 > -1 / (Δ : ℝ) ∧ p.2 > -1 / (Δ : ℝ) ∧ A_d (Δ + 1) p.1 p.2 > 0} (fun p => (A_d (Δ + 1) p.1 p.2) ^ (1 / ((Δ : ℝ) + 1))) := by
      apply_rules [ A_d_pow_dinv_concave ];
      · convert domain_convex Δ ( by linarith ) using 1;
      · exact fun p hp => hp.2.2;
    have h_ineq : ∀ p : ℝ × ℝ, p ∈ {p : ℝ × ℝ | p.1 > -1 / (Δ : ℝ) ∧ p.2 > -1 / (Δ : ℝ) ∧ A_d (Δ + 1) p.1 p.2 > 0} → (A_d (Δ + 1) p.1 p.2) ^ (1 / ((Δ : ℝ) + 1)) ≤ (A_d (Δ + 1) x_star y_star) ^ (1 / ((Δ : ℝ) + 1)) + a₁ * (p.1 - x_star) + a₂ * (p.2 - y_star) := by
      intros p hp;
      have h_ineq : DifferentiableAt ℝ (fun p : ℝ × ℝ => (A_d (Δ + 1) p.1 p.2) ^ (1 / ((Δ : ℝ) + 1))) (x_star, y_star) ∧ ∀ u v : ℝ, fderiv ℝ (fun p : ℝ × ℝ => (A_d (Δ + 1) p.1 p.2) ^ (1 / ((Δ : ℝ) + 1))) (x_star, y_star) (u, v) = a₁ * u + a₂ * v := by
        convert A_d_gradient_at_critical Δ hΔ a₁ a₂ ha₁ ha₂ ξ hξ_pos.1 x_star y_star hx_star hy_star _ using 1;
        convert hξ_pos.2 using 1;
        unfold f_poly; ring_nf;
        norm_cast ; ring;
      have := concave_gradient_inequality ( show Convex ℝ { p : ℝ × ℝ | p.1 > -1 / ( Δ : ℝ ) ∧ p.2 > -1 / ( Δ : ℝ ) ∧ A_d ( Δ + 1 ) p.1 p.2 > 0 } from ?_ ) ‹_› ( show ( x_star, y_star ) ∈ interior { p : ℝ × ℝ | p.1 > -1 / ( Δ : ℝ ) ∧ p.2 > -1 / ( Δ : ℝ ) ∧ A_d ( Δ + 1 ) p.1 p.2 > 0 } from ?_ ) hp h_ineq.1;
      · convert this using 1 ; rw [ h_ineq.2 ] ; ring_nf;
        norm_num ; ring;
      · convert domain_convex Δ ( by linarith ) using 1;
      · refine' mem_interior_iff_mem_nhds.mpr _;
        refine' IsOpen.mem_nhds _ _;
        · refine' IsOpen.inter ( isOpen_lt continuous_const continuous_fst ) ( IsOpen.inter ( isOpen_lt continuous_const continuous_snd ) _ );
          exact isOpen_lt continuous_const ( show Continuous fun p : ℝ × ℝ => A_d ( Δ + 1 ) p.1 p.2 from by unfold A_d; fun_prop );
        · exact h_critical.1;
    convert h_ineq ( x, y ) _ using 1;
    norm_num [ A_d ] at *;
    exact ⟨ by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ show ( Δ : ℝ ) ≥ 2 by norm_cast ], by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ show ( Δ : ℝ ) ≥ 2 by norm_cast ], by positivity ⟩;
  -- By definition of $f_poly$, we know that $A_{Δ+1}(x_*, y_*) = \xi^{Δ+1}$ and $(x_*, y_*) \in Ω$, thus $A_{Δ+1}(x_*, y_*)^{1/(Δ+1)} = \xi$.
  have h_critical_val : (A_d (Δ + 1) x_star y_star) ^ (1 / ((Δ : ℝ) + 1)) = ξ := by
    rw [ h_critical.2, ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith ), Nat.cast_add_one, mul_one_div_cancel ( by linarith ), Real.rpow_one ];
  -- By definition of $f_poly$, we know that $\xi - a₁ x_* - a₂ y_* = \Psi_\Delta(s) + (a₁ + a₂) / Δ$.
  have h_variational : ξ - a₁ * x_star - a₂ * y_star = Psi_Delta Δ hΔ s hs₀ hs₁ + (a₁ + a₂) / (Δ : ℝ) := by
    apply variational_algebraic_identity;
    all_goals norm_num [ s ] at *;
    any_goals assumption;
    · linarith;
    · exact hξ_unique _ ( xi_unique_zero Δ hΔ ( a₁ * a₂ ) hs₀ hs₁ |> Exists.choose_spec |> And.left |> And.left ) ( xi_unique_zero Δ hΔ ( a₁ * a₂ ) hs₀ hs₁ |> Exists.choose_spec |> And.left |> And.right ) ▸ rfl;
  linarith

/-
In the symmetric case a₁ = a₂, the maximum is attained at x_* = y_* > 0.
Matches page 9.
-/
noncomputable section AristotleLemmas

lemma xi_bound_helper (Δ : ℕ) (hΔ : 2 ≤ Δ) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
    s * (xi_Δ Δ hΔ s hs₀ hs₁) ^ (2 * Δ) > 1 := by
      -- By definition of $xi_Δ$, we know that $(Δ + 1) * s * (xi_Δ Δ hΔ s hs₀ hs₁) ^ (2 * Δ) = Δ * (xi_Δ Δ hΔ s hs₀ hs₁) ^ (Δ + 1) + 1$.
      have h_eq : (Δ + 1) * s * (xi_Δ Δ hΔ s hs₀ hs₁) ^ (2 * Δ) = Δ * (xi_Δ Δ hΔ s hs₀ hs₁) ^ (Δ + 1) + 1 := by
        have := Exists.choose_spec ( xi_unique_zero Δ hΔ s hs₀ hs₁ );
        unfold xi_Δ f_poly at *;
        norm_cast at *; linarith [ this.1.2 ] ;
      -- Since ξ > 1 (by definition of xi_Δ) and Δ ≥ 2, we have ξ^{Δ+1} > 1, so Δ ξ^{Δ+1} + 1 > Δ + 1.
      have h_ineq : (xi_Δ Δ hΔ s hs₀ hs₁) ^ (Δ + 1) > 1 := by
        have h_ineq : 1 < xi_Δ Δ hΔ s hs₀ hs₁ := by
          exact Classical.choose_spec ( xi_unique_zero Δ hΔ s hs₀ hs₁ ) |>.1 |>.1;
        exact one_lt_pow₀ h_ineq ( by positivity );
      nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ Δ ) ]

lemma symmetric_critical_point_pos (Δ : ℕ) (hΔ : 2 ≤ Δ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let s := a * a
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := by nlinarith
    let ξ := xi_Δ Δ hΔ s hs₀ hs₁
    let x_star := (a * ξ ^ Δ - 1) / Δ
    x_star > 0 := by
      -- By definition of $\xi$, we have $\xi > 1$ because $s = a^2 < 1$.
      have hξ_pos : 1 < xi_Δ Δ hΔ (a * a) (mul_pos ha₀ ha₀) (by nlinarith) := by
        exact ( xi_unique_zero Δ hΔ ( a * a ) ( mul_pos ha₀ ha₀ ) ( by nlinarith ) ) |>.choose_spec.1.1;
      refine' div_pos _ ( by positivity );
      have := xi_bound_helper Δ hΔ ( a * a ) ( mul_pos ha₀ ha₀ ) ( by nlinarith );
      rw [ pow_mul' ] at this ; nlinarith [ show 0 < a * xi_Δ Δ hΔ ( a * a ) ( mul_pos ha₀ ha₀ ) ( by nlinarith ) ^ Δ by positivity ]

lemma symmetric_value_at_critical (Δ : ℕ) (hΔ : 2 ≤ Δ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let s := a * a
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := by nlinarith
    let ξ := xi_Δ Δ hΔ s hs₀ hs₁
    let x_star := (a * ξ ^ Δ - 1) / Δ
    A_d (Δ + 1) x_star x_star ^ (1 / (Δ + 1 : ℝ)) - a * x_star - a * x_star =
      Psi_Delta Δ hΔ s hs₀ hs₁ + (2 * a) / Δ := by
        have := xi_unique_zero Δ hΔ ( a * a ) ( by positivity ) ( by nlinarith );
        obtain ⟨ ξ, hξ₁, hξ₂ ⟩ := this;
        have := hξ₂ ( xi_Δ Δ hΔ ( a * a ) ( by positivity ) ( by nlinarith ) ) ⟨ ?_, ?_ ⟩ <;> norm_num [ f_poly ] at *;
        · field_simp;
          rw [ show A_d ( Δ + 1 ) ( ( a * xi_Δ Δ hΔ ( a ^ 2 ) ( by positivity ) ( by nlinarith ) ^ Δ - 1 ) / Δ ) ( ( a * xi_Δ Δ hΔ ( a ^ 2 ) ( by positivity ) ( by nlinarith ) ^ Δ - 1 ) / Δ ) = ξ ^ ( Δ + 1 ) from ?_ ];
          · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith ) ] ; norm_num [ Nat.cast_add_one_ne_zero ] ; ring_nf;
            unfold Psi_Delta; norm_num [ this ] ; ring_nf;
            rw [ show xi_Δ Δ hΔ ( a ^ 2 ) ( by positivity ) ( by nlinarith ) = ξ by simpa only [ sq ] using this ] ; nlinarith [ mul_inv_cancel_left₀ ( by positivity : ( Δ : ℝ ) ≠ 0 ) ( a ^ 2 * ξ ^ Δ ) ];
          · convert critical_point_in_Ω Δ hΔ a a ha₀ ha₀ ξ hξ₁.1 _ |> And.right using 1;
            · norm_num [ ← this, sq ];
            · exact_mod_cast hξ₁.2;
        · exact Classical.choose_spec ( xi_unique_zero Δ hΔ ( a * a ) ( by positivity ) ( by nlinarith ) ) |>.1.1;
        · convert Classical.choose_spec ( xi_unique_zero Δ hΔ ( a * a ) ( by positivity ) ( by nlinarith ) ) |>.1.2 using 1

lemma symmetric_pointwise_upper_bound (Δ : ℕ) (hΔ : 2 ≤ Δ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let s := a * a
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := by nlinarith
    ∀ x y, x ≥ 0 → y ≥ 0 → A_d (Δ + 1) x y ^ (1 / (Δ + 1 : ℝ)) - a * x - a * y ≤
      Psi_Delta Δ hΔ s hs₀ hs₁ + (2 * a) / Δ := by
        -- By definition of $xi$, we know that $xi$ is the unique zero of $f_poly$ in $(1, \infty)$.
        have h_xi : ∃ x_star : ℝ, x_star > 1 ∧ f_poly Δ (a * a) x_star = 0 ∧ A_d (Δ + 1) ((a * x_star ^ Δ - 1) / Δ) ((a * x_star ^ Δ - 1) / Δ) = x_star ^ (Δ + 1) := by
          obtain ⟨x_star, hx_star⟩ : ∃ x_star : ℝ, x_star > 1 ∧ f_poly Δ (a * a) x_star = 0 := by
            exact ExistsUnique.exists ( xi_unique_zero Δ hΔ ( a * a ) ( mul_pos ha₀ ha₀ ) ( by nlinarith ) );
          exact ⟨ x_star, hx_star.1, hx_star.2, by
            unfold A_d f_poly at *;
            norm_cast at *;
            simp_all +decide [ Int.subNatNat_eq_coe ];
            field_simp;
            ring_nf at * ; linarith ⟩;
        obtain ⟨x_star, hx_star_gt1, hx_star_root, hx_star_A⟩ := h_xi;
        convert variational_upper_bound Δ hΔ a a ha₀ ha₀ ( by nlinarith ) ( ( a * x_star ^ Δ - 1 ) / Δ ) ( ( a * x_star ^ Δ - 1 ) / Δ ) x_star hx_star_A using 1;
        grind

end AristotleLemmas

lemma symmetric_equality (Δ : ℕ) (hΔ : 2 ≤ Δ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let s := a * a
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := by nlinarith
    let ξ := xi_Δ Δ hΔ s hs₀ hs₁
    let x_star := (a * ξ ^ Δ - 1) / Δ
    x_star > 0 ∧ Φ_Δ Δ a a = Psi_Delta Δ hΔ s hs₀ hs₁ + (2 * a) / Δ := by
  /-
  PROOF STRATEGY:
  1. ROOT INEQUALITY:
     - Let s := a^2. Recall ξ = xi_Δ Δ hΔ s hs₀ hs₁ is the unique root > 1 of
       f(X) = (Δ + 1)sX^{2Δ} - ΔX^{Δ+1} - 1 = 0[cite: 167, 169, 598, 600].
     - Show that (Δ + 1) * s * ξ^{2Δ} = Δ * ξ^{Δ+1} + 1.
     - Since Δ ≥ 2 and ξ > 1, then Δ * ξ^{Δ+1} + 1 > Δ + 1.
     - This implies (Δ + 1) * s * ξ^{2Δ} > Δ + 1, which simplifies to s * ξ^{2Δ} > 1.
     - Taking the square root gives a * ξ^Δ > 1[cite: 183, 615].

  2. POSITIVITY OF THE CRITICAL POINT:
     - By definition, x_star = (a * ξ^Δ - 1) / Δ.
     - From Step 1, a * ξ^Δ > 1 implies x_star > 0[cite: 183, 615].
     - By symmetry (a₁ = a₂ = a), x_star = y_star.

  3. INTERIOR SUPREMUM (USE A_d_gradient_at_critical):
     - Recall Φ_Δ Δ a a = sup_{x,y ≥ 0} (A_{Δ+1}(x,y)^{1/(Δ+1)} - ax - ay)[cite: 160, 588].
     - Since (x_star, y_star) is in the interior of the nonnegative quadrant (x_star, y_star > 0)
       and satisfies the first-order conditions (partial derivatives match a),
       the supremum is exactly the value at this critical point[cite: 184, 616].

  4. VALUE VERIFICATION (USE variational_algebraic_identity):
     - Compute the value: ξ - a * x_star - a * y_star.
     - Substitute x_star and y_star: ξ - 2 * a * ((a * ξ^Δ - 1) / Δ).
     - Rearrange the terms: (ξ - (2 / Δ) * a^2 * ξ^Δ) + (2 * a / Δ).
     - Recognizing a^2 = s, the parenthetical term is exactly Psi_Delta Δ hΔ s hs₀ hs₁[cite: 181, 613].
     - This confirms Φ_Δ Δ a a = Psi_Delta Δ hΔ s hs₀ hs₁ + (2 * a) / Δ[cite: 184, 616].
  -/
  refine' ⟨ _, le_antisymm _ _ ⟩
  all_goals generalize_proofs at *;
  · convert symmetric_critical_point_pos Δ hΔ a ha₀ ha₁ using 1;
  · have h := symmetric_pointwise_upper_bound Δ hΔ a ha₀ ha₁;
    refine' ciSup_le fun x => ?_;
    by_cases hx : 0 ≤ x <;> simp_all +decide [ ciSup_eq_ite ];
    · refine' ciSup_le fun y => _;
      split_ifs <;> [ linarith [ h x y hx ( by linarith ) ] ; linarith [ show 0 ≤ Psi_Delta Δ hΔ ( a * a ) (by positivity) (by nlinarith) + 2 * a / Δ from by
                                                                          specialize h 0 0 ; norm_num at h;
                                                                          exact le_trans ( Real.rpow_nonneg ( by unfold A_d; norm_num ) _ ) h ] ];
    · rw [ if_neg (not_le.mpr hx) ];
      have := h 0 0 le_rfl le_rfl; norm_num [ A_d ] at this;
      linarith;
  · -- Let's choose any $x, y \geq 0$ and show that $f(x, y) \leq C$.
    have h_le_C : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → (A_d (Δ + 1) x y) ^ (1 / (Δ + 1 : ℝ)) - a * x - a * y ≤ Psi_Delta Δ hΔ (a * a) (by linarith) (by linarith) + 2 * a / (Δ : ℝ) := by
      convert symmetric_pointwise_upper_bound Δ hΔ a ha₀ ha₁ using 1;
    have h_eq_C : (A_d (Δ + 1) ((a * xi_Δ Δ hΔ (a * a) (by linarith) (by linarith) ^ Δ - 1) / Δ) ((a * xi_Δ Δ hΔ (a * a) (by linarith) (by linarith) ^ Δ - 1) / Δ)) ^ (1 / (Δ + 1 : ℝ)) - a * ((a * xi_Δ Δ hΔ (a * a) (by linarith) (by linarith) ^ Δ - 1) / Δ) - a * ((a * xi_Δ Δ hΔ (a * a) (by linarith) (by linarith) ^ Δ - 1) / Δ) = Psi_Delta Δ hΔ (a * a) (by linarith) (by linarith) + 2 * a / (Δ : ℝ) := by
      convert symmetric_value_at_critical Δ hΔ a ha₀ ha₁ using 1;
    refine' le_trans _ ( le_ciSup _ ( ( a * xi_Δ Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) ^ Δ - 1 ) / Δ ) );
    · rw [ @ciSup_eq_ite ];
      split_ifs <;> norm_num at *;
      · refine' le_trans _ ( le_ciSup _ ( ( a * xi_Δ Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) ^ Δ - 1 ) / Δ ) );
        · rw [ @ciSup_eq_ite ] ; aesop;
        · refine' ⟨ Psi_Delta Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) + 2 * a / ( Δ : ℝ ), Set.forall_mem_range.2 fun y => _ ⟩;
          rw [ @ciSup_eq_ite ] ; norm_num;
          split_ifs <;> [ linarith [ h_le_C ( ( a * xi_Δ Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) ^ Δ - 1 ) / Δ ) y ( by linarith ) ( by linarith ) ] ; linarith [ show 0 ≤ Psi_Delta Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) + 2 * a / ( Δ : ℝ ) from by
                                                                                                                                                                          have := h_le_C 0 0; norm_num at this;
                                                                                                                                                                          exact le_trans ( Real.rpow_nonneg ( by unfold A_d; norm_num ) _ ) this ] ];
      · have h_pos : 0 < (a * xi_Δ Δ hΔ (a * a) (by linarith) (by linarith) ^ Δ - 1) / Δ := by
          apply symmetric_critical_point_pos Δ hΔ a ha₀ ha₁;
        linarith;
    · refine' ⟨ Psi_Delta Δ hΔ ( a * a ) ( by linarith ) ( by linarith ) + 2 * a / ( Δ : ℝ ), Set.forall_mem_range.2 fun x => _ ⟩;
      rw [ @ciSup_eq_ite ];
      split_ifs <;> norm_num;
      · refine' ciSup_le fun y => _;
        rw [ @ciSup_eq_ite ] ; norm_num;
        split_ifs <;> norm_num at * ; aesop;
        contrapose! h_le_C;
        refine' ⟨ 0, 0, _, _, _ ⟩ <;> norm_num;
        exact h_le_C.trans_le ( Real.rpow_nonneg ( by unfold A_d; norm_num ) _ );
      · refine' le_trans _ ( h_le_C 0 0 ( by norm_num ) ( by norm_num ) ) ; norm_num;
        unfold A_d; norm_num


/--
**Lemma 3.5** `lem:Phi-upper-bound`
Φ_Δ(a₁, a₂) is essentially upper bounded in terms of a₁a₂.

Statement:
There is a function \(\Psi_\Delta\colon(0,1)\to\RR\) such that
for all \(a_1,a_2>0\) with \(a_1a_2<1\),
\[
    \Phi_\Delta(a_1,a_2) \le \Psi_\Delta(a_1a_2) + (a_1+a_2)/\Delta.
\]
Moreover, if \(a_1=a_2\), then equality holds.

Ψ_Δ is explicitly defined in Psi_Delta.
-/
lemma Phi_upper_bound (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ)
    (ha₁ : a₁ > 0) (ha₂ : a₂ > 0) (h_prod : a₁ * a₂ < 1) :
    let s := a₁ * a₂
    let hs₀ : 0 < s := by simpa [s] using (mul_pos ha₁ ha₂)
    let hs₁ : s < 1 := by simpa [s] using h_prod
    let Ψ_Δ := Psi_Delta Δ hΔ
    let Ψ_Δ_s := Ψ_Δ s hs₀ hs₁
    Φ_Δ Δ a₁ a₂ ≤ Ψ_Δ_s + (a₁ + a₂) / (Δ : ℝ) ∧
    (a₁ = a₂ → Φ_Δ Δ a₁ a₂ = Ψ_Δ_s + (a₁ + a₂) / (Δ : ℝ)) := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. ROOT IDENTIFICATION:
     - Let ξ := xi_Δ Δ hΔ s hs₀ hs₁. Use xi_unique_zero to establish that ξ is
       the unique root in (1, ∞) for the characteristic polynomial[cite: 169, 600].
     - This root identity (Δ + 1) * s * ξ^(2Δ) - Δ * ξ^(Δ+1) - 1 = 0 will be
       central to all subsequent algebraic simplifications[cite: 167, 598].

  2. CRITICAL POINT MAPPING:
     - Define the potential maximum (x_star, y_star) using Equation 3.8[cite: 174, 605].
     - Invoke 'critical_point_in_Ω' to prove that this point satisfies the partition
       function identity A_{Δ+1}(x_star, y_star) = ξ^{Δ+1} and resides within the
       geometrically safe convex domain Ω[cite: 177, 607].

  3. ESTABLISHING THE UPPER BOUND:
     - Apply 'variational_upper_bound'. This lemma uses the concavity of A_{Δ+1}^{1/(Δ+1)}
       (Lemma 3.1) to show the tangent plane at (x_star, y_star) bounds the
       partition function variation across the entire nonnegative quadrant[cite: 180, 611].
     - The algebraic conclusion of this bound matches the first term of our
       goal: Ψ_Δ(s) + (a₁ + a₂)/Δ[cite: 181, 613].

  4. SYMMETRIC EQUALITY CASE:
     - For the condition a₁ = a₂, invoke 'symmetric_equality'[cite: 184, 616].
     - This confirms that x_star = y_star > 0, meaning the critical point is
       in the interior of the domain, ensuring the supremum is exactly
       the value computed at (x_star, y_star)[cite: 183, 615].
  -/
  -- First, we show that Φ_Δ(a₁, a₂) ≤ Ψ_Δ(a₁a₂) + (a₁ + a₂)/Δ.
  have h_le : let s := a₁ * a₂;
    let hs₀ : 0 < s := by positivity;
    let hs₁ : s < 1 := h_prod;
    let Ψ_Δ := Psi_Delta Δ hΔ;
    let Ψ_Δ_s := Ψ_Δ s hs₀ hs₁;
    Φ_Δ Δ a₁ a₂ ≤ Ψ_Δ_s + (a₁ + a₂) / (Δ : ℝ) := by
      field_simp;
      have := variational_upper_bound Δ hΔ a₁ a₂ ha₁ ha₂ h_prod;
      have := this 0 0 1 ; norm_num at this;
      have := this ( by unfold A_d; norm_num );
      refine' le_trans ( mul_le_mul_of_nonneg_right ( ciSup_le fun x => _ ) ( Nat.cast_nonneg _ ) ) _;
      exact Psi_Delta Δ hΔ ( a₁ * a₂ ) ( by positivity ) h_prod + ( a₁ + a₂ ) / Δ;
      · rw [ @ciSup_eq_ite ];
        split_ifs <;> norm_num;
        · refine' ciSup_le fun y => _;
          rw [ @ciSup_eq_ite ] ; norm_num;
          field_simp;
          split_ifs <;> norm_num at *;
          · rename_i hx hy;
            rename_i h;
            have := h x y hy hx;
            nlinarith [ mul_div_cancel₀ ( a₁ + a₂ ) ( by positivity : ( Δ : ℝ ) ≠ 0 ) ];
          · contrapose! this;
            refine' ⟨ 0, 0, 1, _, 0, 0, _, _, _ ⟩ <;> norm_num;
            · unfold A_d; norm_num;
            · rw [ add_div', div_lt_iff₀ ] <;> try positivity;
              exact lt_of_lt_of_le ( by linarith ) ( mul_nonneg ( Real.rpow_nonneg ( by unfold A_d; norm_num ) _ ) ( Nat.cast_nonneg _ ) );
        · have := this 0 0; norm_num at this;
          exact le_trans ( Real.rpow_nonneg ( by unfold A_d; norm_num ) _ ) this;
      · rw [ add_mul, div_mul_cancel₀ _ ( by positivity ) ];
  refine ⟨ h_le, ?_ ⟩;
  intro h_eq;
  convert symmetric_equality Δ hΔ a₁ ha₁ _ |> And.right using 1;
  all_goals subst h_eq; ring_nf;
  nlinarith
