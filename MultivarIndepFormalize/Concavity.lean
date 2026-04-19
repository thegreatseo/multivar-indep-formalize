import MultivarIndepFormalize.Definitions

/-!
# Concavity of A_{d+1}(x,y)^{1/(d+1)}

**Lemma 3.1** `lem:Ad+1-concave` (`A_d_pow_dinv_concave`)

Contains the Hessian conditions and the proof that `A_{d+1}(x,y)^{1/(d+1)}`
is concave on any convex subset where `A_{d+1} > 0`.
-/

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open Real

noncomputable section

/-!
## Hessian conditions
-/

/--
Algebraic inequality related to the Hessian of A_{d+1}.
-/
lemma A_d_hessian_cond (d : ℕ) (hd : d ≥ 1) (x y u w : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    let A := A_d (d + 1) x y
    let dx := (d + 1 : ℝ) * d * y + (d + 1)
    let dy := (d + 1 : ℝ) * d * x + (d + 1)
    let dxy := (d + 1 : ℝ) * d
    A * (2 * dxy * u * w) ≤ (d / (d + 1 : ℝ)) * (u * dx + w * dy) ^ 2 := by
      -- If $uw \leq 0$, LHS is negative (since $XY \geq 1$), RHS positive. OK.
      by_cases h_uw : u * w ≤ 0;
      · norm_num [ A_d ];
        exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( by positivity ) ( by nlinarith [ mul_nonneg ( Nat.cast_nonneg d : ( 0 :ℝ ) ≤ d ) ( mul_nonneg ( Nat.cast_nonneg d : ( 0 :ℝ ) ≤ d ) ( mul_nonneg ( Nat.cast_nonneg d : ( 0 :ℝ ) ≤ d ) ( Nat.cast_nonneg d : ( 0 :ℝ ) ≤ d ) ) ) ] ) ) ( by positivity );
      · -- If $uw > 0$, we use $(uX + wY)^2 \ge 4 uw XY$.
        have h_am_gm : (u * ((d + 1) * d * y + (d + 1)) + w * ((d + 1) * d * x + (d + 1)))^2 ≥ 4 * u * w * ((d + 1) * d * x + (d + 1)) * ((d + 1) * d * y + (d + 1)) := by
          linarith [ sq_nonneg ( u * ( ( d + 1 ) * d * y + ( d + 1 ) ) - w * ( ( d + 1 ) * d * x + ( d + 1 ) ) ) ];
        norm_num [ A_d ] at *;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) h_uw.le ] ;

/--
Generalized Hessian condition for A_{d+1} requiring only A >= 0.
-/
lemma A_d_hessian_cond_general (d : ℕ) (hd : d ≥ 1) (x y u w : ℝ)
    (hA : A_d (d + 1) x y ≥ 0) :
    let A := A_d (d + 1) x y
    let dx := (d + 1 : ℝ) * d * y + (d + 1)
    let dy := (d + 1 : ℝ) * d * x + (d + 1)
    let dxy := (d + 1 : ℝ) * d
    A * (2 * dxy * u * w) ≤ (d / (d + 1 : ℝ)) * (u * dx + w * dy) ^ 2 := by
      field_simp;
      unfold A_d at hA ⊢;
      rcases d with ( _ | _ | d ) <;> norm_num at *;
      · cases le_or_gt 0 ( x + 1 ) <;> cases le_or_gt 0 ( y + 1 ) <;> nlinarith [ sq_nonneg ( u * ( y + 1 ) - w * ( x + 1 ) ) ];
      · by_cases hu : u ≥ 0 <;> by_cases hw : w ≥ 0 <;> try nlinarith [ sq_nonneg ( u * ( ( d + 1 + 1 ) * y + 1 ) - w * ( ( d + 1 + 1 ) * x + 1 ) ) ];
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( by nlinarith ) ( by nlinarith ) ) ( sq_nonneg _ );
        · nlinarith [ sq_nonneg ( u * ( ( d + 1 + 1 ) * y + 1 ) + w * ( ( d + 1 + 1 ) * x + 1 ) ), mul_le_mul_of_nonneg_left ( le_of_not_ge hu ) hw ]

/-!
## Concavity of f^{1/(d+1)}
-/

/--
Sufficient condition for the concavity of f^(1/(d+1)) based on the second derivative of f.
-/
lemma concave_rpow_of_condition (d : ℕ) (hd : d ≥ 1) (f : ℝ → ℝ) (S : Set ℝ)
    (hS : Convex ℝ S) (hf_pos : ∀ t ∈ S, f t > 0)
    (hf_diff : DifferentiableOn ℝ f S) (hf_diff2 : DifferentiableOn ℝ (deriv f) (interior S))
    (h_cond : ∀ t ∈ interior S, f t * deriv (deriv f) t ≤ (d / (d + 1 : ℝ)) * (deriv f t) ^ 2) :
    ConcaveOn ℝ S (fun t => f t ^ (1 / (d + 1 : ℝ))) := by
      apply_rules [ concaveOn_of_deriv2_nonpos ];
      · exact ContinuousOn.rpow ( hf_diff.continuousOn ) continuousOn_const fun t ht => Or.inl <| ne_of_gt <| hf_pos t ht;
      · exact DifferentiableOn.rpow ( hf_diff.mono interior_subset ) ( differentiableOn_const _ ) ( by intro t ht; exact ne_of_gt ( hf_pos t ( interior_subset ht ) ) );
      · refine' DifferentiableOn.congr _ fun t ht => _;
        · use fun t => ( 1 / ( d + 1 : ℝ ) ) * f t ^ ( ( 1 : ℝ ) / ( d + 1 ) - 1 ) * deriv f t;
        · refine' DifferentiableOn.mul ( DifferentiableOn.mul ( differentiableOn_const _ ) ( DifferentiableOn.rpow ( hf_diff.mono <| interior_subset ) ( differentiableOn_const _ ) _ ) ) hf_diff2;
          exact fun x hx => ne_of_gt <| hf_pos x <| interior_subset hx;
        · convert HasDerivAt.deriv ( HasDerivAt.rpow_const ( hf_diff.hasDerivAt ( Filter.mem_of_superset ( IsOpen.mem_nhds ( isOpen_interior ) ht ) fun x hx => interior_subset hx ) ) _ ) using 1 <;> norm_num;
          · ring;
          · exact Or.inl <| ne_of_gt <| hf_pos t <| interior_subset ht;
      · intro t ht;
        have hg'' : deriv^[2] (fun t => f t ^ (1 / (d + 1) : ℝ)) t = (1 / (d + 1) : ℝ) * (1 / (d + 1) - 1) * (f t) ^ ((1 / (d + 1) : ℝ) - 2) * (deriv f t) ^ 2 + (1 / (d + 1) : ℝ) * (f t) ^ ((1 / (d + 1) : ℝ) - 1) * deriv (deriv f) t := by
          convert HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq _ ?_ ) using 1;
          · use fun t => ( 1 / ( d + 1 : ℝ ) ) * f t ^ ( 1 / ( d + 1 : ℝ ) - 1 ) * deriv f t;
          · convert HasDerivAt.mul ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.rpow_const ( hf_diff.hasDerivAt <| ?_ ) ?_ ) ) ( hf_diff2.hasDerivAt <| ?_ ) using 1 <;> norm_num;
            · ring_nf;
            · exact mem_interior_iff_mem_nhds.mp ht;
            · exact Or.inl <| ne_of_gt <| hf_pos t <| interior_subset ht;
            · exact mem_interior_iff_mem_nhds.mp ht;
          · filter_upwards [ IsOpen.mem_nhds ( isOpen_interior ) ht ] with u hu;
            convert HasDerivAt.deriv ( HasDerivAt.rpow_const ( hf_diff.hasDerivAt ( Filter.mem_of_superset ( IsOpen.mem_nhds ( isOpen_interior ) hu ) interior_subset ) ) _ ) using 1 <;> norm_num [ ne_of_gt ( hf_pos u ( interior_subset hu ) ) ] ; ring;
        rw [hg''];
        have := h_cond t ht;
        suffices h_factor : (1 / (d + 1) : ℝ) * (1 / (d + 1) - 1) * (deriv f t) ^ 2 + (1 / (d + 1) : ℝ) * f t * deriv (deriv f) t ≤ 0 by
          convert mul_nonpos_of_nonpos_of_nonneg h_factor ( Real.rpow_nonneg ( le_of_lt ( hf_pos t ( interior_subset ht ) ) ) ( 1 / ( d + 1 : ℝ ) - 2 ) ) using 1 ; ring_nf;
          rw [ show ( -1 + ( 1 + d : ℝ ) ⁻¹ ) = ( -2 + ( 1 + d : ℝ ) ⁻¹ ) + 1 by ring, Real.rpow_add_one ( ne_of_gt ( hf_pos t ( interior_subset ht ) ) ) ] ; ring;
        field_simp;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ] at this <;> nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ]

/-!
## Main concavity result
-/

/--
**Lemma 3.1** `lem:Ad+1-concave`
A_{d+1}(x,y)^{1/(d+1)} is concave.

For `d ≥ 2`, `A_{d+1}(x,y)^{1/(d+1)}` is concave on
any convex subset of `{(x,y) ∈ ℝ² : A_{d+1}(x,y) > 0}`.
-/
lemma A_d_pow_dinv_concave (d : ℕ) (hd : d ≥ 2) (Ω : Set (ℝ × ℝ))
    (hΩ_conv : Convex ℝ Ω)
    (hΩ_pos : ∀ p ∈ Ω, A_d (d + 1) p.1 p.2 > 0) :
    ConcaveOn ℝ Ω (fun p => (A_d (d + 1) p.1 p.2) ^ (1 / ((d : ℝ) + 1))) := by
  have h_h : ∀ p q : ℝ × ℝ, p ∈ Ω → q ∈ Ω → ∀ t ∈ Set.Icc 0 1, A_d (d + 1) ((1 - t) * p.1 + t * q.1) ((1 - t) * p.2 + t * q.2) > 0 := by
    exact fun p q hp hq t ht => hΩ_pos _ ( hΩ_conv hp hq ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) );
  have h_concave : ∀ p q : ℝ × ℝ, p ∈ Ω → q ∈ Ω → ConcaveOn ℝ (Set.Icc 0 1) (fun t : ℝ => (A_d (d + 1) ((1 - t) * p.1 + t * q.1) ((1 - t) * p.2 + t * q.2)) ^ (1 / (d + 1 : ℝ))) := by
    intros p q hp hq
    have h_h_deriv : ∀ t ∈ Set.Ioo 0 1, deriv (fun t => A_d (d + 1) ((1 - t) * p.1 + t * q.1) ((1 - t) * p.2 + t * q.2)) t = (q.1 - p.1) * ((d + 1) * d * ((1 - t) * p.2 + t * q.2) + (d + 1)) + (q.2 - p.2) * ((d + 1) * d * ((1 - t) * p.1 + t * q.1) + (d + 1)) := by
      unfold A_d; norm_num [ sub_mul ] ; ring_nf;
      norm_num;
    have h_h_deriv2 : ∀ t ∈ Set.Ioo 0 1, deriv^[2] (fun t => A_d (d + 1) ((1 - t) * p.1 + t * q.1) ((1 - t) * p.2 + t * q.2)) t = 2 * (q.1 - p.1) * (q.2 - p.2) * ((d + 1) * d) := by
      intro t ht;
      convert HasDerivAt.deriv ( HasDerivAt.congr_of_eventuallyEq _ ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds ht.1 ht.2 ) fun x hx => h_h_deriv x hx ) ) using 1;
      convert HasDerivAt.add ( HasDerivAt.const_mul _ <| HasDerivAt.add ( HasDerivAt.const_mul _ <| HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id' t |> HasDerivAt.const_sub _ ) <| hasDerivAt_const _ _ ) <| hasDerivAt_id' t |> HasDerivAt.mul_const <| _ ) <| hasDerivAt_const _ _ ) ( HasDerivAt.const_mul _ <| HasDerivAt.add ( HasDerivAt.const_mul _ <| HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_id' t |> HasDerivAt.const_sub _ ) <| hasDerivAt_const _ _ ) <| hasDerivAt_id' t |> HasDerivAt.mul_const <| _ ) <| hasDerivAt_const _ _ ) using 1 ; ring;
    apply_rules [ concave_rpow_of_condition ];
    · linarith;
    · exact convex_Icc _ _;
    · unfold A_d;
      fun_prop;
    · norm_num +zetaDelta at *;
      exact DifferentiableOn.congr ( by exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( by exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( by exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ) ( DifferentiableOn.mul ( differentiableOn_id ) ( differentiableOn_const _ ) ) ) ) ( differentiableOn_const _ ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) ( by exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_const _ ) ( by exact DifferentiableOn.add ( DifferentiableOn.mul ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ) ( DifferentiableOn.mul ( differentiableOn_id ) ( differentiableOn_const _ ) ) ) ) ( differentiableOn_const _ ) ) ) ) fun t ht => h_h_deriv t ht.1 ht.2;
    · simp +zetaDelta at *;
      intro t ht ht'; rw [ h_h_deriv2 t ht ht', h_h_deriv t ht ht' ] ; rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> try positivity;
      convert A_d_hessian_cond_general d ( by linarith ) ( ( 1 - t ) * p.1 + t * q.1 ) ( ( 1 - t ) * p.2 + t * q.2 ) ( q.1 - p.1 ) ( q.2 - p.2 ) ( le_of_lt ( h_h p.1 p.2 q.1 q.2 hp hq t ht.le ht'.le ) ) |> fun x => mul_le_mul_of_nonneg_right x ( by positivity : ( 0 : ℝ ) ≤ ( d + 1 ) ) using 1 ; ring;
      rw [ div_mul_eq_mul_div, div_mul_cancel₀ _ ( by positivity ) ];
  constructor <;> norm_num;
  · assumption;
  · intro a b ha c d hc x y hx hy hxy; specialize h_concave ( a, b ) ( c, d ) ha hc; simp_all +decide [ ConcaveOn ] ;
    convert h_concave.2 ( show 0 ≤ 0 by norm_num ) ( show 0 ≤ 1 by norm_num ) ( show 0 ≤ 1 by norm_num ) ( show 1 ≤ 1 by norm_num ) hx hy hxy using 1 <;> ring;
    rw [ ← eq_sub_iff_add_eq' ] at hxy ; subst_vars ; ring

end
