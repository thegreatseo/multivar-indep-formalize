/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: df26e493-eebc-40db-b12b-a81c1261bbf2

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma A_d_pow_dinv_concave (d : ℕ) (hd : d ≥ 2) (Ω : Set (ℝ × ℝ))
    (hΩ_conv : Convex ℝ Ω)
    (hΩ_pos : ∀ p ∈ Ω, A_d (d + 1) p.1 p.2 > 0) :
    ConcaveOn ℝ Ω (fun p => (A_d (d + 1) p.1 p.2) ^ (1 / ((d : ℝ) + 1)))
-/

/-
Lemma 3.1 `lem:Ad+1-concave`: A_{d+1}(x,y)^{1/(d+1)} is concave.
Lemma 3.4 `lem:Sd-log-convex`:  log S_d is convex.
-/

import MultivarIndepFormalize.Definitions

set_option linter.style.longLine false

open Real

noncomputable section

/-
Lemma 3.1 `lem:Ad+1-concave`: A_{d+1}(x,y)^{1/(d+1)} is concave.

Statement:
For \(d\ge2\), \(A_{d+1}(x,y)^{\frac{1}{d+1}}\) is concave on
any convex subset of \(\{(x,y)\in\RR^2 : A_{d+1}(x,y)>0\}\).
-/
noncomputable section AristotleLemmas

/-
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

/-
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
      -- By definition of $A_d$, we know that $A_d (d + 1) x y = (d + 1) * d * x * y + (d + 1) * (x + y) + 1$.
      unfold A_d at hA ⊢;
      rcases d with ( _ | _ | d ) <;> norm_num at *;
      · cases le_or_gt 0 ( x + 1 ) <;> cases le_or_gt 0 ( y + 1 ) <;> nlinarith [ sq_nonneg ( u * ( y + 1 ) - w * ( x + 1 ) ) ];
      · by_cases hu : u ≥ 0 <;> by_cases hw : w ≥ 0 <;> try nlinarith [ sq_nonneg ( u * ( ( d + 1 + 1 ) * y + 1 ) - w * ( ( d + 1 + 1 ) * x + 1 ) ) ];
        · exact le_trans ( mul_nonpos_of_nonneg_of_nonpos ( by nlinarith ) ( by nlinarith ) ) ( sq_nonneg _ );
        · nlinarith [ sq_nonneg ( u * ( ( d + 1 + 1 ) * y + 1 ) + w * ( ( d + 1 + 1 ) * x + 1 ) ), mul_le_mul_of_nonneg_left ( le_of_not_ge hu ) hw ]

/-
Sufficient condition for the concavity of f^(1/(d+1)) based on the second derivative of f.
-/
lemma concave_rpow_of_condition (d : ℕ) (hd : d ≥ 1) (f : ℝ → ℝ) (S : Set ℝ)
    (hS : Convex ℝ S) (hf_pos : ∀ t ∈ S, f t > 0)
    (hf_diff : DifferentiableOn ℝ f S) (hf_diff2 : DifferentiableOn ℝ (deriv f) (interior S))
    (h_cond : ∀ t ∈ interior S, f t * deriv (deriv f) t ≤ (d / (d + 1 : ℝ)) * (deriv f t)^2) :
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
        -- By definition of $g$, we know that its second derivative is given by:
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
        -- Substitute the expression for the second derivative from `hg''`.
        rw [hg''];
        have := h_cond t ht;
        -- Factor out $f(t)^{1/(d+1)-2}$ from the expression.
        suffices h_factor : (1 / (d + 1) : ℝ) * (1 / (d + 1) - 1) * (deriv f t) ^ 2 + (1 / (d + 1) : ℝ) * f t * deriv (deriv f) t ≤ 0 by
          convert mul_nonpos_of_nonpos_of_nonneg h_factor ( Real.rpow_nonneg ( le_of_lt ( hf_pos t ( interior_subset ht ) ) ) ( 1 / ( d + 1 : ℝ ) - 2 ) ) using 1 ; ring;
          rw [ show ( -1 + ( 1 + d : ℝ ) ⁻¹ ) = ( -2 + ( 1 + d : ℝ ) ⁻¹ ) + 1 by ring, Real.rpow_add_one ( ne_of_gt ( hf_pos t ( interior_subset ht ) ) ) ] ; ring;
        field_simp;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ] at this <;> nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ]

end AristotleLemmas

lemma A_d_pow_dinv_concave (d : ℕ) (hd : d ≥ 2) (Ω : Set (ℝ × ℝ))
    (hΩ_conv : Convex ℝ Ω)
    (hΩ_pos : ∀ p ∈ Ω, A_d (d + 1) p.1 p.2 > 0) :
    ConcaveOn ℝ Ω (fun p => (A_d (d + 1) p.1 p.2) ^ (1 / ((d : ℝ) + 1))) := by
  -- For any $p, q \in \Omega$, let $h(t) = A_{d+1}((1-t)p + tq)$.
  have h_h : ∀ p q : ℝ × ℝ, p ∈ Ω → q ∈ Ω → ∀ t ∈ Set.Icc 0 1, A_d (d + 1) ((1 - t) * p.1 + t * q.1) ((1 - t) * p.2 + t * q.2) > 0 := by
    exact fun p q hp hq t ht => hΩ_pos _ ( hΩ_conv hp hq ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) );
  -- By Lemma 3.1, $h(t)^{1/(d+1)}$ is concave on $[0,1]$.
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

/-
The set log S_d defined as {(log a₀, log a₁, log a₂) : (a₀, a₁, a₂) ∈ S_d}.
Matches the definition in Section 3.1.
-/
def log_S_d (d : ℕ) : Set (ℝ × ℝ × ℝ) :=
  { w | ∃ v ∈ S_d d, w = (log v.1, log v.2.1, log v.2.2) }

/- Aristotle failed to find a proof. -/
/-
Lemma 3.4 `lem:Sd-log-convex`:  log S_d is convex.

Statement:
For \(d\ge2\), \(\log\calS_d\) is convex.

PROVIDED SOLUTION:

We prove the multiplicative midpoint property for `S_d d`:
if `a = (a0,a1,a2) ∈ S_d d` and `b = (b0,b1,b2) ∈ S_d d`, then
`c := (Real.sqrt (a0*b0), Real.sqrt (a1*b1), Real.sqrt (a2*b2)) ∈ S_d d`.
(Then use the standard equivalence: a set of positive vectors is log-convex iff it is closed
under componentwise geometric means / multiplicative midpoints.)

--------------------------------------------
Step 0: recall the definition we must prove
--------------------------------------------
`(t0,t1,t2) ∈ S_d d` means:
(1) `t0 > 0`, `t1 > 0`, `t2 > 0`, and
(2) for all `x y` with `x ≥ 0`, `y ≥ 0`,
    `t0 + t1*x + t2*y ≥ (A_d (d+1) x y) ^ (1 / ((d:ℝ)+1))`.

So for `c` we need: positivity is immediate since `a_i,b_i>0`, hence `sqrt(a_i*b_i)>0`,
and then we prove the inequality in (2).

---------------------------------------------------------
Step 1: introduce the homogenization `h` of `A_d (d+1)`
---------------------------------------------------------
Define for `w x y : ℝ`:
`h(w,x,y) := ((d+1 : ℝ) * (d : ℝ)) * w^(d-1) * x * y
           + (d+1 : ℝ) * w^d * x
           + (d+1 : ℝ) * w^d * y
           + w^(d+1)`.

(Here `w^n` is the usual nat power on ℝ; we assume `d ≥ 2` so `d-1` behaves well.)

Key algebra fact (for `w>0`):
`h(w,x,y) = w^(d+1) * A_d (d+1) (x/w) (y/w)`.
(Expand `A_d (d+1)`: it is `(d+1)*d*(x/w)*(y/w) + (d+1)*((x/w)+(y/w)) + 1`,
and distribute `w^(d+1)`.)

Also note `h(0,x,y)=0` when `d ≥ 2`.

--------------------------------------------------------------
Step 2: derive the “homogeneous” characterization of membership
--------------------------------------------------------------
Lemma (derive from the definition of `S_d`):
If `a=(a0,a1,a2) ∈ S_d d`, then for all `w x y ≥ 0`,
  `a0*w + a1*x + a2*y ≥ (h(w,x,y)) ^ (1 / ((d:ℝ)+1))`.

Proof sketch:
- If `w=0`, RHS is `0` (since `h(0,x,y)=0`), and LHS is ≥ 0 because `a0>0` and `x,y≥0`.
- If `w>0`, rewrite
  `a0*w + a1*x + a2*y = w * (a0 + a1*(x/w) + a2*(y/w))`.
  Apply the defining inequality of `S_d` to `(x/w, y/w)` (still ≥0),
  then use the algebra identity from Step 1 to convert
  `w * (A_d (d+1) (x/w) (y/w))^(1/(d+1))`
  into `(h(w,x,y))^(1/(d+1))`.

(Implementation note: in Lean, treat the exponent as `Real.rpow`; you’ll want facts like
`Real.mul_rpow` / `Real.rpow_mul` under nonnegativity assumptions.)

----------------------------------------------------------
Step 3: prove closure under geometric mean using Step 2
----------------------------------------------------------
Let `a,b ∈ S_d d` and fix arbitrary `w x y ≥ 0`.
Define the scaled triples:
  `w1 := Real.sqrt (b0/a0) * w`,  `x1 := Real.sqrt (b1/a1) * x`,  `y1 := Real.sqrt (b2/a2) * y`,
  `w2 := Real.sqrt (a0/b0) * w`,  `x2 := Real.sqrt (a1/b1) * x`,  `y2 := Real.sqrt (a2/b2) * y`.

Then:
(1) `c0*w + c1*x + c2*y = a0*w1 + a1*x1 + a2*y1`  (by pulling the scaling into the coefficients),
    so by Step 2 applied to `a`,
    `c0*w + c1*x + c2*y ≥ (h(w1,x1,y1))^(1/(d+1))`.
(2) Symmetrically,
    `c0*w + c1*x + c2*y = b0*w2 + b1*x2 + b2*y2 ≥ (h(w2,x2,y2))^(1/(d+1))`.

Now it suffices to prove the Cauchy–Schwarz estimate:
  `h(w1,x1,y1) * h(w2,x2,y2) ≥ h(w,x,y)^2`.
Reason: set `t := c0*w + c1*x + c2*y` and `u := h(w1,x1,y1)^(1/(d+1))`, `v := h(w2,x2,y2)^(1/(d+1))`.
From (1)(2), `t ≥ u` and `t ≥ v`, hence `t ≥ Real.sqrt (u*v)` (using nonnegativity),
and then use the product inequality to get `u*v ≥ h(w,x,y)^(2/(d+1))`.

Why does `h(w,x,y)` appear?
Because the scalings cancel:
`w1*w2 = (sqrt(b0/a0)*w) * (sqrt(a0/b0)*w) = w^2`, and similarly `x1*x2 = x^2`, `y1*y2 = y^2`.
So the “geometric midpoint triple”
  `v := (Real.sqrt (w1*w2), Real.sqrt (x1*x2), Real.sqrt (y1*y2))`
is exactly `(w,x,y)`.

---------------------------------------------------------
Step 4: Cauchy–Schwarz on the (finite) monomial expansion of h
---------------------------------------------------------
Write `h` as a sum of four monomials with positive coefficients:
  `h(w,x,y) = T_xy(w,x,y) + T_x(w,x,y) + T_y(w,x,y) + T_1(w,x,y)`,
where
  `T_xy = ((d+1)*d) * w^(d-1) * x * y`,
  `T_x  = (d+1) * w^d * x`,
  `T_y  = (d+1) * w^d * y`,
  `T_1  = w^(d+1)`.

Then with `u1=(w1,x1,y1)` and `u2=(w2,x2,y2)` and `v=(w,x,y)`:
  `h(v) = Σ_i sqrt(T_i(u1)) * sqrt(T_i(u2))`
because each monomial satisfies `T_i(v) = sqrt(T_i(u1) * T_i(u2))` (using `w1*w2=w^2`, etc).
Apply Cauchy–Schwarz to the 4-term sum:
  `(Σ_i sqrt(T_i(u1)) * sqrt(T_i(u2)))^2 ≤ (Σ_i T_i(u1)) * (Σ_i T_i(u2))`,
i.e. `h(v)^2 ≤ h(u1) * h(u2)`.

---------------------------------------------------------
Step 5: conclude membership of c in S_d d
---------------------------------------------------------
From Steps 3–4 we obtain for all `w,x,y ≥ 0`:
  `c0*w + c1*x + c2*y ≥ (h(w,x,y))^(1/(d+1))`.
Specialize to `w=1` and use `h(1,x,y) = A_d (d+1) x y` to get:
  `c0 + c1*x + c2*y ≥ (A_d (d+1) x y)^(1/(d+1))`,
which is exactly the inequality required by `S_d d`.
Together with positivity of coordinates, this shows `c ∈ S_d d`.

This proves log-convexity (convexity of the log-image).
-/
lemma Sd_convex (d : ℕ) (hd : d ≥ 2) :
    Convex ℝ (log_S_d d) := by
  sorry
