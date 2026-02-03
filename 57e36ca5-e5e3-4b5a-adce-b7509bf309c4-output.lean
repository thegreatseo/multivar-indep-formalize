/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 57e36ca5-e5e3-4b5a-adce-b7509bf309c4

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma Sd_convex (d : ℕ) (hd : d ≥ 2) :
    Convex ℝ (log_S_d d)

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
**Lemma 3.1** `lem:Ad+1-concave`
A_{d+1}(x,y)^{1/(d+1)} is concave.

**Lemma 3.4** `lem:Sd-log-convex`
log S_d is convex.
-/

-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions

set_option linter.style.longLine false

open Real

noncomputable section

/-
**Lemma 3.1** `lem:Ad+1-concave`
A_{d+1}(x,y)^{1/(d+1)} is concave.

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
      convert A_d_hessian_cond_general d ( by linarith ) ( ( 1 - t ) * p.1 + t * q.1 ) ( ( 1 - t ) * p.2 + t * q.2 ) ( q.1 - p.1 ) ( q.2 - p.2 ) ( le_of_lt ( h_h p.1 p.2 q.1 q.2 hp hq t ht.le ht'.le ) ) |> fun x => mul_le_mul_of_nonneg_right x ( by positivity : ( 0 : ℝ ) ≤ ( d + 1 ) ) using 1 ;
      · ring;
      · rw [ div_mul_eq_mul_div, div_mul_cancel₀ _ ( by positivity ) ];
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
noncomputable section AristotleLemmas

/-
Definition of the homogenized polynomial h(w, x, y) used in the proof of log-convexity of S_d.
-/
noncomputable def h_hom (d : ℕ) (w x y : ℝ) : ℝ :=
  ((d : ℝ) + 1) * d * w ^ (d - 1) * x * y + ((d : ℝ) + 1) * w ^ d * (x + y) + w ^ (d + 1)

/-
Non-negativity of h_hom for non-negative inputs.
-/
lemma h_hom_nonneg (d : ℕ) (w x y : ℝ) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ h_hom d w x y := by
      unfold h_hom;
      positivity

/-
Decomposition of h_hom into 4 terms.
-/
noncomputable def h_hom_term1 (d : ℕ) (w x y : ℝ) : ℝ := ((d : ℝ) + 1) * d * w ^ (d - 1) * x * y
noncomputable def h_hom_term2 (d : ℕ) (w x : ℝ) : ℝ := ((d : ℝ) + 1) * w ^ d * x
noncomputable def h_hom_term3 (d : ℕ) (w y : ℝ) : ℝ := ((d : ℝ) + 1) * w ^ d * y
noncomputable def h_hom_term4 (d : ℕ) (w : ℝ) : ℝ := w ^ (d + 1)

lemma h_hom_eq_sum (d : ℕ) (w x y : ℝ) :
  h_hom d w x y = h_hom_term1 d w x y + h_hom_term2 d w x + h_hom_term3 d w y + h_hom_term4 d w := by
    unfold h_hom h_hom_term1 h_hom_term2 h_hom_term3 h_hom_term4;
    ring

/-
Geometric mean property for the first term of h_hom.
-/
lemma h_hom_term1_geom_mean (d : ℕ) (hd : d ≥ 2) (w1 x1 y1 w2 x2 y2 : ℝ)
    (hw1 : 0 ≤ w1) (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hw2 : 0 ≤ w2) (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) :
    h_hom_term1 d (Real.sqrt (w1 * w2)) (Real.sqrt (x1 * x2)) (Real.sqrt (y1 * y2)) =
    Real.sqrt (h_hom_term1 d w1 x1 y1 * h_hom_term1 d w2 x2 y2) := by
      unfold h_hom_term1;
      rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> first | positivity | ring ; norm_num [ hw1, hx1, hy1, hw2, hx2, hy2 ] ; ring;
      norm_num [ pow_mul', hw1, hx1, hy1, hw2, hx2, hy2 ] ; ring

/-
Geometric mean property for the second term of h_hom.
-/
lemma h_hom_term2_geom_mean (d : ℕ) (hd : d ≥ 2) (w1 x1 w2 x2 : ℝ)
    (hw1 : 0 ≤ w1) (hx1 : 0 ≤ x1) (hw2 : 0 ≤ w2) (hx2 : 0 ≤ x2) :
    h_hom_term2 d (Real.sqrt (w1 * w2)) (Real.sqrt (x1 * x2)) =
    Real.sqrt (h_hom_term2 d w1 x1 * h_hom_term2 d w2 x2) := by
      unfold h_hom_term2;
      rw [ show ( d + 1 : ℝ ) * w1 ^ d * x1 * ( ( d + 1 : ℝ ) * w2 ^ d * x2 ) = ( ( d + 1 : ℝ ) * Real.sqrt ( w1 * w2 ) ^ d * Real.sqrt ( x1 * x2 ) ) ^ 2 by repeat ring <;> norm_num [ hw1, hx1, hw2, hx2, pow_mul', mul_assoc, mul_left_comm, mul_comm ] ] ; rw [ Real.sqrt_sq <| by positivity ]

/-
Geometric mean property for the third term of h_hom.
-/
lemma h_hom_term3_geom_mean (d : ℕ) (hd : d ≥ 2) (w1 y1 w2 y2 : ℝ)
    (hw1 : 0 ≤ w1) (hy1 : 0 ≤ y1) (hw2 : 0 ≤ w2) (hy2 : 0 ≤ y2) :
    h_hom_term3 d (Real.sqrt (w1 * w2)) (Real.sqrt (y1 * y2)) =
    Real.sqrt (h_hom_term3 d w1 y1 * h_hom_term3 d w2 y2) := by
      unfold h_hom_term3; ring;
      rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ] <;> ring <;> try positivity;
      norm_num [ pow_mul', hw1, hy1, hw2, hy2 ] ; ring;
      norm_num [ pow_mul', hw1, hy1, hw2, hy2 ]

/-
Geometric mean property for the fourth term of h_hom.
-/
lemma h_hom_term4_geom_mean (d : ℕ) (hd : d ≥ 2) (w1 w2 : ℝ)
    (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) :
    h_hom_term4 d (Real.sqrt (w1 * w2)) =
    Real.sqrt (h_hom_term4 d w1 * h_hom_term4 d w2) := by
      -- By definition of $h_hom_term4$, we have $h_hom_term4 d w = w^{d+1}$.
      simp [h_hom_term4];
      rw [ ← mul_pow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; push_cast ; ring

/-
Relation between h_hom and A_d.
-/
lemma h_hom_eq_A_d (d : ℕ) (hd : d ≥ 2) (w x y : ℝ) (hw : 0 < w) :
    h_hom d w x y = w ^ (d + 1) * A_d (d + 1) (x / w) (y / w) := by
      unfold h_hom A_d; ring;
      -- Combine like terms and simplify the expression.
      field_simp
      ring;
      cases d <;> norm_num [ pow_succ' ] at * ; ring_nf at *

lemma h_hom_CS (d : ℕ) (hd : d ≥ 2) (w1 x1 y1 w2 x2 y2 : ℝ)
    (hw1 : 0 ≤ w1) (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hw2 : 0 ≤ w2) (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) :
    (h_hom d (Real.sqrt (w1 * w2)) (Real.sqrt (x1 * x2)) (Real.sqrt (y1 * y2))) ^ 2 ≤
      h_hom d w1 x1 y1 * h_hom d w2 x2 y2 := by
        rw [ h_hom_eq_sum, h_hom_eq_sum, h_hom_eq_sum ];
        -- Applying the geometric mean property to each term in the sum.
        have h_geom_mean : ∀ (a b c d a' b' c' d' : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → 0 ≤ a' → 0 ≤ b' → 0 ≤ c' → 0 ≤ d' →
            (Real.sqrt (a * a') + Real.sqrt (b * b') + Real.sqrt (c * c') + Real.sqrt (d * d')) ^ 2 ≤
            (a + b + c + d) * (a' + b' + c' + d') := by
              intros a b c d a' b' c' d' ha hb hc hd ha' hb' hc' hd'
              have h_cauchy_schwarz : (Real.sqrt (a * a') + Real.sqrt (b * b') + Real.sqrt (c * c') + Real.sqrt (d * d')) ^ 2 ≤ (a + b + c + d) * (a' + b' + c' + d') := by
                have h_cauchy_schwarz_gen : ∀ (u v : Fin 4 → ℝ), (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
                  exact fun u v => by norm_num only [ Fin.sum_univ_four ] ; linarith [ sq_nonneg ( u 0 * v 1 - u 1 * v 0 ), sq_nonneg ( u 0 * v 2 - u 2 * v 0 ), sq_nonneg ( u 0 * v 3 - u 3 * v 0 ), sq_nonneg ( u 1 * v 2 - u 2 * v 1 ), sq_nonneg ( u 1 * v 3 - u 3 * v 1 ), sq_nonneg ( u 2 * v 3 - u 3 * v 2 ) ] ;
                convert h_cauchy_schwarz_gen ( fun i => if i = 0 then Real.sqrt a else if i = 1 then Real.sqrt b else if i = 2 then Real.sqrt c else Real.sqrt d ) ( fun i => if i = 0 then Real.sqrt a' else if i = 1 then Real.sqrt b' else if i = 2 then Real.sqrt c' else Real.sqrt d' ) using 1 <;> simp +decide [ Fin.sum_univ_four, Real.sq_sqrt, ha, hb, hc, hd, ha', hb', hc', hd' ];
              exact h_cauchy_schwarz;
        convert h_geom_mean _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ using 1 <;> (apply_rules [ mul_nonneg, pow_nonneg, hw1, hx1, hy1, hw2, hx2, hy2 ] ;);
        any_goals positivity;
        congr! 1;
        · congr! 1;
          · congr! 1;
            · convert h_hom_term1_geom_mean d hd w1 x1 y1 w2 x2 y2 hw1 hx1 hy1 hw2 hx2 hy2 using 1;
            · convert h_hom_term2_geom_mean d hd w1 x1 w2 x2 hw1 hx1 hw2 hx2 using 1;
          · convert h_hom_term3_geom_mean d hd w1 y1 w2 y2 hw1 hy1 hw2 hy2 using 1;
        · exact?

lemma Sd_implies_h_hom_bound (d : ℕ) (hd : d ≥ 2) (a : ℝ × ℝ × ℝ) (ha : a ∈ S_d d)
    (w x y : ℝ) (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a.1 * w + a.2.1 * x + a.2.2 * y ≥ (h_hom d w x y) ^ (1 / ((d : ℝ) + 1)) := by
      by_cases hw : w = 0;
      · rcases d with ( _ | _ | d ) <;> simp_all +decide [ h_hom ];
        exact le_trans ( by rw [ Real.zero_rpow ( by positivity ) ] ) ( add_nonneg ( mul_nonneg ( by linarith [ ha.2.1 ] ) hx ) ( mul_nonneg ( by linarith [ ha.2.2.1 ] ) hy ) );
      · -- Use `ha` with `x/w` and `y/w` to bound the term in parenthesis by `A_d(...)`.
        have h_bound : a.1 + a.2.1 * (x / w) + a.2.2 * (y / w) ≥ (A_d (d + 1) (x / w) (y / w)) ^ (1 / ((d : ℝ) + 1)) := by
          exact ha.2.2.2 _ _ ( div_nonneg hx ( by positivity ) ) ( div_nonneg hy ( by positivity ) );
        field_simp;
        convert mul_le_mul_of_nonneg_left h_bound ( show 0 ≤ w by positivity ) using 1 <;> ring;
        · rw [ show h_hom d w x y = w ^ ( d + 1 ) * A_d ( 1 + d ) ( x * w⁻¹ ) ( w⁻¹ * y ) by simpa [ add_comm, mul_comm, mul_assoc, mul_left_comm, hw ] using h_hom_eq_A_d d hd w x y ( by positivity ) ] ; rw [ Real.mul_rpow ( by positivity ) ( by exact ( show 0 ≤ A_d ( 1 + d ) ( x * w⁻¹ ) ( w⁻¹ * y ) from by
                                                                                                                                                                                                                                                                unfold A_d; norm_num; positivity; ) ) ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num [ Nat.cast_add_one_ne_zero ] ; ring;
          exact Or.inl ( by rw [ show ( d : ℝ ) * ( 1 + d : ℝ ) ⁻¹ + ( 1 + d : ℝ ) ⁻¹ = 1 by linarith [ mul_inv_cancel₀ ( by positivity : ( 1 + d : ℝ ) ≠ 0 ) ] ] ; norm_num );
        · simp +decide [ mul_assoc, mul_comm w, hw ]

lemma Sd_closed_under_geom_mean (d : ℕ) (hd : d ≥ 2) (a b : ℝ × ℝ × ℝ)
    (ha : a ∈ S_d d) (hb : b ∈ S_d d) :
    (Real.sqrt (a.1 * b.1), Real.sqrt (a.2.1 * b.2.1), Real.sqrt (a.2.2 * b.2.2)) ∈ S_d d := by
      refine' ⟨ Real.sqrt_pos.mpr ( mul_pos ha.1 hb.1 ), Real.sqrt_pos.mpr ( mul_pos ha.2.1 hb.2.1 ), Real.sqrt_pos.mpr ( mul_pos ha.2.2.1 hb.2.2.1 ), fun x y hx hy => _ ⟩;
      -- Let $LHS = \sqrt{a_1 b_1} + \sqrt{a_2 b_2} x + \sqrt{a_3 b_3} y$.
      set LHS := Real.sqrt (a.1 * b.1) + Real.sqrt (a.2.1 * b.2.1) * x + Real.sqrt (a.2.2 * b.2.2) * y;
      -- By definition of $LHS$, we know that $LHS^2 \geq (h_hom(w1, x1, y1) * h_hom(w2, x2, y2))^{1/(d+1)}$.
      have h_LHS_sq : LHS^2 ≥ (h_hom d (Real.sqrt (b.1 / a.1)) (x * Real.sqrt (b.2.1 / a.2.1)) (y * Real.sqrt (b.2.2 / a.2.2)) * h_hom d (Real.sqrt (a.1 / b.1)) (x * Real.sqrt (a.2.1 / b.2.1)) (y * Real.sqrt (a.2.2 / b.2.2))) ^ (1 / (d + 1 : ℝ)) := by
        have h_LHS_sq : LHS ≥ (h_hom d (Real.sqrt (b.1 / a.1)) (x * Real.sqrt (b.2.1 / a.2.1)) (y * Real.sqrt (b.2.2 / a.2.2))) ^ (1 / (d + 1 : ℝ)) ∧ LHS ≥ (h_hom d (Real.sqrt (a.1 / b.1)) (x * Real.sqrt (a.2.1 / b.2.1)) (y * Real.sqrt (a.2.2 / b.2.2))) ^ (1 / (d + 1 : ℝ)) := by
          constructor;
          · have := Sd_implies_h_hom_bound d hd a ha ( Real.sqrt ( b.1 / a.1 ) ) ( x * Real.sqrt ( b.2.1 / a.2.1 ) ) ( y * Real.sqrt ( b.2.2 / a.2.2 ) ) ( Real.sqrt_nonneg _ ) ( mul_nonneg hx ( Real.sqrt_nonneg _ ) ) ( mul_nonneg hy ( Real.sqrt_nonneg _ ) );
            convert this using 1;
            simp +zetaDelta at *;
            norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, Real.sqrt_mul, ha.1.ne', ha.2.1.ne', ha.2.2.1.ne', hb.1.ne', hb.2.1.ne', hb.2.2.1.ne' ];
            simp +decide [ ← mul_assoc, ← div_eq_mul_inv, ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ];
          · convert Sd_implies_h_hom_bound d hd b hb ( Real.sqrt ( a.1 / b.1 ) ) ( x * Real.sqrt ( a.2.1 / b.2.1 ) ) ( y * Real.sqrt ( a.2.2 / b.2.2 ) ) ( Real.sqrt_nonneg _ ) ( mul_nonneg hx ( Real.sqrt_nonneg _ ) ) ( mul_nonneg hy ( Real.sqrt_nonneg _ ) ) using 1;
            simp +zetaDelta at *;
            norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ];
            grind;
        rw [ Real.mul_rpow ];
        · nlinarith [ show 0 ≤ h_hom d ( Real.sqrt ( b.1 / a.1 ) ) ( x * Real.sqrt ( b.2.1 / a.2.1 ) ) ( y * Real.sqrt ( b.2.2 / a.2.2 ) ) ^ ( 1 / ( d + 1 : ℝ ) ) by exact Real.rpow_nonneg ( h_hom_nonneg d _ _ _ ( Real.sqrt_nonneg _ ) ( mul_nonneg hx ( Real.sqrt_nonneg _ ) ) ( mul_nonneg hy ( Real.sqrt_nonneg _ ) ) ) _, show 0 ≤ h_hom d ( Real.sqrt ( a.1 / b.1 ) ) ( x * Real.sqrt ( a.2.1 / b.2.1 ) ) ( y * Real.sqrt ( a.2.2 / b.2.2 ) ) ^ ( 1 / ( d + 1 : ℝ ) ) by exact Real.rpow_nonneg ( h_hom_nonneg d _ _ _ ( Real.sqrt_nonneg _ ) ( mul_nonneg hx ( Real.sqrt_nonneg _ ) ) ( mul_nonneg hy ( Real.sqrt_nonneg _ ) ) ) _ ];
        · exact h_hom_nonneg _ _ _ _ ( Real.sqrt_nonneg _ ) ( mul_nonneg hx ( Real.sqrt_nonneg _ ) ) ( mul_nonneg hy ( Real.sqrt_nonneg _ ) );
        · apply h_hom_nonneg;
          · positivity;
          · positivity;
          · positivity;
      -- By definition of $h_hom$, we know that $h_hom(w1, x1, y1) * h_hom(w2, x2, y2) \geq h_hom(1, x, y)^2$.
      have h_h_hom_prod : h_hom d (Real.sqrt (b.1 / a.1)) (x * Real.sqrt (b.2.1 / a.2.1)) (y * Real.sqrt (b.2.2 / a.2.2)) * h_hom d (Real.sqrt (a.1 / b.1)) (x * Real.sqrt (a.2.1 / b.2.1)) (y * Real.sqrt (a.2.2 / b.2.2)) ≥ h_hom d 1 x y ^ 2 := by
        have := h_hom_CS d hd ( Real.sqrt ( b.1 / a.1 ) ) ( x * Real.sqrt ( b.2.1 / a.2.1 ) ) ( y * Real.sqrt ( b.2.2 / a.2.2 ) ) ( Real.sqrt ( a.1 / b.1 ) ) ( x * Real.sqrt ( a.2.1 / b.2.1 ) ) ( y * Real.sqrt ( a.2.2 / b.2.2 ) ) ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num at *;
        · convert this using 3 <;> norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ] ; ring ; norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ] ;
          · rw [ Real.sqrt_sq hx ];
          · ring_nf; norm_num [ ha.2.2.1.le, hb.2.2.1.le, ne_of_gt ha.2.2.1, ne_of_gt hb.2.2.1 ] ;
            rw [ Real.sqrt_sq hy ];
        · positivity;
        · positivity;
        · positivity;
        · exact mul_nonneg hy ( Real.sqrt_nonneg _ );
      -- By definition of $h_hom$, we know that $h_hom(1, x, y) = A_d(d+1, x, y)$.
      have h_h_hom_one : h_hom d 1 x y = A_d (d + 1) x y := by
        unfold h_hom A_d; ring;
        push_cast; ring;
      contrapose! h_LHS_sq;
      refine' lt_of_lt_of_le ( pow_lt_pow_left₀ h_LHS_sq ( by positivity ) ( by positivity ) ) _;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact h_h_hom_one ▸ show 0 ≤ h_hom d 1 x y from by exact h_hom_nonneg d 1 x y ( by positivity ) hx hy ) ] ; norm_num;
      refine' le_trans _ ( Real.rpow_le_rpow ( by exact pow_two_nonneg _ ) h_h_hom_prod ( by positivity ) );
      rw [ h_h_hom_one, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact show 0 ≤ A_d ( d + 1 ) x y from by exact h_h_hom_one ▸ show 0 ≤ h_hom d 1 x y from by exact h_hom_nonneg d 1 x y ( by positivity ) hx hy ) ] ; ring_nf ; norm_num

lemma log_S_d_is_closed (d : ℕ) : IsClosed (log_S_d d) := by
  -- Let `w_n` be a sequence in `log_S_d` converging to `w`.
  have h_seq : ∀ w, (∃ seq : ℕ → ℝ × ℝ × ℝ, (∀ n, seq n ∈ S_d d) ∧ Filter.Tendsto (fun n => (Real.log (seq n).1, Real.log (seq n).2.1, Real.log (seq n).2.2)) Filter.atTop (nhds w)) → w ∈ log_S_d d := by
    rintro w ⟨ seq, hseq_mem, hseq_conv ⟩
    obtain ⟨v, hv⟩ : ∃ v : ℝ × ℝ × ℝ, v ∈ S_d d ∧ w = (Real.log v.1, Real.log v.2.1, Real.log v.2.2) := by
      -- By continuity of the exponential function, we have $v_n \to v$.
      have h_exp_conv : Filter.Tendsto (fun n => (Real.exp (Real.log (seq n).1), Real.exp (Real.log (seq n).2.1), Real.exp (Real.log (seq n).2.2))) Filter.atTop (nhds (Real.exp w.1, Real.exp w.2.1, Real.exp w.2.2)) := by
        exact Filter.Tendsto.prodMk_nhds ( Real.continuous_exp.continuousAt.tendsto.comp ( continuousAt_fst.tendsto.comp hseq_conv ) ) ( Filter.Tendsto.prodMk_nhds ( Real.continuous_exp.continuousAt.tendsto.comp ( continuousAt_snd.fst.tendsto.comp hseq_conv ) ) ( Real.continuous_exp.continuousAt.tendsto.comp ( continuousAt_snd.snd.tendsto.comp hseq_conv ) ) )
      generalize_proofs at *; (
      -- By continuity of the exponential function and the inequality, we have $v \in S_d$.
      have h_v_mem : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → (Real.exp w.1) + (Real.exp w.2.1) * x + (Real.exp w.2.2) * y ≥ (A_d (d + 1) x y) ^ (1 / ((d : ℝ) + 1)) := by
        intros x y hx hy
        have h_lim : Filter.Tendsto (fun n => (Real.exp (Real.log (seq n).1)) + (Real.exp (Real.log (seq n).2.1)) * x + (Real.exp (Real.log (seq n).2.2)) * y) Filter.atTop (nhds ((Real.exp w.1) + (Real.exp w.2.1) * x + (Real.exp w.2.2) * y)) := by
          exact Filter.Tendsto.add ( Filter.Tendsto.add ( continuousAt_fst.tendsto.comp h_exp_conv ) ( Filter.Tendsto.mul ( continuousAt_snd.fst.tendsto.comp h_exp_conv ) tendsto_const_nhds ) ) ( Filter.Tendsto.mul ( continuousAt_snd.snd.tendsto.comp h_exp_conv ) tendsto_const_nhds ) |> fun h => h.trans ( by norm_num ) ;
        generalize_proofs at *; (
        exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim fun n => by simpa only [ Real.exp_log ( hseq_mem n |>.1 ), Real.exp_log ( hseq_mem n |>.2.1 ), Real.exp_log ( hseq_mem n |>.2.2.1 ) ] using hseq_mem n |>.2.2.2 x y hx hy;)
      generalize_proofs at *; (
      exact ⟨ ( Real.exp w.1, Real.exp w.2.1, Real.exp w.2.2 ), ⟨ by positivity, by positivity, by positivity, h_v_mem ⟩, by simp +decide [ Real.log_exp ] ⟩))
    exact ⟨v, hv⟩;
  refine' isClosed_of_closure_subset _;
  intro w hw;
  rw [ mem_closure_iff_seq_limit ] at hw;
  obtain ⟨ seq, hseq₁, hseq₂ ⟩ := hw;
  convert h_seq w _;
  choose seq' hseq' using hseq₁;
  exact ⟨ seq', fun n => hseq' n |>.1, by simpa only [ ← hseq' _ |>.2 ] using hseq₂ ⟩

end AristotleLemmas

lemma Sd_convex (d : ℕ) (hd : d ≥ 2) :
    Convex ℝ (log_S_d d) := by
  -- By definition of $log_S_d$, we know that if $u, v \in log_S_d d$, then $(u+v)/2 \in log_S_d d$.
  have h_midpoint_convexity : ∀ u v : ℝ × ℝ × ℝ, u ∈ log_S_d d → v ∈ log_S_d d → (u + v) / 2 ∈ log_S_d d := by
    rintro u v ⟨ a, ha, rfl ⟩ ⟨ b, hb, rfl ⟩;
    refine' ⟨ ( Real.sqrt ( a.1 * b.1 ), Real.sqrt ( a.2.1 * b.2.1 ), Real.sqrt ( a.2.2 * b.2.2 ) ), Sd_closed_under_geom_mean d hd a b ha hb, _ ⟩;
    norm_num [ Real.log_sqrt ( mul_nonneg ( show 0 ≤ a.1 from ha.1.le ) ( show 0 ≤ b.1 from hb.1.le ) ), Real.log_sqrt ( mul_nonneg ( show 0 ≤ a.2.1 from ha.2.1.le ) ( show 0 ≤ b.2.1 from hb.2.1.le ) ), Real.log_sqrt ( mul_nonneg ( show 0 ≤ a.2.2 from ha.2.2.1.le ) ( show 0 ≤ b.2.2 from hb.2.2.1.le ) ) ];
    rw [ Real.log_mul ( ne_of_gt ha.1 ) ( ne_of_gt hb.1 ), Real.log_mul ( ne_of_gt ha.2.1 ) ( ne_of_gt hb.2.1 ), Real.log_mul ( ne_of_gt ha.2.2.1 ) ( ne_of_gt hb.2.2.1 ) ] ; ext <;> ring;
    · exact show ( Real.log a.1 + Real.log b.1 ) / 2 = Real.log a.1 * ( 1 / 2 ) + Real.log b.1 * ( 1 / 2 ) by ring;
    · exact show ( Real.log a.2.1 + Real.log b.2.1 ) / 2 = Real.log a.2.1 * ( 1 / 2 ) + Real.log b.2.1 * ( 1 / 2 ) by ring;
    · exact show ( Real.log a.2.2 + Real.log b.2.2 ) / 2 = Real.log a.2.2 * ( 1 / 2 ) + Real.log b.2.2 * ( 1 / 2 ) by ring;
  -- Since `log_S_d` is closed (by `log_S_d_is_closed`), and dyadic rationals are dense, the set is convex.
  have h_dense : ∀ u v : ℝ × ℝ × ℝ, u ∈ log_S_d d → v ∈ log_S_d d → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • u + (1 - t) • v ∈ closure (log_S_d d) := by
    intro u v hu hv t ht₁ ht₂_one
    have h_dyadic : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2^n → (k / 2^n : ℝ) • u + (1 - k / 2^n : ℝ) • v ∈ log_S_d d := by
      intro n k hk_le; induction' n with n ih generalizing k <;> simp_all +decide [ pow_succ' ] ;
      · interval_cases k <;> aesop;
      · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
        · convert ih k hk_le using 1 ; ring;
        · convert h_midpoint_convexity _ _ _ _ _ _ ( ih k ( by linarith ) ) ( ih ( k + 1 ) ( by linarith ) ) using 1 ; norm_num ; ring;
          ext <;> norm_num <;> ring;
    -- By the density of dyadic rationals in [0,1], we can find a sequence of dyadic rationals $t_n$ such that $t_n \to t$.
    obtain ⟨t_n, ht_n⟩ : ∃ t_n : ℕ → ℝ, (∀ n, t_n n ∈ Set.Icc 0 1) ∧ (∀ n, ∃ k : ℕ, k ≤ 2^n ∧ t_n n = k / 2^n) ∧ Filter.Tendsto t_n Filter.atTop (nhds t) := by
      use fun n => (⌊t * 2^n⌋₊ : ℝ) / 2^n;
      refine' ⟨ fun n => ⟨ div_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg zero_le_two _ ), div_le_one_of_le₀ ( Nat.floor_le ( by positivity ) |> le_trans <| mul_le_of_le_one_left ( by positivity ) ht₂_one ) ( by positivity ) ⟩, fun n => ⟨ ⌊t * 2 ^ n⌋₊, _, rfl ⟩, _ ⟩;
      · exact Nat.floor_le_of_le ( by norm_num; nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ] );
      · refine' ( tendsto_iff_norm_sub_tendsto_zero.mpr _ );
        norm_num [ div_sub' ];
        refine' squeeze_zero ( fun _ => div_nonneg ( abs_nonneg _ ) ( pow_nonneg zero_le_two _ ) ) ( fun e => div_le_div_of_nonneg_right ( show |↑⌊t * 2 ^ e⌋₊ - 2 ^ e * t| ≤ 1 by erw [ abs_le ] ; constructor <;> linarith [ Nat.floor_le ( show 0 ≤ t * 2 ^ e by positivity ), Nat.lt_floor_add_one ( t * 2 ^ e ), show ( 2 ^ e : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) ] ) ( pow_nonneg zero_le_two _ ) ) ( tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) );
    -- By the properties of the closure, since $t_n \to t$, we have $t_n • u + (1 - t_n) • v \to t • u + (1 - t) • v$.
    have h_tendsto : Filter.Tendsto (fun n => t_n n • u + (1 - t_n n) • v) Filter.atTop (nhds (t • u + (1 - t) • v)) := by
      exact Filter.Tendsto.add ( Filter.Tendsto.smul ht_n.2.2 tendsto_const_nhds ) ( Filter.Tendsto.smul ( tendsto_const_nhds.sub ht_n.2.2 ) tendsto_const_nhds );
    exact mem_closure_of_tendsto h_tendsto ( Filter.Eventually.of_forall fun n => by obtain ⟨ k, hk₁, hk₂ ⟩ := ht_n.2.1 n; simpa [ hk₂ ] using h_dyadic n k hk₁ );
  -- Since `log_S_d` is closed (by `log_S_d_is_closed`), and dyadic rationals are dense, the set is convex. Hence, we can conclude that `log_S_d` is convex.
  have h_closed : IsClosed (log_S_d d) := by
    exact?;
  exact fun u hu v hv a b ha hb hab => by simpa [ ← hab ] using h_dense u v hu hv ( a ) ha ( by linarith ) |> fun h => h_closed.closure_subset h;
