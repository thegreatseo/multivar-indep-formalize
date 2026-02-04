/-
**Lemma 3.4** `lem:Sd-log-convex` (Sd_log_convex)
log S_d is convex.
-/

-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions

set_option linter.style.longLine false

open Real

noncomputable section

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
        · convert this using 3 <;> norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ] ; ring ;
          · norm_num [ ha.1.le, ha.2.1.le, ha.2.2.1.le, hb.1.le, hb.2.1.le, hb.2.2.1.le, ne_of_gt ha.1, ne_of_gt ha.2.1, ne_of_gt ha.2.2.1, ne_of_gt hb.1, ne_of_gt hb.2.1, ne_of_gt hb.2.2.1 ] ;
            rw [ Real.sqrt_sq hx ];
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


/-
**Lemma 3.4** `lem:Sd-log-convex`
log S_d is convex.
-/
lemma Sd_log_convex (d : ℕ) (hd : d ≥ 2) :
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
