/-
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetLogConvex
import MultivarIndepFormalize.DualSetMembershipSeparately

set_option linter.style.longLine false

open Real BigOperators

noncomputable section

/--
Helper lemma: S_d is closed under the geometric mean of Δ elements.
This follows from the convexity of log S_d.
-/
lemma Sd_geometric_mean (Δ : ℕ) (hΔ : Δ ≥ 2) (v : Fin Δ → ℝ × ℝ × ℝ) (hv : ∀ i, v i ∈ S_d Δ) :
    let p := (1 : ℝ) / Δ
    (∏ i, (v i).1 ^ p, ∏ i, (v i).2.1 ^ p, ∏ i, (v i).2.2 ^ p) ∈ S_d Δ := by
      -- By convexity of log S_d, the linear combination is in log S_d.
      have h_log_convex : Convex ℝ (log_S_d Δ) := Sd_log_convex Δ hΔ;
      -- By definition of $log_S_d$, we know that $(log (v_i).1, log (v_i).2.1, log (v_i).2.2) \in log_S_d$ for each $i$.
      have h_log_v : ∀ i, (log (v i).1, log (v i).2.1, log (v i).2.2) ∈ log_S_d Δ := by
        exact fun i => ⟨ v i, hv i, rfl ⟩;
      -- By definition of $log_S_d$, we know that $(\sum_{i=0}^{\Delta-1} p \log (v_i).1, \sum_{i=0}^{\Delta-1} p \log (v_i).2.1, \sum_{i=0}^{\Delta-1} p \log (v_i).2.2) \in log_S_d$.
      have h_log_sum : (Finset.sum Finset.univ fun i => (1 / (Δ : ℝ)) * Real.log (v i).1, Finset.sum Finset.univ fun i => (1 / (Δ : ℝ)) * Real.log (v i).2.1, Finset.sum Finset.univ fun i => (1 / (Δ : ℝ)) * Real.log (v i).2.2) ∈ log_S_d Δ := by
        -- Apply the convexity of log_S_d to the points (log (v i).1, log (v i).2.1, log (v i).2.2) and weights 1/Δ.
        have h_convex_comb : ∀ (x : Fin Δ → ℝ × ℝ × ℝ), (∀ i, x i ∈ log_S_d Δ) → (∑ i, (1 / (Δ : ℝ)) • x i) ∈ log_S_d Δ := by
          intros x hx
          have h_sum : ∑ i : Fin Δ, (1 / (Δ : ℝ)) = 1 := by
            norm_num [ show Δ ≠ 0 by linarith ];
          convert h_log_convex.sum_mem _ _ _ <;> aesop;
        convert h_convex_comb _ h_log_v using 1 ; norm_num [ Prod.ext_iff ];
        induction' ( Finset.univ : Finset ( Fin Δ ) ) using Finset.induction <;> aesop;
      obtain ⟨ w, hw, hw' ⟩ := h_log_sum;
      convert hw using 1;
      -- By definition of exponentiation, we can rewrite the products as exponentials of sums.
      have h_exp_sum : ∀ (x : Fin Δ → ℝ), (∀ i, 0 < x i) → (∏ i, x i ^ (1 / (Δ : ℝ))) = Real.exp (∑ i, (1 / (Δ : ℝ)) * Real.log (x i)) := by
        exact fun x hx => by rw [ Real.exp_sum, Finset.prod_congr rfl ] ; intros; rw [ Real.rpow_def_of_pos ( hx _ ) ] ; ring_nf;;
      have h_exp_sum : (∏ i, (v i).1 ^ (1 / (Δ : ℝ))) = Real.exp (∑ i, (1 / (Δ : ℝ)) * Real.log (v i).1) ∧ (∏ i, (v i).2.1 ^ (1 / (Δ : ℝ))) = Real.exp (∑ i, (1 / (Δ : ℝ)) * Real.log (v i).2.1) ∧ (∏ i, (v i).2.2 ^ (1 / (Δ : ℝ))) = Real.exp (∑ i, (1 / (Δ : ℝ)) * Real.log (v i).2.2) := by
        exact ⟨ h_exp_sum _ fun i => hv i |>.1, h_exp_sum _ fun i => hv i |>.2.1, h_exp_sum _ fun i => hv i |>.2.2.1 ⟩;
      simp_all +decide only [one_div];
      simp_all [Real.exp_log, hw.1, hw.2.1, hw.2.2.1]

lemma SΔ_membership_algebraic_identity {n : ℕ} (Δ : ℝ) (hΔ : Δ ≠ 0)
    (x y a b : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    (∏ i, (x i ^ (Δ / a i) / y i ^ (Δ / b i)) ^ (1 / Δ)) =
    ∏ i, x i ^ (1 / a i) / y i ^ (1 / b i) := by
      apply Finset.prod_congr rfl ?_;
      intro i hi; rw [ Real.div_rpow ( le_of_lt ( Real.rpow_pos_of_pos ( hx i ) _ ) ) ( le_of_lt ( Real.rpow_pos_of_pos ( hy i ) _ ) ), ← Real.rpow_mul ( le_of_lt ( hx i ) ), ← Real.rpow_mul ( le_of_lt ( hy i ) ) ] ; ring_nf; norm_num [ hΔ ] ;
      exact Or.inl ( by rw [ mul_right_comm, mul_inv_cancel₀ hΔ, one_mul ] )

/--
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

**Statement**
Let \(\Delta\ge2\) and \(1\le d_i\le \Delta\), \(1\le i\le \Delta\) be integers. Let \(\lambda_i,\mu_i\ge0\) for \(1\le i\le \Delta\). Then
\[
  \biggl(
  \prod_{i=1}^\Delta \frac{A_{d_i}(\lambda_i,\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\lambda_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}}
  \biggr) \in \calS_\Delta.
\]
-/
lemma SΔ_membership (Δ : ℕ) (hΔ : Δ ≥ 2)
    (d : Fin Δ → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ Δ)
    (η μ : Fin Δ → ℝ) (hη : ∀ i, 0 ≤ η i) (hμ : ∀ i, 0 ≤ μ i) :
    let triple := (
      ∏ i, (A_d (d i) (η i) (μ i)) ^ (1 / (d i : ℝ)) / (A_d (d i + 1) (η i) (μ i)) ^ (1 / ((d i : ℝ) + 1)),
      ∏ i, (B_d (d i) (μ i)) ^ (1 / (d i : ℝ)) / (A_d (d i + 1) (η i) (μ i)) ^ (1 / ((d i : ℝ) + 1)),
      ∏ i, (B_d (d i) (η i)) ^ (1 / (d i : ℝ)) / (A_d (d i + 1) (η i) (μ i)) ^ (1 / ((d i : ℝ) + 1))
    )
    triple ∈ S_d Δ := by
  /-
  USE THE FOLLOWING PROOF SKETCH:
  1. This lemma is a consequence of Lemma 3.3 (Symmetric/Separate Membership; SΔ_membership_separately) and the convexity of log(S_Δ; Sd_log_convex) (Lemma 3.4).
  2. For each index i, Lemma 3.3 establishes that the i-th component triple
     (raised to the power Δ) is in S_Δ.
  3. By the coordinate-wise geometric mean property (log-convexity) of S_Δ
     established in Lemma 3.4, the product of these triples also belongs to S_Δ.
  4. The result follows by taking the Δ-th root of the combined membership
     expression.
  -/
  have := Sd_geometric_mean Δ hΔ;
  convert this ( fun i => ( A_d ( d i ) ( η i ) ( μ i ) ^ ( Δ / ( d i : ℝ ) ) / A_d ( d i + 1 ) ( η i ) ( μ i ) ^ ( Δ / ( d i + 1 : ℝ ) ), B_d ( d i ) ( μ i ) ^ ( Δ / ( d i : ℝ ) ) / A_d ( d i + 1 ) ( η i ) ( μ i ) ^ ( Δ / ( d i + 1 : ℝ ) ), B_d ( d i ) ( η i ) ^ ( Δ / ( d i : ℝ ) ) / A_d ( d i + 1 ) ( η i ) ( μ i ) ^ ( Δ / ( d i + 1 : ℝ ) ) ) ) _ using 1;
  · norm_num [ Real.rpow_def_of_pos, div_eq_mul_inv ];
    congr! 2;
    · refine' Finset.prod_congr rfl fun i _ => _;
      rw [ Real.mul_rpow, ← Real.rpow_neg, ← Real.rpow_mul, ← Real.rpow_neg, ← Real.rpow_mul ] <;> norm_num [ show Δ ≠ 0 by linarith ];
      · field_simp;
      all_goals unfold A_d; norm_num [ hη, hμ ];
      any_goals nlinarith [ hη i, hμ i, show ( d i : ℝ ) ≥ 1 by exact_mod_cast hd i |>.1, show ( d i : ℝ ) ≤ Δ by exact_mod_cast hd i |>.2, mul_nonneg ( hη i ) ( hμ i ), mul_nonneg ( show ( d i : ℝ ) ≥ 0 by positivity ) ( hη i ), mul_nonneg ( show ( d i : ℝ ) ≥ 0 by positivity ) ( hμ i ) ];
      · exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( hd i |>.1 ) ) ) ) ( hη i ) ) ( hμ i ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( hη i ) ( hμ i ) ) ) ) zero_le_one;
      · field_simp;
        exact Real.rpow_nonneg ( add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg ( mul_nonneg ( mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( hd i |>.1 ) ) ) ( hη i ) ) ( hμ i ) ) ( add_nonneg ( hη i ) ( hμ i ) ) ) ) zero_le_one ) _;
      · exact Real.rpow_nonneg ( by nlinarith [ hη i, hμ i, show ( d i : ℝ ) ≥ 1 by exact_mod_cast hd i |>.1, show ( d i : ℝ ) ≤ Δ by exact_mod_cast hd i |>.2, mul_nonneg ( hη i ) ( hμ i ), mul_nonneg ( show ( d i : ℝ ) ≥ 0 by positivity ) ( hη i ), mul_nonneg ( show ( d i : ℝ ) ≥ 0 by positivity ) ( hμ i ) ] ) _;
    · field_simp;
      congr! 1;
      · refine' Finset.prod_congr rfl fun i _ => _;
        rw [ Real.div_rpow ];
        · rw [ ← Real.rpow_mul, ← Real.rpow_mul ] <;> ring_nf <;> norm_num [ show Δ ≠ 0 by linarith ];
          · exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by norm_num ) ) ( by linarith [ hη i, hμ i ] ) ) ( by linarith [ hη i, hμ i ] ) ) ( mul_nonneg ( by linarith [ hd i ] ) ( by linarith [ hη i, hμ i ] ) ) ) zero_le_one;
          · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( hμ i ) ) zero_le_one;
        · exact Real.rpow_nonneg ( by unfold B_d; exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( hμ _ ) ) zero_le_one ) _;
        · exact Real.rpow_nonneg ( by exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by norm_num ) ) ( hη i ) ) ( hμ i ) ) ( mul_nonneg ( by positivity ) ( add_nonneg ( hη i ) ( hμ i ) ) ) ) zero_le_one ) _;
      · refine' Finset.prod_congr rfl fun i _ => _;
        rw [ Real.div_rpow ( Real.rpow_nonneg ( _ ) _ ) ( Real.rpow_nonneg ( _ ) _ ), ← Real.rpow_mul ( _ ), ← Real.rpow_mul ( _ ) ] ; ring_nf;
        · norm_num [ show Δ ≠ 0 by linarith ];
        · exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by norm_num ) ) ( by linarith [ hη i, hμ i ] ) ) ( by linarith [ hη i, hμ i ] ) ) ( mul_nonneg ( by positivity ) ( by linarith [ hη i, hμ i ] ) ) ) zero_le_one;
        · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( hη i ) ) zero_le_one;
        · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( hη i ) ) zero_le_one;
        · exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) ( by norm_num ) ) ( by linarith [ hη i, hμ i ] ) ) ( by linarith [ hη i, hμ i ] ) ) ( mul_nonneg ( by positivity ) ( by linarith [ hη i, hμ i ] ) ) ) zero_le_one;
  · exact fun i => SΔ_membership_separately Δ hΔ ( d i ) ( hd i |>.1 ) ( hd i |>.2 ) ( η i ) ( μ i ) ( hη i ) ( hμ i )
