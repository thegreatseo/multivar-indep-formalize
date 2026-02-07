/-
**Lemma 3.3** `lem:Sn-membership-separately`
"Something separated" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.TechnicalLemmas
import MultivarIndepFormalize.DualSetBoundary

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
The function H_k(x) = A_k(x) / B_k(x).
Matches definition on page 11[cite: 800].
-/
def H_k (k : ℕ) (x : ℝ) : ℝ :=
  A_d k x x / B_d k x

lemma H_k_eq (k : ℕ) (x : ℝ) :
    H_k k x = (k * (k - 1) * x ^ 2 + 2 * k * x + 1) / (k * x + 1) := by
  unfold H_k A_d B_d; ring;

lemma H_k_zero (k : ℕ) : H_k k 0 = 1 := by
  convert H_k_eq k 0 using 1 ; norm_num

lemma H_k_strictMonoOn (k : ℕ) (hk : 1 ≤ k) :
    StrictMonoOn (H_k k) (Set.Ici 0) := by
  unfold StrictMonoOn;
  unfold H_k;
  norm_num [ A_d, B_d ];
  intro a ha b hb hab; rw [ div_lt_div_iff₀ ] <;> try positivity;
  nlinarith [ mul_le_mul_of_nonneg_left hab.le ( show 0 ≤ ( k : ℝ ) * a by positivity ), mul_le_mul_of_nonneg_left hab.le ( show 0 ≤ ( k : ℝ ) * b by positivity ), mul_le_mul_of_nonneg_left hab.le ( show 0 ≤ ( k : ℝ ) ^ 2 * a * b by positivity ), mul_le_mul_of_nonneg_left hab.le ( show 0 ≤ ( k : ℝ ) ^ 2 * a ^ 2 by positivity ), mul_le_mul_of_nonneg_left hab.le ( show 0 ≤ ( k : ℝ ) ^ 2 * b ^ 2 by positivity ), show ( k : ℝ ) ≥ 1 by norm_cast ]

lemma H_1_tendsto : Filter.Tendsto (H_k 1) Filter.atTop (nhds 2) := by
  -- Substitute $k = 1$ into the definition of $H_k$.
  unfold H_k A_d B_d;
  field_simp;
  rw [ Metric.tendsto_nhds ] ; norm_num;
  exact fun ε hε => ⟨ ⌈ε⁻¹ * 3⌉₊ + 1, fun x hx => abs_lt.mpr ⟨ by nlinarith [ Nat.le_ceil ( ε⁻¹ * 3 ), mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( x * 2 + 1 ) ( by linarith : ( x + 1 ) ≠ 0 ) ], by nlinarith [ Nat.le_ceil ( ε⁻¹ * 3 ), mul_inv_cancel₀ hε.ne', div_mul_cancel₀ ( x * 2 + 1 ) ( by linarith : ( x + 1 ) ≠ 0 ) ] ⟩ ⟩

lemma H_k_tendsto_atTop (k : ℕ) (hk : 1 < k) :
    Filter.Tendsto (H_k k) Filter.atTop Filter.atTop := by
  -- We'll use that $H_k(x)$ grows without bound as $x$ approaches infinity. Note that $H_k(x) \geq \frac{(k-1)x^2}{kx+1}$.
  suffices h_suff' : Filter.Tendsto (fun x : ℝ => (k * (k - 1) * x^2) / (k * x + 1)) Filter.atTop Filter.atTop by
    -- Since $H_k(x) \geq \frac{(k-1)x^2}{kx+1}$ for all $x \geq 0$, and the right-hand side tends to infinity, it follows that $H_k(x)$ also tends to infinity.
    have h_ge : ∀ x : ℝ, 0 < x → H_k k x ≥ (k * (k - 1) * x^2) / (k * x + 1) := by
      intro x hx
      rw [H_k_eq];
      gcongr ; nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast ];
    refine' Filter.tendsto_atTop.2 fun x => _;
    filter_upwards [ h_suff'.eventually_gt_atTop x, Filter.eventually_gt_atTop 0 ] with y hy₁ hy₂ using le_trans hy₁.le <| h_ge y hy₂;
  -- We can divide the numerator and the denominator by $x$ and then take the limit as $x$ approaches infinity.
  suffices h_suff'' : Filter.Tendsto (fun x : ℝ => (k * (k - 1) * x) / (k + 1 / x)) Filter.atTop Filter.atTop by
    grind;
  -- We can use the fact that $k + 1/x$ tends to $k$ as $x$ approaches infinity.
  have h_denom : Filter.Tendsto (fun x : ℝ => k + 1 / x) Filter.atTop (nhds k) := by
    simpa using tendsto_inv_atTop_zero.const_add ( k : ℝ );
  apply Filter.Tendsto.atTop_mul_pos;
  exacts [ inv_pos.mpr ( by positivity : 0 < ( k : ℝ ) ), Filter.Tendsto.const_mul_atTop ( by nlinarith [ show ( k : ℝ ) > 1 by norm_cast ] ) Filter.tendsto_id, h_denom.inv₀ ( by positivity ) ]

/--
For each k ≥ 2 and s ≥ 1, there is a unique x_k ≥ 0 such that H_k(x_k)^(1/k) = s.
Established by H_k(0) = 1 and strict monotonicity on page 11[cite: 800, 801].
-/
lemma exists_unique_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s)
   (hks : k = 1 → s < 2):
    ∃! x : ℝ, x ≥ 0 ∧ (H_k k x) ^ (1 / (k : ℝ)) = s := by
      -- By definition of $H_k$, we know that $H_k(x)$ is strictly increasing on $(0, \infty)$ and tends to infinity as $x$ tends to infinity. Hence, it has a unique preimage for any $s \geq 1$.
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x ≥ 0 ∧ (H_k k x) ^ (1 / k : ℝ) = s := by
        by_cases hk1 : k = 1;
        · -- By definition of $H_k$, we know that $H_k(x) = \frac{2x + 1}{x + 1}$ for $k = 1$.
          have hH1 : ∀ x : ℝ, x ≥ 0 → H_k 1 x = (2 * x + 1) / (x + 1) := by
            intro x hx; unfold H_k; unfold A_d B_d; ring;
          -- By definition of $H_k$, we know that $H_k(x) = \frac{2x + 1}{x + 1}$ for $k = 1$. We need to solve $(2x + 1) / (x + 1) = s$ for $x$.
          have h_eq : ∃ x : ℝ, x ≥ 0 ∧ (2 * x + 1) / (x + 1) = s := by
            exact ⟨ ( s - 1 ) / ( 2 - s ), div_nonneg ( by linarith ) ( by linarith [ hks hk1 ] ), by rw [ div_eq_iff ] <;> nlinarith [ hks hk1, mul_div_cancel₀ ( s - 1 ) ( by linarith [ hks hk1 ] : ( 2 - s ) ≠ 0 ) ] ⟩;
          aesop;
        · -- Since $H_k(x)$ is continuous and strictly increasing on $[0, \infty)$, and $H_k(0) = 1$ and $H_k(x) \to \infty$ as $x \to \infty$, by the intermediate value theorem, there exists some $x \geq 0$ such that $H_k(x) = s^k$.
          have h_ivt : ∃ x ∈ Set.Icc 0 (s ^ k), H_k k x = s ^ k := by
            apply_rules [ intermediate_value_Icc ] <;> norm_num;
            · positivity;
            · refine' ContinuousOn.div _ _ _ <;> norm_num [ H_k ];
              · exact Continuous.continuousOn ( by unfold A_d; continuity );
              · exact Continuous.continuousOn ( by unfold B_d; continuity );
              · exact fun x hx₁ hx₂ => by unfold B_d; positivity;
            · -- Since $H_k k 0 = 1$ and $s \geq 1$, we have $1 \leq s^k$.
              have h1 : H_k k 0 ≤ s^k := by
                exact le_trans ( by norm_num [ H_k_zero ] ) ( one_le_pow₀ hs );
              refine ⟨ h1, ?_ ⟩;
              rw [ H_k_eq ];
              rw [ le_div_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne hk ( Ne.symm hk1 ), pow_pos ( zero_lt_one.trans_le hs ) k, mul_le_mul_of_nonneg_left ( show ( k : ℝ ) ≥ 2 by norm_cast; exact Nat.lt_of_le_of_ne hk ( Ne.symm hk1 ) ) ( pow_nonneg ( zero_le_one.trans hs ) k ) ];
          exact h_ivt.imp fun x hx => ⟨ hx.1.1, by rw [ hx.2, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ⟩;
      use x;
      -- Since $H_k$ is strictly increasing on $[0, \infty)$, the function $(H_k k x)^{1/k}$ is also strictly increasing. Therefore, if $y$ and $x$ are both solutions, then $y$ must equal $x$ because the function is strictly increasing.
      have h_unique : StrictMonoOn (fun x => (H_k k x) ^ (1 / k : ℝ)) (Set.Ici 0) := by
        -- Since $H_k$ is strictly increasing on $[0, \infty)$, and the $k$-th root function is strictly increasing, their composition is also strictly increasing.
        have h_comp_mono : StrictMonoOn (fun x => H_k k x) (Set.Ici 0) := by
          exact H_k_strictMonoOn k hk;
        exact fun x hx y hy hxy => Real.rpow_lt_rpow ( show 0 ≤ H_k k x from by exact div_nonneg ( by { exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( by linarith [ Set.mem_Ici.mp hx ] ) ) ( by linarith [ Set.mem_Ici.mp hx ] ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ Set.mem_Ici.mp hx ] ) ) ) zero_le_one } ) ( by { exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ Set.mem_Ici.mp hx ] ) ) zero_le_one } ) ) ( h_comp_mono hx hy hxy ) ( by positivity );
      exact ⟨ hx, fun y hy => h_unique.eq_iff_eq hy.1 hx.1 |>.1 <| hy.2.trans hx.2.symm ⟩

/--
The unique zero x_k(s).
-/
def x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) : ℝ :=
  Classical.choose (exists_unique_x_k k hk s hs hks).exists

/--
The scaling function R_k(s) = B_k(x_k(s))^{1/k} / A_{k+1}(x_k(s))^{1/(k+1)}.
Defined using the x_k value that satisfies the uniqueness property[cite: 802].
-/
def R_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) : ℝ :=
  let x := x_k k hk s hs hks
  (B_d k x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))

lemma x_k_spec (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    x_k k hk s hs hks ≥ 0 ∧ (H_k k (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) = s :=
  Classical.choose_spec (exists_unique_x_k k hk s hs hks).exists

lemma H_k_le_lin (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
  H_k k x ≤ 1 + k * x := by
    rw [ H_k_eq, div_le_iff₀ ] <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ]

lemma x_k_ge_s_sub_one (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    x_k k hk s hs hks ≥ s - 1 := by
      -- By definition of $x_k$, we know that $H_k(x_k) = s^k$.
      set x := x_k k hk s hs hks
      have hx : (H_k k x) = s ^ k := by
        convert congr_arg ( · ^ k ) ( x_k_spec k hk s hs hks |>.2 ) using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( ?_ ) ] <;> norm_num [ show k ≠ 0 by linarith ];
        · rfl;
        · exact div_nonneg ( add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ) ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ) ( mul_nonneg ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ) ) zero_le_one ) ( add_nonneg ( mul_nonneg ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ( by linarith [ x_k_spec k hk s hs hks |>.1 ] ) ) zero_le_one );
      -- By definition of $H_k$, we know that $H_k(x) \leq 1 + kx$.
      have h_le : H_k k x ≤ 1 + k * x := by
        convert H_k_le_lin k hk x ( x_k_spec k hk s hs hks |>.1 ) using 1;
      -- By Bernoulli's inequality, $s^k \ge 1 + k(s-1)$.
      have h_bernoulli : s ^ k ≥ 1 + k * (s - 1) := by
        exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ pow_succ' ] ; nlinarith [ sq_nonneg ( s - 1 ) ] ; ;
      nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ) ]

def Q_poly (d : ℕ) (s x : ℝ) : ℝ :=
  2 * d * s * x^2 + (2 * s + d - s^2 * d - s^2) * x - (s - 1)

lemma Q_poly_nonneg (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ s - 1) :
  Q_poly d s x ≥ 0 := by
    -- Let's consider the two cases: $s \leq 1$ and $s > 1$.
    by_cases hs_le_one : s ≤ 1;
    · cases le_antisymm hs_le_one hs ; unfold Q_poly ; ring_nf ; positivity;
    · unfold Q_poly;
      -- Since $s > 1$, we have $Q(s-1) = (d - 1)(s - 1)^3 \geq 0$.
      have hQ_s_minus_1_nonneg : 2 * d * s * (s - 1) ^ 2 + (2 * s + d - s ^ 2 * d - s ^ 2) * (s - 1) - (s - 1) ≥ 0 := by
        nlinarith [ sq_nonneg ( s - 1 ), mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) ( sq_nonneg ( s - 1 ) ) ];
      nlinarith [ mul_le_mul_of_nonneg_left hx ( show ( 0 :ℝ ) ≤ d by positivity ), mul_le_mul_of_nonneg_left hx ( show ( 0 :ℝ ) ≤ s by positivity ), sq_nonneg ( x - ( s - 1 ) ), mul_le_mul_of_nonneg_left hx ( show ( 0 :ℝ ) ≤ s - 1 by linarith ), mul_le_mul_of_nonneg_left hx ( show ( 0 :ℝ ) ≤ d * s by positivity ) ]

def numerator_diff (d : ℕ) (s x : ℝ) : ℝ :=
  d * (d + 1) * s^2 * x^3 + (-d * (d + 1) * s^2 + d * (d + 3) * s) * x^2 + (2 * s + d - (d + 1) * s^2) * x - (s - 1)

lemma numerator_diff_eq (d : ℕ) (s x : ℝ) :
  numerator_diff d s x = Q_poly d s x + d * (d + 1) * s * x^2 * (s * x - s + 1) := by
  unfold numerator_diff Q_poly
  ring

def Num_poly (d : ℕ) (s x : ℝ) : ℝ :=
  (d * x + 1) * (d * (d + 1) * s^2 * x^2 + 2 * (d + 1) * s * x + 1) -
  (d * (d - 1) * x^2 + 2 * d * x + 1) * ((d + 1) * s^2 * x + s)

lemma Num_poly_eq_numerator_diff (d : ℕ) (s x : ℝ) :
  Num_poly d s x = numerator_diff d s x := by
  unfold Num_poly numerator_diff
  ring

lemma term_nonneg (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ s - 1) :
  d * (d + 1) * s * x^2 * (s * x - s + 1) ≥ 0 := by
    exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ( by positivity ) ) ( sq_nonneg _ ) ) ( by nlinarith [ sq_nonneg ( s - 1 ) ] )

lemma Num_poly_rel (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ 0)
  (hH : H_k d x = s ^ d) :
  Num_poly d s x = (d * x + 1) * ((d * (d + 1) * s^2 * x^2 + 2 * (d + 1) * s * x + 1) - s^(d+1) * ((d + 1) * s * x + 1)) := by
    -- Substitute the expression for the numerator of $H_k(x)$ from $hH$.
    have h_subst : (d * (d - 1) * x^2 + 2 * d * x + 1) = s^d * (d * x + 1) := by
      unfold H_k at hH;
      unfold A_d B_d at hH ; rw [ div_eq_iff ] at hH <;> ring_nf at * <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ d ) ];
    convert congr_arg ( fun y => ( d * x + 1 ) * ( d * ( d + 1 ) * s ^ 2 * x ^ 2 + 2 * ( d + 1 ) * s * x + 1 ) - y * ( ( d + 1 ) * s ^ 2 * x + s ) ) h_subst using 1 ; ring

lemma Num_poly_nonneg (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ s - 1) :
  Num_poly d s x ≥ 0 := by
  rw [ Num_poly_eq_numerator_diff, numerator_diff_eq ]
  have h_Q : Q_poly d s x ≥ 0 := Q_poly_nonneg d hd s hs x hx
  have h_term : d * (d + 1) * s * x^2 * (s * x - s + 1) ≥ 0 := term_nonneg d hd s hs x hx
  linarith

lemma H_d_plus_one_ge_s_pow_d_plus_one (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ s - 1)
  (hH : H_k d x = s ^ d) (hQ : Q_poly d s x ≥ 0) :
  H_k (d + 1) (s * x) ≥ s ^ (d + 1) := by
    -- By definition of $H_k$, we know that $H_k (d + 1) (s * x) = \frac{(d + 1) * d * (s * x)^2 + 2 * (d + 1) * (s * x) + 1}{(d + 1) * (s * x) + 1}$.
    have hH_def : H_k (d + 1) (s * x) = ((d + 1) * d * (s * x)^2 + 2 * (d + 1) * (s * x) + 1) / ((d + 1) * (s * x) + 1) := by
      convert H_k_eq ( d + 1 ) ( s * x ) using 1 ; push_cast ; ring;
    field_simp;
    rw [ hH_def, le_div_iff₀ ] <;> try nlinarith [ show 0 ≤ s * x by nlinarith ];
    -- By definition of $H_k$, we know that $H_k d x = s^d$ implies $s^d = \frac{d(d-1)x^2 + 2dx + 1}{dx + 1}$.
    have h_eq : s^d = (d * (d - 1) * x^2 + 2 * d * x + 1) / (d * x + 1) := by
      rw [ ← hH, H_k_eq ];
    rw [ pow_succ, h_eq ];
    rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> try nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ];
    have h_num_nonneg : numerator_diff d s x ≥ 0 := by
      convert Num_poly_nonneg d hd s hs x hx using 1;
      exact Eq.symm (Num_poly_eq_numerator_diff d s x);
    unfold numerator_diff at h_num_nonneg; linarith;

lemma H_d_plus_one_ge_s_pow_d_plus_one_aux (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (x : ℝ) (hx : x ≥ s - 1)
  (hH : H_k d x = s ^ d) (hQ : Q_poly d s x ≥ 0) :
  H_k (d + 1) (s * x) ≥ s ^ (d + 1) := by
    -- Apply the lemma that states if $H_d(x) = s^d$ and $Q_poly d s x \geq 0$, then $H_{d+1}(s*x) \geq s^{d+1}$.
    apply H_d_plus_one_ge_s_pow_d_plus_one d hd s hs x hx hH hQ

-- Part A: The technical derivative of the scaling function
/-
The derivative of log R_k(s) with respect to s for s > 1.
Matches equation (3.15) on page 11 of the paper:
∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)).
-/
/-
  USE THE FOLLOWING PROOF SKETCH:
  1. Expand log (R_k(s)) using the definition:
      log R_k(s) = (1/k) * log (B_k(x)) - (1/(k+1)) * log (A_{k+1}(x)), where x = x_k(s).
  2. Use the Chain Rule: d/ds [log R_k(s)] = (d/dx [log R_k(x)] * dx/ds).
  3. Calculate d/dx [log R_k(x)]:
      Since A_{k+1}(x) = (s^k + 2x)B_k(x), this simplifies to the expression in Eq (3.14):
      (s^k - 2(k-1)x - 2) / ((s^k + 2x) * B_k(x)).
  4. Find the implicit derivative dx/ds:
      Differentiate the relation A_k(x) = s^k * B_k(x) with respect to s.
      Rearranging gives dx/ds = (s^(k-1) * B_k(x)) / (2(k-1)x + 2 - s^k).
  5. Multiply the results from Step 3 and Step 4:
      The terms (2(k-1)x + 2 - s^k) cancel out, leaving exactly -s^(k-1) / (s^k + 2x_k(s)).
  -/
-- lemma log_Rk_diff (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) :
--     deriv (λ u => log (R_k k hk u (le_of_lt hs))) s =
--     -s ^ (k - 1) / (s ^ k + 2 * x_k k hk s (le_of_lt hs)) := by
--   sorry -- Based on implicit differentiation of H_k(x_k(s)) = s^k [cite: 805, 807]

-- Part B: The comparison of the zero-points
/--
The comparison of unique zeros x_k(s).
Matches the requirement for equation (3.15) to imply monotonicity: x_{d+1}(s) ≤ s * x_d(s).
-/
lemma x_k_comparison (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (hds : d = 1 → s < 2) :
    x_k (d + 1) (by linarith) s hs (by intro h; linarith) ≤ s * x_k d hd s hs hds := by
      have h_unique : ∃ x : ℝ, x ≥ 0 ∧ (H_k d x) ^ (1 / (d : ℝ)) = s ∧ (H_k (d + 1) (s * x)) ^ (1 / ((d + 1) : ℝ)) ≥ s := by
        have h_unique : ∃ x : ℝ, x ≥ 0 ∧ (H_k d x) ^ (1 / (d : ℝ)) = s := by
          exact ExistsUnique.exists ( exists_unique_x_k d hd s hs fun h => by aesop ) |> fun ⟨ x, hx ⟩ => ⟨ x, hx.1, hx.2 ⟩
        generalize_proofs at *;
        obtain ⟨ x, hx₁, hx₂ ⟩ := h_unique
        generalize_proofs at *;
        have h_unique : H_k (d + 1) (s * x) ≥ s ^ (d + 1) := by
          apply H_d_plus_one_ge_s_pow_d_plus_one_aux d hd s hs x (by
          have := x_k_ge_s_sub_one d hd s hs hds
          generalize_proofs at *;
          have h_unique : x_k d hd s hs hds = x := by
            apply ExistsUnique.unique (exists_unique_x_k d hd s hs hds) (x_k_spec d hd s hs hds) ⟨hx₁, hx₂⟩
          generalize_proofs at *;
          linarith) (by
          rw [ ← hx₂, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact le_of_lt ( show 0 < H_k d x from by exact div_pos ( by exact add_pos_of_nonneg_of_pos ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hd ) ) ) ( by positivity ) ) ( by positivity ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) ) zero_lt_one ) ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) ( by positivity ) ) zero_lt_one ) ) ), one_div_mul_cancel ( by positivity ), Real.rpow_one ]) (by
          apply Q_poly_nonneg d hd s hs x (by
          have := x_k_ge_s_sub_one d hd s hs hds
          generalize_proofs at *;
          have h_unique : x_k d hd s hs hds = x := by
            apply ExistsUnique.unique (exists_unique_x_k d hd s hs hds) (x_k_spec d hd s hs hds) ⟨hx₁, hx₂⟩
          generalize_proofs at *;
          linarith))
        generalize_proofs at *;
        exact ⟨ x, hx₁, hx₂, by exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), Nat.cast_add_one, mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) h_unique ( by positivity ) ) ⟩
      generalize_proofs at *;
      obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_unique
      have hx₄ : x_k d hd s hs hds = x := by
        apply ExistsUnique.unique (exists_unique_x_k d hd s hs hds) (x_k_spec d hd s hs hds) ⟨hx₁, hx₂⟩
      have hx₅ : x_k (d + 1) ‹_› s hs ‹_› ≤ s * x := by
        have hx₅ : ∀ y : ℝ, y ≥ 0 → (H_k (d + 1) y) ^ (1 / ((d + 1) : ℝ)) ≥ s → x_k (d + 1) ‹_› s hs ‹_› ≤ y := by
          intros y hy₁ hy₂
          generalize_proofs at *;
          have hx₅ : StrictMonoOn (fun x => (H_k (d + 1) x) ^ (1 / ((d + 1) : ℝ))) (Set.Ici 0) := by
            have hx₅ : StrictMonoOn (fun x => H_k (d + 1) x) (Set.Ici 0) := by
              exact H_k_strictMonoOn _ ( by linarith )
            generalize_proofs at *;
            exact fun x hx y hy hxy => Real.rpow_lt_rpow ( show 0 ≤ H_k ( d + 1 ) x from by exact div_nonneg ( by exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr <| Nat.one_le_cast.mpr <| by linarith ) ) <| by aesop ) <| by aesop ) <| mul_nonneg ( Nat.cast_nonneg _ ) <| by aesop ) zero_le_one ) <| by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) <| by aesop ) zero_le_one ) ( hx₅ hx hy hxy ) <| by positivity;
          generalize_proofs at *;
          exact hx₅.le_iff_le ( show 0 ≤ x_k ( d + 1 ) ‹_› s hs ‹_› from by have := x_k_spec ( d + 1 ) ‹_› s hs ‹_›; aesop ) hy₁ |>.1 <| by have := x_k_spec ( d + 1 ) ‹_› s hs ‹_›; aesop;
        generalize_proofs at *;
        exact hx₅ _ ( mul_nonneg ( by positivity ) hx₁ ) hx₃
      rw [hx₄] at *
      exact hx₅

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
  USE THE FOLLOWING PROOF SKETCH:
  1. Let w₀, w₁ be the terms defined in the lemma. The goal (w₀, w₁, w₁) ∈ S_Δ
     means showing w₀ + w₁x + w₁y ≥ A_{Δ+1}(x,y)^{1/(Δ+1)} for all x,y ≥ 0. [cite: 124, 190]
  2. Use the zero-finding logic from page 11: define s := H_d(η)^{1/d} and find
     a unique α ≥ 0 such that H_Δ(α)^{1/Δ} = s. Note that s ≥ 1, and if d = 1, then s < 2. [cite: 221]
  3. Define a comparison triple (a₀, a₁, a₁) where a₁ := B_Δ(α)^{1/Δ} / A_{Δ+1}(α)^{1/(Δ+1)}
     and a₀ := A_Δ(α)^{1/Δ} / A_{Δ+1}(α)^{1/(Δ+1)}. [cite: 217]
  4. Note that (a₀, a₁, a₁) is on the boundary of S_Δ because it represents the
     tangent plane to z = A_{Δ+1}(x,y)^{1/(Δ+1)} at (α, α). [cite: 140, 155]
  5. By the concavity of A_{Δ+1}^{1/(Δ+1)}, the tangent plane satisfies
     a₀ + a₁x + a₁y ≥ A_{Δ+1}(x,y)^{1/(Δ+1)}. [cite: 141, 154]
  6. Apply Monotonicity (Item 7 Expansion):
     - From ∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)) and x_k_comparison, we have R_Δ(s) ≤ R_d(s) since Δ ≥ d. [cite: 227, 218]
     - By definition, w₁ = R_d(s)^Δ and a₁ = R_Δ(s)^Δ, so w₁ ≥ a₁. [cite: 190, 217, 223]
     - Since H_d(η)^{1/d} = H_Δ(α)^{1/Δ} = s, the "base" terms satisfy
       w₀ = w₁ * s^Δ and a₀ = a₁ * s^Δ.
     - Because w₁ ≥ a₁ and s ≥ 1, it follows that w₀ ≥ a₀.
  7. Since w₀ ≥ a₀ and w₁ ≥ a₁, the degree d plane (w₀ + w₁x + w₁y) is
     point-wise greater than or equal to the tangent plane (a₀ + a₁x + a₁y). [cite: 214, 215]
  8. Since the tangent plane already bounds the partition function from above,
     the degree d plane also satisfies the membership condition for S_Δ. [cite: 141, 154, 213]
  -/
  sorry -- Uses monotonicity derived from Part A and Part B [cite: 803, 808, 791]

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
  PROOF SKETCH:
  1. Define the weight triple w = (w₀, w₁, w₂) using the powers of A_d, B_d, and A_{d+1}
     as stated in the lemma.
  2. Handle the case w₁w₂ = 1: This implies η = μ = 0 by Proposition 3.7. The triple
     becomes (1, 1, 1), which is in S_Δ because (1+x+y)^{Δ+1} ≥ A_{Δ+1}(x,y)[cite: 193, 194].
  3. Reduction to the Symmetric Case (w₁w₂ < 1):
     - The goal is w₀ ≥ Φ_Δ(w₁, w₂). By Lemma 3.5, it suffices to show that
       w₀ - (w₁ + w₂)/Δ ≥ Ψ_Δ(w₁w₂)[cite: 196].
     - Treat w₀, w₁, w₂ as functions of B := B_d(μ) and C := B_d(η). Note that
       the product BC is proportional to w₁w₂[cite: 197].
     - Fix the product BC = K² and define B(t) = Keᵗ, C(t) = Ke⁻ᵗ[cite: 199, 200].
  4. Analyze the Derivative:
     - Compute the derivative of f(t) = w₀(t) - (w₁(t) + w₂(t))/Δ.
     - Show f'(t) = d⁻¹(p(B-C)A^{p-1} - (Bᵖ - Cᵖ))D^{-Δ/(d+1)}[cite: 203].
     - Since A ≥ B ≥ C, this derivative is non-negative for t ≥ 0.
  5. Minimum at Symmetry:
     - The expression is minimized when t = 0, which corresponds to B = C (i.e., η = μ).
     - At this minimum, the inequality reduces exactly to the symmetric case:
       w₀(K,K) - Φ_Δ(w₁(K,K), w₂(K,K))[cite: 205].
  6. Final Invocation:
     - Apply SΔ_membership_symmetric to confirm that the symmetric triple is in S_Δ[cite: 207].
     - Since the multivariate case dominates the symmetric case, the general triple
       (w₀, w₁, w₂) must also be in S_Δ.
  -/
  sorry
