import MultivarIndepFormalize.Definitions

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
