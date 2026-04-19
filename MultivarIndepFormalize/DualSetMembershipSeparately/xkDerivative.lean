import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison

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
The implicit derivative of the zero-finding function x_k(s) for s > 1.
Matches equation (3.14) on page 11.
-/

/-
The derivative of H_k(x) with respect to x.
-/
lemma H_k_deriv (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ≥ 0) :
    HasDerivAt (H_k k) (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2) x := by
  convert HasDerivAt.div ( HasDerivAt.comp x ( show HasDerivAt ( fun x : ℝ => ( k : ℝ ) * ( k - 1 ) * x ^ 2 + 2 * k * x + 1 ) _ _ from HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_pow 2 _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_id _ ) ) ( HasDerivAt.comp x ( show HasDerivAt ( fun x : ℝ => ( k : ℝ ) * x + 1 ) _ _ from HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_id _ ) ) ?_ using 1 <;> norm_num ; ring;
  · ext x; unfold H_k A_d B_d; ring;
    simpa [ div_eq_mul_inv ] using by ring;
  · ring;
  · positivity

/-
Algebraic identity required for the derivative of x_k(s).
-/
set_option linter.unusedVariables false in
lemma deriv_x_k_algebraic_identity (k : ℕ) (hk : 1 ≤ k) (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s)
    (h_eq : H_k k x = s ^ k) :
    k * s ^ (k - 1) / (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2) =
    s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k) := by
  unfold H_k B_d at *;
  rw [ div_eq_iff ] at h_eq;
  · rw [ div_div_eq_mul_div, div_eq_div_iff ];
    · unfold A_d at h_eq;
      grind;
    · exact mul_ne_zero ( by positivity ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, sq_nonneg ( ( k : ℝ ) * x + 1 ) ] );
    · unfold A_d at h_eq;
      nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * x ≥ 0 by positivity, show ( k : ℝ ) * x ^ 2 ≥ 0 by positivity, show ( k : ℝ ) ^ 2 * x ≥ 0 by positivity, show ( k : ℝ ) ^ 2 * x ^ 2 ≥ 0 by positivity, pow_pos hs k ];
  · positivity

/-
Extension of x_k to the whole real line (0 outside valid range).
-/
def x_k_ext (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : ℝ :=
  if h : 1 ≤ t ∧ (k = 1 → t < 2) then x_k k hk t h.1 h.2 else 0

/-
x_k_ext is a local right inverse of H_k^(1/k).
-/
lemma x_k_ext_is_inverse (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    ∀ᶠ t in nhds s, (H_k k (x_k_ext k hk t)) ^ (1 / (k : ℝ)) = t := by
  have h_neighborhood : ∀ᶠ t in nhds s, 1 ≤ t ∧ (k = 1 → t < 2) := by
    by_cases hk1 : k = 1 <;> simp_all +decide;
    · exact ⟨ Ici_mem_nhds hs, Iio_mem_nhds hks ⟩;
    · exact Ici_mem_nhds hs;
  filter_upwards [ h_neighborhood ] with t ht using by rw [ show x_k_ext k hk t = x_k k hk t ht.1 ht.2 from by unfold x_k_ext; aesop ] ; exact ( x_k_spec k hk t ht.1 ht.2 ) |>.2;

/-
Definition of f_k and its strict monotonicity.
-/
def f_k (k : ℕ) (x : ℝ) : ℝ := (H_k k x) ^ (1 / (k : ℝ))

lemma f_k_strictMonoOn (k : ℕ) (hk : 1 ≤ k) : StrictMonoOn (f_k k) (Set.Ici 0) := by
  intro x hx y hy hxy;
  have h_pos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x < y → H_k k x < H_k k y := by
    exact fun x y hx hy hxy => H_k_strictMonoOn k hk hx hy hxy;
  have h_pos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x < y → (H_k k x) ^ (1 / (k : ℝ)) < (H_k k y) ^ (1 / (k : ℝ)) := by
    exact fun x y hx hy hxy => Real.rpow_lt_rpow ( show 0 ≤ H_k k x from by rw [ H_k_eq ] ; exact div_nonneg ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * ( k - 1 ) * x ^ 2 ≥ 0 by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( sq_nonneg _ ) ] ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * x ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) hx ] ) ) ( h_pos x y hx hy hxy ) ( by positivity );
  convert h_pos x y hx hy hxy using 1

/-
Continuity of f_k on [0, \infty).
-/
lemma f_k_continuousOn (k : ℕ) (hk : 1 ≤ k) : ContinuousOn (f_k k) (Set.Ici 0) := by
  refine ContinuousOn.rpow ( ContinuousOn.div ?_ ?_ ?_ ) ?_ ?_ <;> norm_num;
  · exact Continuous.continuousOn ( by unfold A_d; continuity );
  · exact Continuous.continuousOn ( by unfold B_d; continuity );
  · exact fun x hx => by unfold B_d; positivity;
  · exact continuousOn_const;
  · exact fun x hx => Or.inr hk

/-
Definitions of DomainK and RangeK.
-/
def DomainK (k : ℕ) : Set ℝ := {s | 1 ≤ s ∧ (k = 1 → s < 2)}
def RangeK : Set ℝ := Set.Ici 0

/-
f_k maps [0, \infty) into DomainK.
-/
lemma f_k_mem_DomainK (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    f_k k x ∈ DomainK k := by
      -- Since $H_k$ is strictly increasing on $[0, \infty)$ and $H_k(0) = 1$, we have $H_k(x) \geq 1$ for all $x \geq 0$.
      have h_Hk_ge_one : ∀ x : ℝ, 0 ≤ x → H_k k x ≥ 1 := by
        intro x hx
        have h_Hk_ge_one : H_k k x ≥ H_k k 0 := by
          exact H_k_strictMonoOn k hk |> fun h => h.le_iff_le ( by norm_num ) ( by assumption ) |>.2 hx;
        exact le_trans ( by norm_num [ H_k_eq ] ) h_Hk_ge_one;
      refine' ⟨ _, _ ⟩;
      · exact Real.one_le_rpow ( h_Hk_ge_one x hx ) ( by positivity );
      · unfold f_k; intro hk'; rcases eq_or_ne k 1 with rfl | hk' <;> simp_all +decide [ H_k ] ;
        unfold A_d B_d; norm_num; rw [ div_lt_iff₀ ] <;> nlinarith;

/-
Order isomorphism between RangeK and DomainK using the strictly monotonic function f_k and its inverse x_k.
-/
noncomputable def g_iso (k : ℕ) (hk : 1 ≤ k) : ↥(RangeK) ≃o ↥(DomainK k) :=
  StrictMono.orderIsoOfRightInverse
    (fun x => ⟨f_k k x, f_k_mem_DomainK k hk x x.2⟩)
    (fun x y h => f_k_strictMonoOn k hk x.2 y.2 h)
    (fun s => ⟨x_k k hk s s.2.1 s.2.2, (x_k_spec k hk s s.2.1 s.2.2).1⟩)
    (fun s => Subtype.ext (x_k_spec k hk s s.2.1 s.2.2).2)

/-
DomainK is a neighborhood of s.
-/
lemma DomainK_mem_nhds (k : ℕ) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
  DomainK k ∈ nhds s := by
    rcases eq_or_ne k 1 <;> simp_all +contextual [ DomainK ];
    · exact Ico_mem_nhds hs hks;
    · exact Filter.mem_of_superset ( Ioi_mem_nhds hs ) fun x hx => hx.out.le

/-
x_k_ext agrees with the inverse of the isomorphism on the domain.
-/
lemma x_k_ext_eq_iso_symm (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : t ∈ DomainK k) :
  x_k_ext k hk t = ((g_iso k hk).symm ⟨t, ht⟩).val := by
    unfold x_k_ext;
    -- By definition of $g_iso$, we know that $g_iso k hk (x_k k hk t ...) = ⟨t, ht⟩$.
    have h_g_iso : g_iso k hk (⟨x_k k hk t ht.1 ht.2, (x_k_spec k hk t ht.1 ht.2).1⟩ : ↥(RangeK)) = ⟨t, ht⟩ := by
      exact Subtype.ext ( x_k_spec k hk t ht.1 ht.2 |>.2 );
    rw [ ← h_g_iso, OrderIso.symm_apply_apply ];
    grind

/-
Continuity of the inverse isomorphism.
-/
lemma g_iso_symm_continuous (k : ℕ) (hk : 1 ≤ k) : Continuous (g_iso k hk).symm := by
  have h_iso_cont : Continuous (g_iso k hk).symm := by
    have h_subspace : OrderTopology (DomainK k) := by
      have h_order_top : OrderTopology (Set.Ici (1 : ℝ)) := by
        infer_instance;
      rcases k with ( _ | _ | k ) <;> norm_num at *;
      · rw [ show DomainK 1 = Set.Ico 1 2 from ?_ ];
        · infer_instance;
        · ext; simp [DomainK];
      · convert h_order_top using 1;
        · congr with x ; simp +decide [ DomainK ];
        · congr! 1;
          ext; simp [DomainK];
        · congr! 1;
          ext; simp [DomainK]
    have h_subspace_range : OrderTopology (RangeK) := by
      simp [RangeK];
      infer_instance
    exact OrderIso.continuous (g_iso k hk).symm;
  exact h_iso_cont

/-
Continuity of x_k_ext on DomainK.
-/
lemma x_k_ext_continuousOn_DomainK (k : ℕ) (hk : 1 ≤ k) :
  ContinuousOn (x_k_ext k hk) (DomainK k) := by
    -- Rewrite the restriction of `x_k_ext` to `DomainK k` using `x_k_ext_eq_iso_symm`.
    have h_restrict : Set.restrict (DomainK k) (x_k_ext k hk) = (fun t => ((g_iso k hk).symm t).val) ∘ (fun t => ⟨t, t.2⟩ : ↥(DomainK k) → ↥(DomainK k)) := by
      exact funext fun x => x_k_ext_eq_iso_symm k hk x x.2;
    convert h_restrict.symm ▸ Continuous.comp _ _ using 1;
    · exact continuousOn_iff_continuous_restrict;
    · exact Continuous.comp ( continuous_subtype_val ) ( g_iso_symm_continuous k hk );
    · fun_prop (disch := solve_by_elim)

/-
Continuity of x_k_ext at s.
-/
lemma x_k_ext_continuousAt (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
  ContinuousAt (x_k_ext k hk) s := by
    exact ContinuousAt.congr ( x_k_ext_continuousOn_DomainK k hk |> ContinuousOn.continuousAt <| Filter.mem_of_superset ( DomainK_mem_nhds k s hs hks ) <| Set.Subset.refl _ ) <| Filter.eventually_of_mem ( DomainK_mem_nhds k s hs hks ) fun x hx => by aesop;

/-
Derivative of f_k.
-/
lemma f_k_hasDerivAt (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ≥ 0) :
  HasDerivAt (f_k k) ((1 / (k : ℝ)) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2)) x := by
    convert HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ using 1 <;> norm_num;
    · rw [ H_k_deriv k hk x hx |> HasDerivAt.deriv ] ; ring;
    · unfold H_k;
      unfold A_d B_d; norm_num [ mul_comm, hx ];
      exact DifferentiableAt.div ( by norm_num ) ( by norm_num ) ( by positivity );
    · exact Or.inl <| div_ne_zero ( by unfold A_d; exact ne_of_gt <| by cases k <;> norm_num [ A_d ] at * ; positivity ) ( by unfold B_d; exact ne_of_gt <| by cases k <;> norm_num [ B_d ] at * ; positivity )

lemma deriv_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let x_ext : ℝ → ℝ := fun t => if ht : (1 ≤ t) ∧ (k = 1 → t < 2) then
        x_k k hk t ht.1 ht.2
      else
        0
    let x := x_ext s
    HasDerivAt x_ext
      (s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)) s := by
  /-
  PROOF STRATEGY:
  1. Use the relation A_k(x) = s^k * B_k(x) from the definition of x_k[cite: 990].
  2. Apply the Implicit Function Theorem or 'HasDerivAt.deriv_comp' to the
     identity H_k(x_k(s)) = s^k[cite: 990].
  3. Differentiate both sides with respect to s:
     H_k'(x) * dx/ds = k * s^(k-1)[cite: 695, 990].
  4. Substitute the expression for H_k' from Equation (3.11) and solve for dx/ds[cite: 680, 990].
  -/
  set x_ext := fun t => if ht : 1 ≤ t ∧ (k = 1 → t < 2) then x_k k hk t ht.1 ht.2 else 0
  set x := x_ext s
  have hx : x ≥ 0 := by
    simp +zetaDelta at *;
    split_ifs <;> [ exact ( x_k_spec k hk s hs.le hks ) |>.1; exact le_rfl ]
  have hx_s : H_k k x = s ^ k := by
    -- By definition of $x_k$, we know that $H_k k x = s^k$.
    have hx_eq : (H_k k x) ^ (1 / (k : ℝ)) = s := by
      convert x_k_spec k hk s hs.le ( by aesop ) |>.2;
      grind;
    rw [ ← hx_eq, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact ( show 0 ≤ H_k k x from by exact ( by rw [ H_k_eq ] ; exact div_nonneg ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * ( k - 1 ) ≥ 0 by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ] ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ) ), one_div_mul_cancel ( by positivity ), Real.rpow_one ]
  have hx_deriv : HasDerivAt (fun t => x_ext t) (s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)) s := by
    have hx_deriv : HasDerivAt (fun t => x_ext t) (1 / ((1 / k) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2))) s := by
      have h_inv_deriv : HasDerivAt (fun t => f_k k t) ((1 / k) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2)) x := by
        convert f_k_hasDerivAt k hk x hx using 1;
      have := @HasDerivAt.of_local_left_inverse;
      convert this ( show ContinuousAt x_ext s from ?_ ) h_inv_deriv ?_ ?_ using 1;
      · simp only [one_div, mul_inv_rev, inv_div, inv_inv]
      · convert x_k_ext_continuousAt k hk s hs hks using 1;
      · simp +zetaDelta at *;
        refine' ⟨ ⟨ by linarith, _ ⟩, ⟨ by linarith, _ ⟩, _ ⟩;
        · exact ne_of_gt ( Real.rpow_pos_of_pos ( by rw [ hx_s ] ; positivity ) _ );
        · split_ifs <;> norm_num;
          nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( x_k k hk s ( by linarith ) ( by tauto ) : ℝ ) ≥ 0 by exact ( x_k_spec k hk s ( by linarith ) ( by tauto ) ) |>.1, mul_nonneg ( show ( k : ℝ ) ≥ 0 by positivity ) ( sq_nonneg ( x_k k hk s ( by linarith ) ( by tauto ) : ℝ ) ) ];
        · split_ifs <;> linarith [ show ( k : ℝ ) * x_k k hk s ( by linarith ) ( by aesop ) ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact ( x_k_spec k hk s ( by linarith ) ( by aesop ) ) |>.1 ) ];
      · convert x_k_ext_is_inverse k hk s hs hks using 1;
    convert hx_deriv using 1;
    convert deriv_x_k_algebraic_identity k hk x s hx ( by linarith ) hx_s |> Eq.symm using 1;
    rcases k with ( _ | k ) <;> simp_all +decide;
    rw [ ← Real.rpow_natCast _ ( k + 1 ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ Nat.cast_add_one_ne_zero ] ; ring;
    rw [ show ( -1 - ( k : ℝ ) + ( k : ℝ ) * ( 1 + ( k : ℝ ) ) ⁻¹ + ( 1 + ( k : ℝ ) ) ⁻¹ ) = -k by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 + ( k : ℝ ) ) ≠ 0 ) ] ] ; norm_num [ Real.rpow_neg ( by positivity : 0 ≤ s ) ] ; ring;
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
  exact hx_deriv
