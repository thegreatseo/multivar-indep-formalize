import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk

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
