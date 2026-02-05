/-
**Lemma 3.5** `lem:Phi-upper-bound` (Phi_upper_bound)
Φ_Δ(a₁, a₂) is essentially upper bounded in terms of a₁a₂.

**Claim 3.6** (xi_unique_zero)
f has a unique zero ξ on (1,∞).
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.TechnicalLemmas

set_option linter.style.longLine false

open Real

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
      rw [ sub_div', div_eq_iff ] <;> first | positivity | ring;
      norm_num [ Real.rpow_add hX, Real.rpow_neg_one ] ; ring;
      norm_cast ; simp +decide [ sq, mul_assoc, mul_comm, mul_left_comm, hX.ne' ];
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
      convert h_term1.atTop_add h_term2 using 1 ; ring;
      ext; unfold h_aux; ring


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
lemma critical_point_in_Ω (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
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
  sorry

/--
The value at the critical point provides an upper bound for the variation of A_{Δ+1}^{1/(Δ+1)}.
Matches page 9, Equation 3.7.
-/
lemma variational_upper_bound (Δ : ℕ) (hΔ : 2 ≤ Δ) (a₁ a₂ : ℝ) (ha₁ : a₁ > 0) (ha₂ : a₂ > 0) (ha₁a₂ : a₁ * a₂ < 1)
    (x_star y_star : ℝ) (ξ : ℝ) (h_A : A_d (Δ + 1) x_star y_star = ξ ^ (Δ + 1)) :
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
  sorry

/--
In the symmetric case a₁ = a₂, the maximum is attained at x_* = y_* > 0.
Matches page 9.
-/
lemma symmetric_equality (Δ : ℕ) (hΔ : 2 ≤ Δ) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    let s := a * a
    let hs₀ : 0 < s := by aesop
    let hs₁ : s < 1 := by nlinarith
    let ξ := xi_Δ Δ hΔ s hs₀ hs₁
    let x_star := (a * ξ ^ Δ - 1) / Δ
    x_star > 0 ∧ Φ_Δ Δ a a = Psi_Delta Δ hΔ s hs₀ hs₁ + (2 * a) / Δ := by
  /-
  PROOF STRATEGY:
  1. Use a * ξ^Δ > 1 (from root property) to prove x_star = y_star > 0. [cite: 183, 615]
  2. Since the critical point is in the interior of (ℝ≥0)², the supremum is attained here.
  3. Verify the equality matches the target expression.
  -/
  sorry

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
  sorry
