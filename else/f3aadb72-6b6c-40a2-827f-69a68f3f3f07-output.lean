/-
**Lemma 3.5** `lem:Phi-upper-bound`
Φ_Δ(a₁, a₂) is essentially upper bounded in terms of a₁a₂.

**Claim 3.6**
f has a unique zero ξ on (1,∞).

**Proposition 3.7** `prop:basic-ineq-2`
-/


import MultivarIndepFormalize.Definitions

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
**Claim 3.6**
f has a unique zero ξ on (1,∞).

**Statement**
For \(0< s<1\), $f(X)$ has a unique zero \(\xi_\Delta (s)\) on \((1,\infty)\).

f(X) is f_poly and defined as (Δ+1)a_1a_2 X^{2Δ} - Δ X^{Δ+1} - 1
-/
noncomputable section AristotleLemmas

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
The first term (Δ+1)s X^(Δ-1) is increasing because Δ ≥ 2 implies Δ-1 > 0.
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

end AristotleLemmas

lemma xi_unique_zero (Δ : ℕ) (hΔ : Δ ≥ 2) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) :
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
def xi_Δ (Δ : ℕ) (hΔ : Δ ≥ 2) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) : ℝ :=
  (xi_unique_zero Δ hΔ s hs₀ hs₁).choose

/--
The auxiliary function Ψ_Δ(s) = ξ_Δ(s) - (2/Δ) * s * ξ_Δ(s)^Δ.
Matches source definition.
-/
def Psi_Delta (Δ : ℕ) (hΔ : Δ ≥ 2) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) : ℝ :=
  let ξ := xi_Δ Δ hΔ s hs₀ hs₁
  ξ - (2 / (Δ : ℝ)) * s * ξ ^ (Δ : ℝ)

/- Aristotle failed to find a proof. -/
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
lemma Phi_upper_bound (Δ : ℕ) (hΔ : Δ ≥ 2) (a₁ a₂ : ℝ)
    (ha₁ : a₁ > 0) (ha₂ : a₂ > 0) (h_prod : a₁ * a₂ < 1) :
    let s := a₁ * a₂
    let hs₀ : 0 < s := by simpa [s] using (mul_pos ha₁ ha₂)
    let hs₁ : s < 1 := by simpa [s] using h_prod
    let Ψ_Δ := Psi_Delta Δ hΔ
    let Ψ_Δ_s := Ψ_Δ s hs₀ hs₁
    Φ_Δ Δ a₁ a₂ ≤ Ψ_Δ_s + (a₁ + a₂) / (Δ : ℝ) ∧
    (a₁ = a₂ → Φ_Δ Δ a₁ a₂ = Ψ_Δ_s + (a₁ + a₂) / (Δ : ℝ)) := by
  sorry

/--
**Proposition 3.7** `prop:basic-ineq`

**Statement**
Let \(d\ge1\) and \(x,y\ge0\). Then
\(
  (dx+1)^{d+1} (dy+1)^{d+1} \le \bigl( (d+1)dxy + (d+1)(x+y) + 1 \bigr)^{2d}
\).
Equality holds if and only if \(x=y=0\).
-/
lemma basic_ineq (d : ℕ) (hd : d ≥ 1) (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) :
    ((d : ℝ) * x + 1) ^ ((d : ℝ) + 1) * ((d : ℝ) * y + 1) ^ ((d : ℝ) + 1) ≤
    ((d + 1 : ℝ) * d * x * y + (d + 1 : ℝ) * (x + y) + 1) ^ (2 * (d : ℝ)) ∧
    (((d : ℝ) * x + 1) ^ ((d : ℝ) + 1) * ((d : ℝ) * y + 1) ^ ((d : ℝ) + 1) =
    ((d + 1 : ℝ) * d * x * y + (d + 1 : ℝ) * (x + y) + 1) ^ (2 * (d : ℝ)) ↔ x = 0 ∧ y = 0) := by
  constructor;
  · norm_cast ; norm_num [ mul_pow ];
    rw [ ← mul_pow ];
    refine' le_trans ( pow_le_pow_left₀ ( by positivity ) ( show ( ( d : ℝ ) * x + 1 ) * ( ( d : ℝ ) * y + 1 ) ≤ ( ( d + 1 ) * ( d : ℝ ) * x * y + ( d + 1 ) * ( x + y ) + 1 ) by nlinarith [ mul_nonneg hx hy, mul_nonneg hx ( sq_nonneg y ), mul_nonneg hy ( sq_nonneg x ) ] ) _ ) _;
    exact pow_le_pow_right₀ ( by nlinarith [ mul_nonneg hx hy, mul_nonneg ( Nat.cast_nonneg d ) hx, mul_nonneg ( Nat.cast_nonneg d ) hy ] ) ( by linarith );
  · constructor;
    · contrapose!;
      -- Assume $x \neq 0$ or $y \neq 0$. Without loss of generality, assume $x \neq 0$.
      intro hxy
      by_cases hx0 : x = 0;
      · rcases d with ( _ | _ | d ) <;> simp_all +decide;
        · norm_num; nlinarith [ mul_self_pos.2 hxy ];
        · norm_cast;
          refine' ne_of_lt ( lt_of_lt_of_le _ ( pow_le_pow_right₀ ( by nlinarith [ show ( 0 : ℝ ) < y by positivity ] ) ( show 2 * ( d + 1 + 1 ) ≥ d + 1 + 1 + 1 by linarith ) ) );
          gcongr ; norm_num;
      · by_cases hy0 : y = 0 <;> simp_all +decide [ Real.rpow_add, Real.rpow_mul ];
        · norm_cast ; norm_num [ pow_mul' ];
          rw [ ← pow_mul' ];
          refine' ne_of_lt ( lt_of_lt_of_le _ ( pow_le_pow_right₀ ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast ] ) ( show d + 1 ≤ 2 * d by linarith ) ) );
          gcongr ; nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show x > 0 by positivity ];
        · -- By simplifying, we can see that the inequality holds strictly for $x, y > 0$.
          have h_simp : ((d * x + 1) * (d * y + 1)) ^ (d + 1 : ℝ) < (((d + 1) * d * x * y + (d + 1) * (x + y) + 1) ^ (2 * d : ℝ)) := by
            field_simp;
            -- By simplifying, we can see that the inequality holds strictly for $x, y > 0$ because the right-hand side grows faster than the left-hand side.
            have h_simp : ((d * x + 1) * (d * y + 1)) < ((d + 1) * (d * x * y + (x + y)) + 1) := by
              nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, show 0 < x * y by positivity, show 0 < x by positivity, show 0 < y by positivity, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) hx, mul_le_mul_of_nonneg_left ( show ( d : ℝ ) ≥ 1 by norm_cast ) hy ];
            exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( by positivity ) h_simp ( by positivity ) ) ( Real.rpow_le_rpow_of_exponent_le ( by nlinarith [ show ( d : ℝ ) ≥ 1 by norm_cast, mul_nonneg hx hy ] ) ( by norm_cast; linarith ) );
          rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; exact ne_of_lt h_simp;
    · aesop
