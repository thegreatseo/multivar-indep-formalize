-- Harmonic `generalize_proofs` tactic

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison
import MultivarIndepFormalize.DualSetMembershipSeparately.DualSetMembershipSymmetric

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Real (exp log sqrt)

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/--
The multivariate weight triple (w₀, w₁, w₂).
Matches Equation (3.9) on page 9 of the paper.
-/
def weight_triple (Δ d : ℕ) (η μ : ℝ) : ℝ × ℝ × ℝ :=
  let p : ℝ := (Δ : ℝ) / (d : ℝ)
  let q : ℝ := (Δ : ℝ) / ((d : ℝ) + 1)
  let Ad := A_d d η μ
  let Bdμ := B_d d μ
  let Bdη := B_d d η
  let Ad_next := A_d (d + 1) η μ
  (Ad ^ p / Ad_next ^ q, Bdμ ^ p / Ad_next ^ q, Bdη ^ p / Ad_next ^ q)

/--
The derivative of the difference f(t) = w₀(t) - (w₁(t) + w₂(t))/Δ.
Matches the logic on page 10.
-/
lemma deriv_weight_difference (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (K : ℝ) (hK : K > 0) (D : ℝ) (hD : D > 0) (t : ℝ) :
    let p := (Δ : ℝ) / (d : ℝ)
    let B := K * exp t
    let C := K * exp (-t)
    let A := ((d - 1) * K ^ 2 + B + C - 1) / d
    let f := λ u =>
      let Bu := K * exp u
      let Cu := K * exp (-u)
      let Au := ((d - 1) * K ^ 2 + Bu + Cu - 1) / d
      (Au ^ p - (Bu ^ p + Cu ^ p) / Δ) * D ^ (-(Δ : ℝ) / (d + 1))
    HasDerivAt f ((d : ℝ)⁻¹ * (p * (B - C) * A ^ (p - 1) - (B ^ p - C ^ p)) * D ^ (- (Δ : ℝ) / (d + 1))) t := by
  /-
  PROOF STRATEGY:
  1. Use 'HasDerivAt' rules for exponentials and powers.
  2. Differentiate A(t) with respect to t: dA/dt = (B - C) / d. [cite: 202, 650]
  3. Differentiate (B^p + C^p) with respect to t: d(B^p + C^p)/dt = p(B^p - C^p). [cite: 202, 650]
  4. Combine using the Chain Rule to obtain the target derivative expression. [cite: 203, 652]
  -/
  refine HasDerivAt.mul_const ?_ (D ^ (- (Δ : ℝ) / (d + 1)))
  sorry

/--
The derivative f'(t) is non-negative for t ≥ 0, since A ≥ B ≥ C.
Matches the logic on page 10.
-/
lemma weight_difference_nonnegative (p : ℝ) (hp : p ≥ 1) (A B C : ℝ) (hABC : A ≥ B ∧ B ≥ C ∧ C > 0) :
    p * (B - C) * A ^ (p - 1) ≥ B ^ p - C ^ p := by
  /-
  PROOF STRATEGY:
  1. Express the difference B^p - C^p as the integral of p * ζ^(p-1) from C to B.
  2. Since A ≥ B, then for all ζ ∈ [C, B], we have A ≥ ζ.
  3. Because p ≥ 1, the function ζ^(p-1) is non-decreasing, so A^(p-1) ≥ ζ^(p-1).
  4. Therefore, (B - C) * p * A^(p-1) ≥ ∫_C^B p * ζ^(p-1) dζ = B^p - C^p.
  -/
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Icc C B, B^p - C^p = p * c^(p-1) * (B - C) := by
    by_cases hB : B = C;
    · aesop;
    · have := exists_deriv_eq_slope ( f := fun x => x ^ p ) ( show B > C from lt_of_le_of_ne hABC.2.1 ( Ne.symm hB ) );
      exact this ( by exact continuousOn_of_forall_continuousAt fun x hx => by exact ContinuousAt.rpow ( continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( by exact fun x hx => by exact DifferentiableAt.differentiableWithinAt <| by apply_rules [ DifferentiableAt.rpow ] <;> norm_num ; linarith [ hx.1, hx.2 ] ) |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, Set.Ioo_subset_Icc_self hc₁, by rw [ eq_div_iff ( sub_ne_zero_of_ne hB ) ] at hc₂; norm_num [ show c ≠ 0 by linarith [ hc₁.1, hc₁.2 ] ] at hc₂ ⊢; linarith ⟩;
  nlinarith [ show 0 ≤ p * ( B - C ) by exact mul_nonneg ( by positivity ) ( by linarith ), show c ^ ( p - 1 ) ≤ A ^ ( p - 1 ) by exact Real.rpow_le_rpow ( by linarith [ hc.1.1 ] ) ( by linarith [ hc.1.2 ] ) ( by linarith ) ]

/--
Converts the geometric mean B-value K back to the fugacity parameter η.
Based on B_d(η) = dη + 1. Matches page 10 logic.
-/
def K_to_η (d : ℕ) (K : ℝ) : ℝ :=
  (K - 1) / (d : ℝ)

lemma B_d_K_to_η (d : ℕ) (hd : 1 ≤ d) (K : ℝ) :
    B_d d (K_to_η d K) = K := by
  unfold B_d K_to_η
  field_simp
  ring

lemma A_d_K_to_η (d : ℕ) (hd : 1 ≤ d) (K : ℝ) :
    A_d d (K_to_η d K) (K_to_η d K) = ((d - 1) * K ^ 2 + 2 * K - 1) / d := by
  unfold A_d K_to_η
  field_simp
  ring

/--
Lemma 3.3 Reduction: The function f(t) = w₀ - (w₁ + w₂)/Δ is non-decreasing for t ≥ 0.
Matches the derivative analysis on page 10[cite: 203, 652].
-/
lemma weight_diff_monotone (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (K D : ℝ) (hK : K > 0) (hD : D > 0) :
    let p := (Δ : ℝ) / (d : ℝ)
    let f := λ t =>
      let B := K * exp t
      let C := K * exp (-t)
      let A := ((d - 1) * K ^ 2 + B + C - 1) / d
      (A ^ p - (B ^ p + C ^ p) / Δ) * D ^ (-Δ / (d + 1 : ℝ))
    MonotoneOn f (Set.Icc 0 (log K)) := by
  /-
  PROOF STRATEGY:
  1. Calculate the derivative f'(t) as shown in 'deriv_weight_difference'. [cite: 203, 652]
  2. Use the fact that A ≥ B ≥ C for t ≥ 0 to show the derivative is non-negative. [cite: 204, 654]
  3. The core inequality p(B-C)A^{p-1} ≥ B^p - C^p follows from the Mean Value Theorem
     applied to ζ^p on the interval [C, B]. [cite: 204, 654]
  4. Conclude that f(t) ≥ f(0) for all t ≥ 0.
  -/
  sorry

/--
The multivariate weight triple is bounded below by the symmetric case
due to the monotonicity of the dual gap. Matches page 10.
-/
lemma dual_gap_minimized_at_symmetry (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let s := B_d d η * B_d d μ
    let K := sqrt s
    let w₀ := (weight_triple Δ d η μ).1
    let w₁ := (weight_triple Δ d η μ).2.1
    let w₂ := (weight_triple Δ d η μ).2.2
    let w₀_sym := (weight_triple Δ d (K_to_η d K) (K_to_η d K)).1
    let w₁_sym := (weight_triple Δ d (K_to_η d K) (K_to_η d K)).2.1
    w₀ - (w₁ + w₂) / Δ ≥ w₀_sym - (2 * w₁_sym) / Δ := by
  /-
  PROOF STRATEGY:
  1. Let B = B_d(μ) and C = B_d(η). Let K = sqrt(BC) and t = log(sqrt(B/C)). [cite: 199, 648]
  2. Apply 'weight_diff_monotone' to show f(t) ≥ f(0).
  3. f(t) corresponds to the multivariate weights and f(0) to the symmetric weights.
  -/
  sorry

/--
The gap w₀ - Φ_Δ(w₁, w₂) is bounded below by the symmetric gap.
Matches page 10.
-/
lemma multivariate_reduction_to_symmetric (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d)
    (η μ : ℝ) (hη : η ≥ 0) (hμ : μ ≥ 0) :
    let w := weight_triple Δ d η μ
    let K := (B_d d η * B_d d μ).sqrt
    let w_sym := weight_triple Δ d (K_to_η d K) (K_to_η d K)
    w.1 - Φ_Δ Δ w.2.1 w.2.2 ≥ w_sym.1 - Φ_Δ Δ w_sym.2.1 w_sym.2.2 := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. GEOMETRIC MEAN INVARIANT:
     - Let B := B_d d μ and C := B_d d η. Fix the product BC = K²[cite: 198, 647].
     - Note that w.2.1 * w.2.2 depends only on K, so the product of the weights
       is invariant under the transformation Keᵗ and Ke⁻ᵗ.

  2. GAP ANALYSIS VIA DERIVATIVES:
     - Define the gap function f(t) = w₀ - (w₁ + w₂)/Δ as in 'deriv_weight_difference'.
     - Invoke 'weight_diff_monotone' to establish that f(t) is non-decreasing
       for t ≥ 0[cite: 203, 652].
     - Since the multivariate state corresponds to some t ≥ 0 and symmetry to t = 0,
       conclude that the gap is minimized at symmetry: f(t) ≥ f(0)[cite: 205, 655].

  3. BOUNDARY REDUCTION VIA LEMMA 3.5:
     - Use 'Phi_upper_bound' (Lemma 3.5) to bound the dual function Φ_Δ:
       Φ_Δ Δ w.2.1 w.2.2 ≤ Ψ_Δ Δ (w.2.1 * w.2.2) + (w.2.1 + w.2.2) / Δ[cite: 196, 645].
     - This implies the inequality:
       w.1 - Φ_Δ Δ w.2.1 w.2.2 ≥ w.1 - (w.2.1 + w.2.2) / Δ - Ψ_Δ Δ (w.2.1 * w.2.2)[cite: 205, 656].

  4. SYMMETRIC MATCHING:
     - Invoke 'dual_gap_minimized_at_symmetry' to show the RHS is exactly
       minimized when B = C, which is achieved by (K_to_η d K)[cite: 199, 648].
     - Use the 'moreover' equality case of Lemma 3.5 for a₁ = a₂ to show that
       at symmetry, Φ_Δ Δ w_sym.1 w_sym.2 matches the bound exactly[cite: 184, 616].

  5. FINAL COMPARISON:
     - Combine the functional minimum from Step 2 with the boundary equality
       from Step 4 to close the goal[cite: 206, 658].
  -/
  sorry

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
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. BOUNDARY CASE:
     - Check if η = 0 and μ = 0.
     - If so, the triple becomes (1, 1, 1). Prove this is in S_Δ by showing
       (1+x+y)^(Δ+1) ≥ A_{Δ+1}(x,y) for all x,y ≥ 0. [cite: 193, 194]

  2. DEFINE THE INVARIANT PRODUCT:
     - For η, μ > 0, let B := B_d d μ and C := B_d d η.
     - Let K := sqrt (B * C). This K represents the symmetric state where η = μ
       while maintaining the same product of weights (w₁ * w₂). [cite: 198, 206]

  3. INVOKE MULTIVARIATE REDUCTION:
     - Apply 'multivariate_reduction_to_symmetric' to the weight triple w.
     - This uses 'dual_gap_minimized_at_symmetry' and the derivative analysis of f(t)
       to show that the gap w₀ - Φ_Δ(w₁, w₂) is minimized at the symmetric point
       defined by K_to_η d K. [cite: 196, 205]

  4. SYMMETRIC MEMBERSHIP:
     - Let η_sym := K_to_η d K. Apply 'SΔ_membership_symmetric' to prove the
       resulting symmetric weight triple w_sym is in S_Δ. [cite: 207, 1039]
     - This implies the symmetric gap is non-negative: w_sym.0 ≥ Φ_Δ Δ w_sym.1 w_sym.1.

  5. CONCLUSION OF MEMBERSHIP:
     - Combine the reduction result (Step 3) with the symmetric membership (Step 4).
     - Since the multivariate gap dominates the symmetric gap, and the symmetric
       gap is non-negative, conclude that w₀ ≥ Φ_Δ Δ w₁.1 w₁.2. [cite: 207, 1040]
     - This confirms (w₀, w₁, w₂) ∈ S_Δ by the variational definition of the dual set.
  -/
  sorry
