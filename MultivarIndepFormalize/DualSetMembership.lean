/-
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetLogConvex
import MultivarIndepFormalize.DualSetMembershipSeparately

set_option linter.style.longLine false

open Real

noncomputable section

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
  sorry
