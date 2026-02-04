/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0934ac25-1ae9-44b1-8ce5-4c88f9f58476

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was negated by Aristotle:

- lemma exists_unique_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    ∃! x : ℝ, x ≥ 0 ∧ (H_k k x) ^ (1 / (k : ℝ)) = s

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
**Lemma 3.3** `lem:Sn-membership-separately`
"Something separated" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/


import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.Analytics
import MultivarIndepFormalize.DualSet


set_option linter.style.longLine false

open Real

noncomputable section

/--
The function H_k(x) = A_k(x) / B_k(x).
Matches definition on page 11[cite: 800].
-/
def H_k (k : ℕ) (x : ℝ) : ℝ :=
  A_d k x x / B_d k x

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
For each s ≥ 1, there is a unique x_k ≥ 0 such that H_k(x_k)^(1/k) = s.
Established by H_k(0) = 1 and strict monotonicity on page 11[cite: 800, 801].
-/
lemma exists_unique_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    ∃! x : ℝ, x ≥ 0 ∧ (H_k k x) ^ (1 / (k : ℝ)) = s := by
  /-
  USE THE FOLLOWING PROOF SKETCH:
  1. Use the derivative calculation from Eq (3.11): H_k'(x) > 0 for x ≥ 0. [cite: 679, 680]
  2. Note H_k(0) = 1, meaning H_k(0)^(1/k) = 1. [cite: 681, 684]
  3. Since H_k(x) → ∞ as x → ∞, the function is a bijection [0,∞) → [1,∞). [cite: 683, 684]
  4. Apply the Intermediate Value Theorem for strictly monotonic functions. [cite: 684]
  -/
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose $k = 1$.
  use 1
  simp [H_k];
  -- Let's choose $s = 2$.
  use 2; norm_num [A_d, B_d] at *; (
  -- Let's simplify the equation $(x + x + 1) / (x + 1) = 2$.
  intro h
  obtain ⟨x, hx⟩ := h
  have h_eq : (x + x + 1) = 2 * (x + 1) := by
    grind
  linarith [hx.left])

-/
/--
For each s ≥ 1, there is a unique x_k ≥ 0 such that H_k(x_k)^(1/k) = s.
Established by H_k(0) = 1 and strict monotonicity on page 11[cite: 800, 801].
-/
lemma exists_unique_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) :
    ∃! x : ℝ, x ≥ 0 ∧ (H_k k x) ^ (1 / (k : ℝ)) = s := by
  /-
  USE THE FOLLOWING PROOF SKETCH:
  1. Use the derivative calculation from Eq (3.11): H_k'(x) > 0 for x ≥ 0. [cite: 679, 680]
  2. Note H_k(0) = 1, meaning H_k(0)^(1/k) = 1. [cite: 681, 684]
  3. Since H_k(x) → ∞ as x → ∞, the function is a bijection [0,∞) → [1,∞). [cite: 683, 684]
  4. Apply the Intermediate Value Theorem for strictly monotonic functions. [cite: 684]
  -/
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `exists_unique_x_k`-/
-- Based on Eq (3.12)

/--
The unique zero x_k(s).
By taking (k ≥ 1) and (s ≥ 1) as arguments, we simplify all future proofs.
-/
def x_k (k : ℕ) (hk : k ≥ 1) (s : ℝ) (hs : s ≥ 1) : ℝ :=
  Classical.choose (exists_unique_x_k k hk s hs).exists

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `x_k`-/
/--
The scaling function R_k(s) = B_k(x_k(s))^{1/k} / A_{k+1}(x_k(s))^{1/(k+1)}.
Defined using the x_k value that satisfies the uniqueness property[cite: 802].
-/
def R_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) : ℝ :=
  let x := x_k k hk s hs
  (B_d k x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  x_k
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (d + 1)
Function expected at
  x_k
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  d-/
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
lemma x_k_comparison (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) :
    let hd1 : 1 ≤ d + 1 := by simp
    (x_k (d + 1) hd1 s hs) ≤ s * (x_k d hd s hs) := by
  /-
  USE THE FOLLOWING PROOF SKETCH:
  1. Let x := x_k d hd s hs. By definition, H_d(x) = s^d[cite: 684, 706, 708].
  2. To prove x_{d+1}(s) ≤ s * x, it is sufficient to show s^(d+1) ≤ H_{d+1}(sx)
     because H_{d+1} is a strictly increasing function[cite: 680, 684, 704, 705].
  3. Expand the difference H_{d+1}(sx) - s^(d+1) using the definitions of A_d and B_d[cite: 707, 708, 711].
  4. Define the quadratic polynomial Q(x) := 2dsx^2 + (2s + d - s^2d - s^2)x - (s - 1).
  5. Show that Q(x) is non-negative for x ≥ s - 1:
     - The leading coefficient 2ds is positive.
     - The value at the boundary Q(s - 1) = (d - 1)(s - 1)^3 is non-negative for d ≥ 1 and s ≥ 1.
  6. Confirm that x_d(s) ≥ s - 1 by using the inequality H_d(x) ≤ 1 + dx[cite: 716].
  7. Since x ≥ s - 1 implies Q(x) ≥ 0, it follows that H_{d+1}(sx) ≥ s^(d+1)[cite: 717].
  -/
  sorry

/- Aristotle failed to find a proof. -/
-- Based on the quadratic polynomial Q(x) analysis on page 12 [cite: 814, 815, 817]

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
     a unique α ≥ 0 such that H_Δ(α)^{1/Δ} = s. [cite: 221]
  3. Define a comparison triple (a₀, a₁, a₁) where a₁ := B_Δ(α)^{1/Δ} / A_{Δ+1}(α)^{1/(Δ+1)}
     and a₀ := A_Δ(α)^{1/Δ} / A_{Δ+1}(α)^{1/(Δ+1)}. [cite: 217]
  4. Note that (a₀, a₁, a₁) is on the boundary of S_Δ because it represents the
     tangent plane to z = A_{Δ+1}(x,y)^{1/(Δ+1)} at (α, α). [cite: 140, 155]
  5. By the concavity of A_{Δ+1}^{1/(Δ+1)}, the tangent plane satisfies
     a₀ + a₁x + a₁y ≥ A_{Δ+1}(x,y)^{1/(Δ+1)}. [cite: 141, 154]
  6. Apply Monotonicity (Item 7 Expansion):
     - From log_Rk_diff and x_k_comparison, we have R_Δ(s) ≤ R_d(s) since Δ ≥ d. [cite: 227, 218]
     - By definition, w₁ = R_d(s)^Δ and a₁ = R_Δ(s)^Δ, so w₁ ≥ a₁. [cite: 190, 217, 223]
     - Since H_d(η)^{1/d} = H_Δ(α)^{1/Δ} = s, the "base" terms satisfy
       w₀ = w₁ * s^Δ and a₀ = a₁ * s^Δ.
     - Because w₁ ≥ a₁ and s ≥ 1, it follows that w₀ ≥ a₀.
  7. Since w₀ ≥ a₀ and w₁ ≥ a₁, the degree d plane (w₀ + w₁x + w₁y) is
     point-wise greater than or equal to the tangent plane (a₀ + a₁x + a₁y). [cite: 214, 215]
  8. Since the tangent plane already bounds the partition function from above,
     the degree d plane also satisfies the membership condition for S_Δ. [cite: 141, 154, 213]
  -/
  sorry

/- Aristotle failed to find a proof. -/
-- Uses monotonicity derived from Part A and Part B [cite: 803, 808, 791]

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