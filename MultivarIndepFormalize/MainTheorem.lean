/-
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

NOTE: In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembership
import MultivarIndepFormalize.SemiproperPolyRecurrence

set_option linter.style.longLine false

open BigOperators SimpleGraph Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/--
Theorem 1.4 Base Case: The inequality holds as an equality for a single-vertex graph.
Matches page 4.
-/
lemma semiproper_lower_bd_base [Unique V]
    (η μ : V → ℝ) :
    Z_G_2 G η μ = ∏ v : V, (η v + μ v + 1) := by
  /-
  USE THE FOLLOWING PROOF STRATEGY:
  1. For a single vertex w, the only independent set pairs (I, J) are ({w}, ∅), (∅, {w}), and (∅, ∅).
  2. The sum Z_G_2 = η_w + μ_w + 1.
  3. The degree d_w = 0, so the product term simplifies to (0 + (η_w + μ_w) + 1)^(1/1).
  -/
  sorry

/--
The inductive step reduction for Theorem 1.4.
If the lower bound holds for all graphs with fewer than |V| vertices, then the
partition function Z_G_2 is bounded below by a term involving the dual weight triple.
Matches pages 7-8 of the paper.
-/
lemma neighborhood_reduction (w : V)
    (η μ : V → ℝ) (hη : ∀ v, 0 ≤ η v) (hμ : ∀ v, 0 ≤ μ v)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (∀ v, 0 ≤ η' v) → (∀ v, 0 ≤ μ' v) →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    let Δ := G.degree w
    let w_tri := weight_triple Δ Δ (η w) (μ w) -- Note: evaluating at current fugacities
    let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    Z_G_2 G η μ ≥ remaining_prod * neighborhood_prod * (w_tri.1 + w_tri.2.1 * η w + w_tri.2.2 * μ w) :=
  open scoped Classical in
  by
  /-
  USE THE FOLLOWING PROOF STRATEGY:

  1. APPLY RECURRENCE:
     - Use 'semiproper_poly_recurrence' at vertex w to split Z_G_2 into three
       partition functions over G \ {w}. [cite: 115]

  2. APPLY INDUCTION HYPOTHESIS:
     - Apply h_ih to each of the three terms in the recurrence. [cite: 116]
     - Note that for the second and third terms, the fugacities are zeroed out
       on the neighborhood N(w). [cite: 115]

  3. FACTOR COMMON TERMS:
     - Observe that for all vertices v ∉ N(w) ∪ {w}, the degree d_v and fugacities
       η_v, μ_v are identical across all three inductive terms.
     - Factor out 'remaining_prod' (the product over V \ (N(w) ∪ {w})).

  4. LOCAL WEIGHT RECOGNITION:
     - For vertices v ∈ N(w), the degree in G \ {w} is d_v - 1.
     - Recognize that the three sums over the neighborhood terms match the
       components of 'w_triple' (w₀, w₁, w₂). [cite: 124, 125]
     - Specifically, the first inductive term yields w₀ * neighborhood_prod,
       the second yields w₁ * η_w * neighborhood_prod, and the third
       yields w₂ * μ_w * neighborhood_prod. [cite: 126, 128]

  5. ALGEBRAIC REASSEMBLY:
     - Combine the factored terms to reach the final lower bound expression. [cite: 132]
  -/
  sorry

/--
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

**Statement**
Let \(G\) be a graph and let \(\eta_v\) and \(\mu_v\), \(v\in V(G)\), be nonnegative reals. Then
\begin{equation}\label{eq:main2}
  Z_G^{(2)}(\blambda,\bmu) \ge \prod_{v \in V(G)} Z_{K_{d_v+1}}^{(2)}(\eta_v,\mu_v)^{\frac{1}{d_v+1}}
  = \prod_{v \in V(G)} \big( (d_v+1)d_v\eta_v\mu_v + (d_v+1)(\eta_v +\mu_v) + 1 \big)^{\frac{1}{d_v+1}}.
\end{equation}
Here \(\blambda = (\eta_v)_{v\in V(G)}\) and \(\bmu = (\mu_v)_{v\in V(G)}\).
-/
theorem semiproper_multiaff_lower_bd (η μ : V → ℝ)
    (h_pos_η : ∀ v, η v ≥ 0)
    (h_pos_μ : ∀ v, μ v ≥ 0) :
    Z_G_2 G η μ ≥ ∏ v : V,
      let d_v : ℝ := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1)) := by
  /-
  USE THE FOLLOWING PROOF STRATEGY:
  1. Induct on the number of vertices using 'Nat.strong_induction_on'.
  2. Use 'semiproper_lower_bd_base' for the card = 1 case.
  3. For the inductive step, pick w with max degree Δ[cite: 113].
  4. Invoke 'neighborhood_reduction' to reach the local inequality.
  5. Apply 'SΔ_membership_separately' (Lemma 3.3) to confirm that the local weight
     triple satisfies the membership condition for S_d Δ[cite: 138, 139].
  6. By the definition of S_d (the variational inequality), the lower bound follows[cite: 132].
  -/
  sorry
