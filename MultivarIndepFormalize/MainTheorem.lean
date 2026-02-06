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
  1. INDUCTION SETUP:
     - Proceed by induction on the vertex set size |V|[cite: 112, 490].
     - Base Case (|V|=1): The inequality holds as an equality since the
       product contains one term with d_v = 0, matching Z_K₁^{(2)}[cite: 112, 490].
     - Inductive Step: Assume the lower bound holds for all graphs
       with |V|-1 vertices[cite: 112, 490].
  2. VERTEX DELETION:
     - Select a vertex w with maximum degree Δ = Δ(G)[cite: 113, 491].
     - Apply semiproper_poly_recurrence to decompose Z_G_2(η, μ)[cite: 115, 494].
     - Apply the induction hypothesis to the three partition functions
       on the subgraph G \ {w}[cite: 116, 496].
  3. LOCAL REDUCTION:
     - Cancel out shared product factors for all vertices v ∉ {w} ∪ N(w)[cite: 117, 507].
     - Use definitions A_d(η, μ) = Z_{K_d}^{(2)}(η, μ) and B_d(η) = Z_{K_d}^{(1)}(η)[cite: 117, 512, 513].
     - Reduce the problem to verifying the neighborhood inequality (3.2)[cite: 117, 511].
  4. DUAL SET MEMBERSHIP:
     - Divide the inequality by the RHS product to show that the
       resulting weight triple is in the dual set S_Δ[cite: 132, 544].
     - Identify this triple as the one defined in Lemma 3.2 (lem_Sn_membership)[cite: 134, 546].
  5. CONCLUSION:
     - Complete the inductive step by invoking Lemma 3.2, which proves
       membership via separate reduction (Lemma 3.3) and log-convexity
       of the dual set (Lemma 3.4)[cite: 136, 550].
  -/
  sorry
