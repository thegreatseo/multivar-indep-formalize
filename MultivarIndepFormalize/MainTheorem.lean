/-
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

NOTE: In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembership

set_option linter.style.longLine false

open BigOperators SimpleGraph Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-
Recurrence relation for the multivariate semiproper coloring polynomial.
Matches the relation on page 5 of the paper:
Z^{(2)}_G(\blambda,\bmu)
= Z^{(2)}_{G\setminus w}(\blambda',\bmu')
  + \lambda_w Z^{(2)}_{G\setminus w}(\blambda',\bmu')|_{\lambda_v=0,\, v\in N(w)}
  + \mu_w Z^{(2)}_{G\setminus w}(\blambda',\bmu')|_{\mu_v=0,\, v\in N(w)}
Here \blambda and \bmu are functions from V(G) to nonnegative reals.
Also, f(x,y)|_{x=z} means f(z,y), i.e., the value of f(x,y) where x is substituted by z.
-/
lemma semiproper_poly_recurrence (v : V) (η μ : V → ℝ) (w : V) :
    let G_minus_v := G.induce {x | x ≠ v}
    let η_rest := η ∘ (↑) -- η restricted to V \ {w}
    let μ_rest := μ ∘ (↑) -- μ restricted to V \ {w}
    let η_sub := (fun v => if G.Adj w v then 0 else η v) ∘ (↑) -- Substitution η_v = 0 for v ∈ N(w)
    let μ_sub := (fun v => if G.Adj w v then 0 else μ v) ∘ (↑) -- Substitution μ_v = 0 for v ∈ N(w)
    Z_G_2 G η μ =
      Z_G_2 G_minus_v η_rest μ_rest +
      η w * Z_G_2 G_minus_v η_sub μ_rest +
      μ w * Z_G_2 G_minus_v η_rest μ_sub := by
  /-
  PROOF SKETCH:
  1. Expand the definition of Z_G_2 as a sum over pairs of disjoint independent sets (I, J).
  2. Partition the sum into three cases based on the membership of vertex w:
     - Case 1: w ∉ I and w ∉ J. This corresponds to Z_G_2 on G \ {w}.
     - Case 2: w ∈ I (and thus w ∉ J). Since I is an independent set, no neighbor
       v ∈ N(w) can be in I. This is equivalent to setting η_v = 0 for all v ∈ N(w).
     - Case 3: w ∈ J (and thus w ∉ I). Similarly, no neighbor v ∈ N(w) can be in J,
       equivalent to setting μ_v = 0 for all v ∈ N(w).
  3. Factor out η_w and μ_w from the respective sums to match the recurrence terms.
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
  1. INDUCTION SETUP:
     - Proceed by induction on the size of the vertex set |V|[cite: 111, 490].
     - Base Case (|V|=1): The inequality is an equality, as the product has one
       term with d_v=0, matching the definition of Z_K₁^{(2)}[cite: 112, 490].
     - Inductive Step: Assume the bound holds for all graphs with |V|-1 vertices.

  2. VERTEX DELETION:
     - Pick a vertex w with maximum degree Δ = Δ(G).
     - Apply the recurrence relation (semiproper_poly_recurrence)[cite: 115, 494]:
       Z_G2(η, μ) = Z_{G\w}2 + η_w * Z_{G\w}2|_{N(w)=0} + μ_w * Z_{G\w}2|_{μ=0, N(w)=0}.
     - Apply the induction hypothesis to the three partition functions on G \ {w}[cite: 116, 496].

  3. LOCAL REDUCTION:
     - Factor out the common terms for vertices v ∉ {w} ∪ N(w)[cite: 117, 507].
     - Let A_d(η, μ) = Z_{K_d}^{(2)}(η, μ) and B_d(η) = Z_{K_d}^{(1)}(η)[cite: 117, 512, 513].
     - The goal reduces to proving the technical inequality (3.2)[cite: 117, 511]:
       ∏_{v∈N(w)} A_{d_v}(η_v, μ_v)^{1/d_v} + η_w ∏_{v∈N(w)} B_{d_v}(μ_v)^{1/d_v}
       + μ_w ∏_{v∈N(w)} B_{d_v}(η_v)^{1/d_v} ≥ A_{Δ+1}(η_w, μ_w)^{1/(Δ+1)} ∏_{v∈N(w)} A_{d_v+1}(η_v, μ_v)^{1/(d_v+1)}.

  4. DUAL SET MEMBERSHIP:
     - Divide both sides by the RHS product term. The inequality is equivalent to
       showing that a specific weight triple is in the dual set S_Δ[cite: 132, 544].
     - The triple is exactly the one defined in Lemma 3.2 (SΔ_membership)[cite: 134, 546].

  5. CONCLUSION:
     - Invoke Lemma 3.2, which proves this membership by combining Lemma 3.3
       (the separate reduction) and Lemma 3.4 (log-convexity)[cite: 136, 550].
     - This confirms the local inequality holds, completing the inductive step.
  -/
  sorry
