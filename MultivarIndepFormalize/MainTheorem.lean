-- Harmonic `generalize_proofs` tactic

/-
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

NOTE: In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembership
import MultivarIndepFormalize.SemiproperPolyRecurrence

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open BigOperators SimpleGraph Real

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-
Theorem 1.4 Base Case: The inequality holds as an equality for a single-vertex graph.
Matches page 4.
-/
noncomputable section AristotleLemmas

/-
For a type V with a unique element, the sum of a function f over all subsets of V is equal to f(∅) + f({default}).
-/
lemma sum_over_subsets_unique {V : Type*} [Fintype V] [Unique V] [DecidableEq V] (f : Set V → ℝ) :
    ∑ I : Set V, f I = f ∅ + f {default} := by
      -- Since $V$ is a unique type, the only subsets are $\emptyset$ and � $\�{default\}$.
      have h_subsets : ∀ (I : Set V), I = ∅ ∨ I = {Inhabited.default} := by
        exact fun I => by rcases I.eq_empty_or_nonempty with h | h <;> [ exact Or.inl h; exact Or.inr ( Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨ h, fun x hx => Subsingleton.elim x _ ⟩ ) ] ;
      convert Finset.sum_pair ?_ using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
      all_goals try simpa using Set.singleton_ne_empty Inhabited.default |> Ne.symm;
      exact fun I _ hI => False.elim <| hI <| by simpa using h_subsets I;
      exact Classical.typeDecidableEq (Set V)

end AristotleLemmas

lemma Z_G_2_empty [IsEmpty V] (η μ : V → ℝ) : Z_G_2 G η μ = 1 := by
  unfold Z_G_2; simp +decide ;
  simp +decide [ Inhabited.default ]

lemma semiproper_lower_bd_base [Unique V]
    (η μ : V → ℝ) :
    Z_G_2 G η μ = ∏ v : V, (η v + μ v + 1) := by
  /-
  USE THE FOLLOWING PROOF STRATEGY:
  1. For a single vertex w, the only independent set pairs (I, J) are ({w}, ∅), (∅, {w}), and (∅, ∅).
  2. The sum Z_G_2 = η_w + μ_w + 1.
  3. The degree d_w = 0, so the product term simplifies to (0 + (η_w + μ_w) + 1)^(1/1).
  -/
  convert sum_over_subsets_unique _ using 1;
  all_goals try infer_instance;
  rw [ sum_over_subsets_unique, sum_over_subsets_unique ] ; simp +decide [ Set.disjoint_singleton_left ] ; ring;

/--
The inductive step reduction for Theorem 1.4.
If the lower bound holds for all graphs with fewer than |V| vertices, then the
partition function Z_G_2 is bounded below by a term involving the dual weight triple.
Matches pages 7-8 of the paper.

PROVIDED SOLUTION
USE THE FOLLOWING PROOF STRATEGY:

  1. APPLY RECURRENCE:
     - Use 'semiproper_poly_recurrence' at vertex w to split Z_G_2 into three
       partition functions over G \ {w}. [cite: 115]
     - This is already done.

  2. APPLY INDUCTION HYPOTHESIS:
     - Apply h_ih to each of the three terms in the recurrence. [cite: 116]
     - Note that for the second and third terms, the fugacities are zeroed out
       on the neighborhood N(w). [cite: 115]

  3. FACTOR COMMON TERMS:
     - Observe that for all vertices v ∉ N(w) ∪ {w}, the degree d_v and fugacities
       η_v, μ_v are identical across all three inductive terms.
     - Factor out 'remaining_prod' (the product over V \ (N(w) ∪ {w})).

  4. LOCAL WEIGHT RECOGNITION:
     - Now we have ∏ v : N(w), ( A_d (deg v) (η v) (μ v) ) ^ (1/(deg v))
        + (η w) ∏ v : N(w) ( B_d (deg v) (μ v) ) ^ (1/(deg v))
        + (μ w) ∏ v : N(w) ( B_d (deg v) (η v) ) ^ (1/(deg v))
       times 'remaining_prod'.
     - Use `SΔ_membership' to show that
        ∏ v : N(w), ( A_d (deg v) (η v) (μ v) ) ^ (1/(deg v))
          + (η w) ∏ v : N(w), ( B_d (deg v) (μ v) ) ^ (1/(deg v))
          + (μ w) ∏ v : N(w), ( B_d (deg v) (η v) ) ^ (1/(deg v))
       is lower-bounded by
        ( A_d (Δ + 1) (η w) (μ w) ) ^ (1 / (deg w + 1)) * ∏ v : N(w), ( A_d (deg v + 1) (η v) (μ v) ) ^ (1 / (deg v + 1)).
      - Note that all the vertices in N(w) has degree ≥ 1.
      - Finally, `neighborhood_prod' = ∏ v : N(w), ( A_d (deg v + 1) (η v) (μ v) ) ^ (1 / (deg v + 1)).
-/
lemma neighborhood_reduction (w : V) (hw : G.degree w = G.maxDegree)
    (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    let Δ := G.degree w
    let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    Z_G_2 G η μ ≥ remaining_prod * neighborhood_prod * (A_d (Δ + 1) (η w) (μ w)) ^ (1 / ((Δ : ℝ) + 1)) :=
  open scoped Classical in
  by
  let Δ := G.degree w
  rw [semiproper_poly_recurrence G η μ w];
  sorry


noncomputable section AristotleLemmas

-- lemma weight_triple_lower_bound (Δ : ℕ) (η μ : ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) :
--     let w_tri := weight_triple Δ Δ η μ
--     w_tri.1 + w_tri.2.1 * η + w_tri.2.2 * μ ≥ (A_d (Δ + 1) η μ) ^ (1 / ((Δ : ℝ) + 1)) := by
--       rcases lt_trichotomy Δ 1 with hΔ | rfl | hΔ <;> norm_num at *;
--       · unfold weight_triple A_d; norm_num [ hΔ ] ; ring_nf; norm_num [ hη, hμ ] ;
--       · unfold weight_triple A_d; norm_num [ ← Real.sqrt_eq_rpow ] ; ring_nf;
--         field_simp;
--         rw [ Real.sq_sqrt ] <;> norm_num [ B_d ] <;> nlinarith [ mul_nonneg hη hμ ];
--       · have := SΔ_membership_separately Δ ( by linarith ) Δ ( by linarith ) ( by linarith ) η μ hη hμ;
--         unfold S_d at this; aesop;

lemma product_decomposition (w : V) (f : V → ℝ) :
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w), f v) *
    (∏ v ∈ G.neighborFinset w, f v) * f w = ∏ v : V, f v := by
      rw [ ← Finset.prod_union, ← Finset.prod_erase_mul _ _ ( Finset.mem_univ w ) ];
      · rcongr x ; aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₁ |>.2 hx₂

lemma inductive_step_bound (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    Z_G_2 G η μ ≥ ∏ v : V,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1)) := by
        rcases isEmpty_or_nonempty V with hV | hV
        · simp [Z_G_2_empty G _ _]
        · let w := Classical.choose G.exists_maximal_degree_vertex
          have hw : G.degree w = G.maxDegree := by
            generalize_proofs at *;
            -- By definition of `maxDegree`, there exists a vertex `w` such that `G.degree w = G.maxDegree`. Use `Classical.choose` to obtain such a vertex and then show that its degree is indeed the maximum.
            have hw_max : G.degree w = G.maxDegree := by
              have := Classical.choose_spec ‹∃ x : V, G.maxDegree = G.degree x›
              exact this.symm;
            -- Apply the hypothesis `hw_max` to conclude the proof.
            exact hw_max
          -- USE neighborhood_reduction with w and hw
          have h_neighborhood_reduction : let Δ := G.degree w;
              let w_tri := weight_triple Δ Δ (η w) (μ w);
              let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
                let d_v := (G.degree v : ℝ)
                ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
              let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
                let d_v := (G.degree v : ℝ)
                ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
              Z_G_2 G η μ ≥ remaining_prod * neighborhood_prod * (A_d (Δ + 1) (η w) (μ w)) ^ (1 / ((Δ : ℝ) + 1)) := by
            exact neighborhood_reduction G w hw η μ hη hμ h_ih
          have h_product_decomposition : let Δ := G.degree w;
              let term_w := ((Δ + 1) * Δ * η w * μ w + (Δ + 1) * (η w + μ w) + 1) ^ (1 / ((Δ : ℝ) + 1))
              let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
                let d_v := (G.degree v : ℝ)
                ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
              let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
                let d_v := (G.degree v : ℝ)
                ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
              remaining_prod * neighborhood_prod * term_w = ∏ v : V,
                let d_v := (G.degree v : ℝ)
                ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1)) := by
            convert product_decomposition G w _ using 1;
          -- rw [h_product_decomposition] at h_neighborhood_reduction
          -- By definition of $A_d$, we know that $A_d (Δ + 1) (η w) (μ w) = term_w$.
          simp [A_d] at *;
          grind

end AristotleLemmas

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
  induction' hVn : Fintype.card V using Nat.strong_induction_on with n ih

  have h_induction_step : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
    Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
    Z_G_2 G' η' μ' ≥ ∏ v : V',
      let d_v := (G'.degree v : ℝ)
      ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1)) := by
        intros V' _ _ G' _' μ' h_card hη' hμ';
        by_cases hV' : Nonempty V';
        · intro h_card_nonneg;
          induction' n : Fintype.card V' using Nat.strong_induction_on with n ih generalizing V' G' μ' h_card;
          -- Apply the induction hypothesis to the graph G' with the given conditions.
          apply inductive_step_bound G' μ' h_card hμ' h_card_nonneg;
          intros V'' _ _ G'' _''' μ'' h_card'' hη'' hμ'';
          intro h_card''_nonneg;
          by_cases hV'' : Nonempty V'';
          · exact ih _ ( by linarith ) _ _ _ _ ( by linarith ) hμ'' hV'' h_card''_nonneg rfl;
          · simp +zetaDelta at *;
            unfold Z_G_2; simp +decide [ Finset.prod_empty ] ;
            simp +decide [ Inhabited.default ];
        · simp +zetaDelta at *;
          rw [ show Z_G_2 G' μ' h_card = 1 by exact? ] ; norm_num

  exact inductive_step_bound G η μ h_pos_η h_pos_μ h_induction_step;
