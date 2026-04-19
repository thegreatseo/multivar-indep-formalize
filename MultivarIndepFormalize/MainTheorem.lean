import MultivarIndepFormalize.PartitionFunction
import MultivarIndepFormalize.DualSetMembership
import MultivarIndepFormalize.SemiproperPolyRecurrence
import MultivarIndepFormalize.NeighborhoodHelper

/-!
# Main Theorem

**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`

The lower bound for the multiaffine polynomial on semiproper colourings
with two proper colours.

NOTE: In the statements and proofs, replace every λ to η.
-/

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open BigOperators SimpleGraph Real

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-!
## Inductive step
-/

/--
The inductive step reduction for Theorem 1.4.

If the lower bound holds for all graphs with fewer than `|V|` vertices, then the
partition function `Z_G_2` is bounded below by a term involving the dual weight triple.
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
  rw [semiproper_poly_recurrence G η μ w]
  -- Case split on Δ and use helper lemmas
  rcases Nat.lt_or_ge (G.degree w) 1 with hΔ_zero | hΔ_ge1
  · -- Δ = 0 case
    have hΔ : G.degree w = 0 := by omega
    exact neighborhood_reduction_delta_zero G w η μ hη hμ hΔ h_ih
  · rcases Nat.lt_or_ge (G.degree w) 2 with hΔ_one | hΔ_ge2
    · -- Δ = 1 case
      have hΔ : G.degree w = 1 := by omega
      exact neighborhood_reduction_delta_one G w η μ hη hμ hΔ hw h_ih
    · -- Δ ≥ 2 case
      exact neighborhood_reduction_delta_ge_two G w η μ hη hμ hΔ_ge2 hw h_ih

/--
The inductive step: given the induction hypothesis for smaller graphs,
`Z_G_2` satisfies the desired lower bound.
-/
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
          have hw : G.degree w = G.maxDegree :=
            (Classical.choose_spec G.exists_maximal_degree_vertex).symm
          have h_nr := neighborhood_reduction G w hw η μ hη hμ h_ih
          have h_pd : _ = ∏ v : V, _ := product_decomposition G w
            (fun v => ((G.degree v + 1 : ℝ) * G.degree v * η v * μ v + (G.degree v + 1 : ℝ) * (η v + μ v) + 1) ^ (1 / ((G.degree v : ℝ) + 1)))
          simp [A_d] at *;
          grind

/-!
## Main theorem
-/

/--
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`

Let `G` be a graph and let `η_v` and `μ_v`, `v ∈ V(G)`, be nonnegative reals. Then

  `Z_G^{(2)}(η, μ) ≥ ∏_{v ∈ V(G)} ((d_v+1) d_v η_v μ_v + (d_v+1)(η_v + μ_v) + 1)^{1/(d_v+1)}`
-/
theorem semiproper_multiaff_lower_bd (η μ : V → ℝ)
    (h_pos_η : ∀ v, η v ≥ 0)
    (h_pos_μ : ∀ v, μ v ≥ 0) :
    Z_G_2 G η μ ≥ ∏ v : V,
      let d_v : ℝ := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1)) := by
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
          apply inductive_step_bound G' μ' h_card hμ' h_card_nonneg;
          intros V'' _ _ G'' _''' μ'' h_card'' hη'' hμ'';
          intro h_card''_nonneg;
          by_cases hV'' : Nonempty V'';
          · exact ih _ ( by linarith ) _ _ _ _ ( by linarith ) hμ'' hV'' h_card''_nonneg rfl;
          · simp +zetaDelta at *;
            unfold Z_G_2; simp +decide [ Finset.prod_empty ] ;
            simp +decide [ Inhabited.default ];
        · simp +zetaDelta at *;
          rw [ show Z_G_2 G' μ' h_card = 1 by exact Z_G_2_empty G' μ' h_card ] ; norm_num

  exact inductive_step_bound G η μ h_pos_η h_pos_μ h_induction_step;

end

#print axioms semiproper_multiaff_lower_bd
