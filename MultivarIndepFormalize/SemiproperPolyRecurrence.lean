import MultivarIndepFormalize.Definitions

set_option linter.mathlibStandardSet false

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

open BigOperators SimpleGraph Real

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-
An independent set in the induced graph G \ {w} corresponds to an independent set in G that does not contain w.
-/
lemma isIndepSet_image (w : V) (S' : Set {x // x ≠ w}) :
  G.IsIndepSet (S'.image Subtype.val) ↔ (G.induce {x | x ≠ w}).IsIndepSet S' := by
  simp +decide [ Set.Pairwise, SimpleGraph.IsIndepSet ]

/-
The part of the partition function sum where w is in neither I nor J is equal to the partition function of G \ {w}.
-/
open scoped Classical in
lemma Z_G_2_term1 (w : V) (η μ : V → ℝ) :
    let G_minus_v := G.induce {x | x ≠ w}
    let η_rest := η ∘ (↑)
    let μ_rest := μ ∘ (↑)
    (∑ I : Set V, ∑ J : Set V,
      if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J ∧ w ∉ I ∧ w ∉ J then
        (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u)
      else 0) =
    Z_G_2 G_minus_v η_rest μ_rest := by
  convert Set.indicator_apply ?_ ?_ using 1;
  rotate_left;
  exact String.Pos.Raw;
  exact String.Pos.Raw;
  exact Zero.ofOfNat0
  exact Set.univ
  intro a; exact a
  simp +decide [ Set.indicator ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun I : Set { x : V // ¬x = w } => I.image Subtype.val ) Finset.univ ) ) ];
  · rw [ Finset.sum_image ];
    · refine' Finset.sum_congr rfl fun I _ => _;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun J : Set { x : V // ¬x = w } => J.image Subtype.val ) Finset.univ ) ) ];
      · rw [ Finset.sum_image ];
        · simp +decide [ Set.disjoint_left, SimpleGraph.IsIndepSet ];
          simp +decide [ Set.Pairwise, Set.image ];
          grind;
        · intro J hJ K hK hJK; ext x; replace hJK := Set.ext_iff.mp hJK x; aesop;
      · simp +contextual [ Set.disjoint_left ];
        intro x hx₁ hx₂ hx₃ hx₄ hx₅;
        contrapose! hx₁;
        use { y : { x : V // ¬x = w } | y.val ∈ x };
        ext y; aesop;
    · intro I hI J hJ h_eq; ext x; replace h_eq := Set.ext_iff.mp h_eq x; aesop;
  · simp +decide [ Set.ext_iff ];
    intro x hx;
    contrapose! hx;
    use { y : { x : V // ¬x = w } | y.val ∈ x };
    aesop

/-
The part of the partition function sum where w is in I corresponds to the term η_w * Z_{G \ w}(η_sub, μ_rest).
-/
open scoped Classical in
lemma Z_G_2_term2 (w : V) (η μ : V → ℝ) :
    let G_minus_v := G.induce {x | x ≠ w}
    let μ_rest := μ ∘ (↑)
    let η_sub := (fun v => if G.Adj w v then 0 else η v) ∘ (↑)
    (∑ I : Set V, ∑ J : Set V,
      if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J ∧ w ∈ I then
        (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u)
      else 0) =
    η w * Z_G_2 G_minus_v η_sub μ_rest := by
  convert Set.disjoint_image_iff _ using 1;
  rotate_left;
  exact Set V × Set V;
  exact ( Set V × Set V ) × ( Fin 2 );
  exact fun p => ( p, 0 );
  exact Set.univ;
  exact ∅;
  · exact fun p q h => by injection h;
  · simp +decide [ Z_G_2 ];
    -- By definition of $Z_G_2$, we can split the sum into two parts: one where $w \in I$ and one where $w \notin I$.
    have h_split : ∑ I : Set V, ∑ J : Set V, (if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J ∧ w ∈ I then (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u) else 0) =
                   ∑ I : Set V, ∑ J : Set V, (if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J ∧ w ∈ I then η w * (∏ v ∈ (I \ {w}).toFinset, η v) * (∏ u ∈ J.toFinset, μ u) else 0) := by
                     refine' Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => _;
                     split_ifs <;> simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Set.mem_toFinset.mpr ‹_› ) ];
                     exact Or.inl ( by rw [ Finset.prod_eq_mul_prod_diff_singleton ( Set.mem_toFinset.mpr ( by tauto ) ) ] );
    rw [ h_split, Finset.mul_sum _ _ _ ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun I : Set { x : V // ¬x = w } => Insert.insert w ( I.image Subtype.val ) ) Finset.univ ) ) ];
    · rw [ Finset.sum_image ];
      · refine' Finset.sum_congr rfl fun I _ => _;
        rw [ Finset.mul_sum _ _ _ ];
        rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun J : Set { x : V // ¬x = w } => J.image Subtype.val ) Finset.univ ) ) ];
        · rw [ Finset.sum_image ];
          · refine' Finset.sum_congr rfl fun J _ => _;
            simp +decide [ Set.disjoint_left, Set.mem_insert_iff, Set.mem_image, Finset.prod_ite ];
            field_simp;
            split_ifs <;> simp_all +decide [ SimpleGraph.isIndepSet_iff, Finset.prod_filter ];
            · rw [ Finset.card_eq_zero.mpr ] <;> simp +decide [ *, Finset.prod_ite ];
              · rw [ mul_right_comm, Finset.prod_filter ];
                refine' congr rfl ( Finset.prod_congr rfl fun x hx => _ );
                split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
                rename_i h₁ h₂ h₃;
                exact False.elim ( h₁.1 ( Set.mem_insert _ _ ) ( Set.mem_insert_of_mem _ ( Set.mem_image_of_mem _ hx ) ) ( by aesop ) h₃ );
              · intro a ha haI; have := ‹ ( ( Insert.insert w ( Subtype.val '' I ) ).Pairwise fun v w => ¬G.Adj v w ) ∧ ( Subtype.val '' J ).Pairwise fun v w => ¬G.Adj v w ›.1 ( Set.mem_insert _ _ ) ( Set.mem_insert_of_mem _ ( Set.mem_image_of_mem _ haI ) ) ; aesop;
            · rename_i h₁ h₂;
              contrapose! h₂;
              exact ⟨ fun x hx y hy hxy => h₁.1 ( Set.mem_insert_of_mem _ ( Set.mem_image_of_mem _ hx ) ) ( Set.mem_insert_of_mem _ ( Set.mem_image_of_mem _ hy ) ) ( by aesop ), fun x hx y hy hxy => h₁.2.1 ( Set.mem_image_of_mem _ hx ) ( Set.mem_image_of_mem _ hy ) ( by aesop ) ⟩;
            · rename_i h₁ h₂;
              contrapose! h₁;
              simp_all +decide [ Set.Pairwise, Finset.prod_eq_zero_iff ];
              exact fun a ha ha' => by simpa [ SimpleGraph.adj_comm ] using h₁.1.2 a ha ha';
          · intro J hJ J' hJ' h_eq; ext x; replace h_eq := Set.ext_iff.mp h_eq x; aesop;
        · simp +contextual [ Set.disjoint_left ];
          intro x hx₁ hx₂ hx₃ hx₄ hx₅;
          contrapose! hx₁;
          use { y : { x : V // ¬x = w } | y.val ∈ x };
          ext v; simp [Set.mem_image];
          exact fun hv => by rintro rfl; exact hx₄ hv;
      · intro I hI J hJ hij; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
    · simp +contextual [ Finset.mem_image ];
      intro I hI; rw [ Finset.sum_eq_zero ] ; intros J hJ; specialize hI ( { x : { x : V // ¬x = w } | x.val ∈ I \ { w } } ) ; simp_all +decide [ Set.ext_iff ] ;
      grind

/-
The part of the partition function sum where w is in J corresponds to the term μ_w * Z_{G \ w}(η_rest, μ_sub).
-/
open scoped Classical in
lemma Z_G_2_term3 (w : V) (η μ : V → ℝ) :
    let G_minus_v := G.induce {x | x ≠ w}
    let η_rest := η ∘ (↑)
    let μ_sub := (fun v => if G.Adj w v then 0 else μ v) ∘ (↑)
    (∑ I : Set V, ∑ J : Set V,
      if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J ∧ w ∈ J then
        (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u)
      else 0) =
    μ w * Z_G_2 G_minus_v η_rest μ_sub := by
  convert Z_G_2_term2 G w μ η using 1;
  field_simp;
  convert Iff.rfl using 2;
  · rw [ Finset.sum_comm ];
    simp +decide only [disjoint_comm, mul_comm];
    simp +decide only [and_left_comm];
  · unfold Z_G_2; ring;
    rw [ Finset.sum_comm ];
    congr! 3;
    simp +decide only [disjoint_comm, and_comm];
    grind

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
open scoped Classical in
lemma semiproper_poly_recurrence (η μ : V → ℝ) (w : V) :
    let G_minus_v := G.induce {x | x ≠ w}
    let η_rest := η ∘ (↑) -- η restricted to V \ {w}
    let μ_rest := μ ∘ (↑) -- μ restricted to V \ {w}
    let η_sub := (fun v => if G.Adj w v then 0 else η v) ∘ (↑) -- Substitution η_v = 0 for v ∈ N(w)
    let μ_sub := (fun v => if G.Adj w v then 0 else μ v) ∘ (↑) -- Substitution μ_v = 0 for v ∈ N(w)
    Z_G_2 G η μ =
      Z_G_2 G_minus_v η_rest μ_rest +
      η w * Z_G_2 G_minus_v η_sub μ_rest +
      μ w * Z_G_2 G_minus_v η_rest μ_sub := by
  convert congr_arg₂ ( · + · ) ( congr_arg₂ ( · + · ) ( Z_G_2_term1 G w η μ ) ( Z_G_2_term2 G w η μ ) ) ( Z_G_2_term3 G w η μ ) using 1;
  simp +decide only [← Finset.sum_add_distrib];
  refine' Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => _;
  by_cases hI : w ∈ I <;> by_cases hJ : w ∈ J <;> simp +decide [ hI, hJ ];
  exact fun hI' hJ' hIJ => False.elim ( hIJ.le_bot ⟨ hI, hJ ⟩ )
