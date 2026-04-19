import MultivarIndepFormalize.Basic
import MultivarIndepFormalize.DualSetMembership

/-!
# Neighborhood reduction helpers

Helper lemmas for the inductive step of the main theorem, including:
- Degree computations in induced subgraphs
- Product splitting over neighbor/non-neighbor partitions
- S_d membership inequalities applied to neighborhood products
- The neighborhood reduction for Δ = 0, 1, and ≥ 2
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

/-! ## Degree in induced subgraphs -/

/-
Degree of a non-neighbor of w in G.induce {x | x ≠ w} equals degree in G
-/
lemma induce_degree_non_adj (w : V) (v : {x : V // x ≠ w}) (hadj : ¬G.Adj w v.val) :
    (G.induce {x | x ≠ w}).degree v = G.degree v.val := by
  refine' Finset.card_bij ( fun x hx => x.val ) _ _ _;
  · aesop;
  · aesop;
  · simp +decide [ SimpleGraph.mem_neighborFinset ];
    exact fun x hx => ⟨ hx, by rintro rfl; exact hadj hx.symm ⟩

/-
Degree of a neighbor of w in G.induce {x | x ≠ w} equals degree in G minus 1
-/
lemma induce_degree_adj (w : V) (v : {x : V // x ≠ w}) (hadj : G.Adj w v.val) :
    (G.induce {x | x ≠ w}).degree v = G.degree v.val - 1 := by
  rw [ SimpleGraph.degree, SimpleGraph.degree ];
  simp +decide [ SimpleGraph.neighborFinset, SimpleGraph.neighborSet, SimpleGraph.adj_comm ];
  rw [ ← Finset.card_erase_of_mem ];
  convert rfl;
  refine' Finset.card_bij ( fun x hx => ⟨ x, _ ⟩ ) _ _ _;
  any_goals exact w;
  all_goals simp_all +decide [ SimpleGraph.adj_comm ]

/-! ## Product splitting -/

/-
A product over {x : V // x ≠ w} can be split into neighbor and non-neighbor parts
-/
lemma prod_subtype_split (w : V) (f : {x : V // x ≠ w} → ℝ) :
    (∏ v : {x : V // x ≠ w}, f v) =
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => G.Adj w v.val),  f v) *
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => ¬G.Adj w v.val), f v) := by
  rw [ Finset.prod_filter_mul_prod_filter_not ]

/-
Relate product over neighbor-subtypes to product over neighborFinset
-/
lemma prod_neighbor_subtype_eq (w : V) (f : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => G.Adj w v.val), f v.val) =
    (∏ v ∈ G.neighborFinset w, f v) := by
  refine' Finset.prod_bij ( fun x hx => x.val ) _ _ _ _ <;> simp +decide;
  exact fun v hv => ⟨ hv, hv.ne.symm ⟩

/-
Relate product over non-neighbor-subtypes to product over complement
-/
lemma prod_non_neighbor_subtype_eq (w : V) (f : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => ¬G.Adj w v.val), f v.val) =
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w), f v) := by
  refine' Finset.prod_bij ( fun v hv => v.val ) _ _ _ _ <;> simp_all +decide [ SimpleGraph.neighborFinset ]

/-! ## Core S_d membership inequality -/

/-
The algebraic core: S_d membership applied to give the key product inequality.
From SΔ_membership, we get (a₀, a₁, a₂) ∈ S_d Δ where the components are
products of ratios. Multiplying the S_d inequality by the common denominator
gives this inequality.
-/
lemma Sd_membership_product_ineq (Δ : ℕ) (hΔ : Δ ≥ 2)
    (d : Fin Δ → ℕ) (hd : ∀ i, 1 ≤ d i ∧ d i ≤ Δ)
    (η μ : Fin Δ → ℝ) (hη : ∀ i, 0 ≤ η i) (hμ : ∀ i, 0 ≤ μ i)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∏ i, (A_d (d i) (η i) (μ i)) ^ (1 / (d i : ℝ))) +
    x * (∏ i, (B_d (d i) (μ i)) ^ (1 / (d i : ℝ))) +
    y * (∏ i, (B_d (d i) (η i)) ^ (1 / (d i : ℝ))) ≥
    (A_d (Δ + 1) x y) ^ (1 / ((Δ : ℝ) + 1)) *
    (∏ i, (A_d (d i + 1) (η i) (μ i)) ^ (1 / ((d i : ℝ) + 1))) := by
  have := SΔ_membership Δ hΔ d hd η μ hη hμ;
  have := this.2.2.2 x y hx hy;
  rw [ Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_div_distrib ] at this;
  rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, ge_iff_le, le_div_iff₀ ] at this <;> first | linarith | simp_all +decide ;
  exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ( A_d_pos _ _ _ ( hη i ) ( hμ i ) ) _

/-
For non-neighbors v of w in the induced subgraph, the product term from h1 matches
the corresponding term in remaining_prod (since degrees are equal).
-/
lemma non_neighbor_prod_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => ¬G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * (η ∘ Subtype.val) v * (μ ∘ Subtype.val) v + (d_v + 1) * ((η ∘ Subtype.val) v + (μ ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) := by
  refine' Finset.prod_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
  · tauto;
  · tauto;
  · intro a ha h; rw [ induce_degree_non_adj ] ;
    exact h

/-
For neighbors v of w in the induced subgraph, when the original η/μ are used,
G'.degree v + 1 = G.degree v, so A_d(G'.degree v + 1, η v, μ v) = A_d(G.degree v, η v, μ v).
-/
lemma neighbor_prod_h1_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * (η ∘ Subtype.val) v * (μ ∘ Subtype.val) v + (d_v + 1) * ((η ∘ Subtype.val) v + (μ ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ G.neighborFinset w,
      (A_d (G.degree v) (η v) (μ v)) ^ (1 / (G.degree v : ℝ))) := by
  refine' Finset.prod_bij ( fun v hv => v.val ) _ _ _ _ <;> simp +contextual [ * ];
  · exact fun v hv => hv.ne.symm;
  · intro a ha h;
    rw [ show ( SimpleGraph.induce { x | ¬x = w } G ).degree ⟨ a, ha ⟩ = G.degree a - 1 from ?_ ];
    · rw [ Nat.cast_sub ] <;> norm_num;
      · unfold A_d; ring;
      · exact Finset.card_pos.mpr ⟨ w, by simpa [ SimpleGraph.adj_comm ] using h ⟩;
    · convert induce_degree_adj G w ⟨ a, ha ⟩ h using 1

/-
For neighbors v of w in the induced subgraph, when η is zeroed on neighbors,
the product gives B_d(G.degree v, μ v) terms.
-/
lemma neighbor_prod_h2_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) v * (μ ∘ Subtype.val) v + (d_v + 1) * (((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) v + (μ ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ G.neighborFinset w,
      (B_d (G.degree v) (μ v)) ^ (1 / (G.degree v : ℝ))) := by
  refine' Finset.prod_bij _ _ _ _ _;
  use fun a ha => a.val;
  · aesop;
  · aesop;
  · aesop;
  · simp +decide [ B_d ];
    intro a ha h; rw [ if_pos h ] ; rw [ induce_degree_adj _ _ _ h ] ; ring_nf
    rw [ Nat.cast_sub ( by linarith [ G.degree_pos_iff_exists_adj a |>.2 ⟨ w, h.symm ⟩ ] ) ] ; ring_nf
    aesop

/-
For neighbors v of w in the induced subgraph, when μ is zeroed on neighbors,
the product gives B_d(G.degree v, η v) terms.
-/
lemma neighbor_prod_h3_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * (η ∘ Subtype.val) v * ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) v + (d_v + 1) * ((η ∘ Subtype.val) v + ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ G.neighborFinset w,
      (B_d (G.degree v) (η v)) ^ (1 / (G.degree v : ℝ))) := by
  refine' Finset.prod_bij ( fun v hv => v ) _ _ _ _ <;> simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
  · exact fun v hv => hv.ne.symm;
  · intro a ha h; rw [ show ( Finset.filter ( fun x : { x : V // x ≠ w } => G.Adj a x ) Finset.univ ).card = Finset.card ( Finset.filter ( fun x : V => G.Adj a x ) Finset.univ ) - 1 from ?_ ] ; simp +decide [ *, B_d ] ;
    · rcases n : Finset.card ( Finset.filter ( fun x => G.Adj a x ) Finset.univ ) with ( _ | _ | n ) <;> simp_all +decide;
      exact False.elim <| n <| h.symm;
    · rw [ ← Finset.card_erase_of_mem ( Finset.mem_filter.mpr ⟨ Finset.mem_univ w, h.symm ⟩ ) ] ; rw [ ← Finset.card_image_of_injective _ Subtype.coe_injective ] ; congr ; ext ; aesop;

/-
For non-neighbors, the product from h2 (with η zeroed on neighbors) equals the
non-neighbor product from h1 (since η is not zeroed on non-neighbors).
-/
lemma non_neighbor_prod_h2_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => ¬G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) v * (μ ∘ Subtype.val) v + (d_v + 1) * (((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) v + (μ ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) := by
  refine' Finset.prod_bij ( fun v hv => v.val ) _ _ _ _ <;> simp +contextual [ * ];
  intro v hv hv'; rw [ induce_degree_non_adj ] ; aesop;

/-
For non-neighbors, the product from h3 (with μ zeroed on neighbors) equals the
non-neighbor product from h1.
-/
lemma non_neighbor_prod_h3_eq (w : V) (η μ : V → ℝ) :
    (∏ v ∈ (Finset.univ : Finset {x : V // x ≠ w}).filter (fun v => ¬G.Adj w v.val),
      let d_v := ((G.induce {x | x ≠ w}).degree v : ℝ)
      ((d_v + 1) * d_v * (η ∘ Subtype.val) v * ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) v + (d_v + 1) * ((η ∘ Subtype.val) v + ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) v) + 1) ^ (1 / (d_v + 1))) =
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) := by
  refine' Finset.prod_bij ( fun v hv => v.val ) _ _ _ _ <;> simp +contextual [ * ];
  intro v hv hv'; rw [ induce_degree_non_adj ] ; aesop;

/-
The S_d membership inequality applied to products over the neighborFinset.
Converts from Finset-indexed products to Fin-indexed products and applies Sd_membership_product_ineq.
-/
omit [Fintype V] [DecidableEq V] in
lemma Sd_membership_finset_ineq (Δ : ℕ) (hΔ : Δ ≥ 2)
    (S : Finset V) (hS : S.card = Δ)
    (d : V → ℕ) (hd : ∀ v ∈ S, 1 ≤ d v ∧ d v ≤ Δ)
    (η μ : V → ℝ) (hη : ∀ v ∈ S, 0 ≤ η v) (hμ : ∀ v ∈ S, 0 ≤ μ v)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∏ v ∈ S, (A_d (d v) (η v) (μ v)) ^ (1 / (d v : ℝ))) +
    x * (∏ v ∈ S, (B_d (d v) (μ v)) ^ (1 / (d v : ℝ))) +
    y * (∏ v ∈ S, (B_d (d v) (η v)) ^ (1 / (d v : ℝ))) ≥
    (A_d (Δ + 1) x y) ^ (1 / ((Δ : ℝ) + 1)) *
    (∏ v ∈ S, (A_d (d v + 1) (η v) (μ v)) ^ (1 / ((d v : ℝ) + 1))) := by
  obtain ⟨e, he⟩ : ∃ e : Fin Δ ≃ S, True := by
    exact ⟨ Fintype.equivOfCardEq ( by aesop ), trivial ⟩;
  convert Sd_membership_product_ineq Δ hΔ ( fun i => d ( e i ) ) ( fun i => hd ( e i ) ( e i |>.2 ) ) ( fun i => η ( e i ) ) ( fun i => μ ( e i ) ) ( fun i => hη ( e i ) ( e i |>.2 ) ) ( fun i => hμ ( e i ) ( e i |>.2 ) ) x y hx hy using 1 <;> norm_num [ Finset.prod_equiv e ];
  · refine' congrArg₂ _ ( congrArg₂ _ _ _ ) _;
    · rw [ ← Finset.prod_coe_sort ];
      conv_lhs => rw [ ← Equiv.prod_comp e ] ;
    · rw [ ← Finset.prod_coe_sort ];
      conv_lhs => rw [ ← Equiv.prod_comp e ] ;
    · rw [ ← Finset.prod_coe_sort ];
      conv_lhs => rw [ ← Equiv.prod_comp e ] ;
  · left;
    conv_lhs => rw [ ← Finset.prod_coe_sort ] ;
    conv_lhs => rw [ ← Equiv.prod_comp e ] ;

/-
Remaining product is nonneg (product of rpow with nonneg base).
-/
lemma remaining_prod_nonneg (w : V) (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) :
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) ≥ 0 := by
  apply Finset.prod_nonneg;
  intro v hv;
  apply_rules [ Real.rpow_nonneg, add_nonneg, mul_nonneg ] <;> norm_num

/-
For Δ = 0, there are no neighbors, so the sum of three products (factored)
equals (1 + η w + μ w) * remaining_prod.
-/
lemma neighborhood_reduction_delta_zero (w : V) (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hΔ : G.degree w = 0)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) (μ ∘ Subtype.val) +
      η w * Z_G_2 (G.induce {x | x ≠ w}) ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) (μ ∘ Subtype.val) +
      μ w * Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) ≥
    remaining_prod * neighborhood_prod * (A_d (G.degree w + 1) (η w) (μ w)) ^ (1 / ((G.degree w : ℝ) + 1)) := by
  rw [ SimpleGraph.degree ] at hΔ ; simp_all +decide [ SimpleGraph.neighborFinset ];
  simp_all +decide [ SimpleGraph.neighborSet ];
  convert mul_le_mul_of_nonneg_right ( h_ih { x : V // x ≠ w } ( G.induce { x | ¬x = w } ) ( η ∘ Subtype.val ) ( μ ∘ Subtype.val ) ?_ ?_ ?_ ) ( show 0 ≤ ( 1 + η w + μ w ) by linarith [ show 0 ≤ η w by exact hη w, show 0 ≤ μ w by exact hμ w ] ) using 1;
  · congr! 1;
    · refine' Finset.prod_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
      intro a ha; rw [ Finset.card_filter, Finset.card_filter ] ;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : { x : V // ¬x = w } => x.val ) Finset.univ ) ) ] <;> simp +decide ;
      · rw [ Finset.card_filter, Finset.card_filter ];
        rw [ Finset.sum_image ] ; aesop;
      · exact fun h => hΔ h.symm;
    · unfold A_d; norm_num [ show G.degree w = 0 from by rw [ SimpleGraph.degree ] ; exact Finset.card_eq_zero.mpr <| by aesop ] ;
      ring;
  · ring!;
  · simp +decide [ Fintype.card_subtype_compl ];
    exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
  · exact fun _ => hη _;
  · exact fun _ => hμ _

/--
Key algebraic inequality for the Δ = 1 case:
(a+b+1+c(b+1)+d(a+1))² ≥ (2cd+2c+2d+1)(2ab+2a+2b+1)
for a,b,c,d ≥ 0.
-/
lemma delta_one_sq_ineq (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a + b + 1 + c * (b + 1) + d * (a + 1))^2 ≥
    (2*c*d + 2*c + 2*d + 1) * (2*a*b + 2*a + 2*b + 1) := by
  set p := a + 1
  set q := b + 1
  set r := c + 1
  set s := d + 1
  have hp : p ≥ 1 := by linarith
  have hq : q ≥ 1 := by linarith
  have h_lhs : a + b + 1 + c * (b + 1) + d * (a + 1) = r * q + s * p - 1 := by ring
  have h_rhs : (2*c*d + 2*c + 2*d + 1) * (2*a*b + 2*a + 2*b + 1) =
    (2*r*s - 1) * (2*p*q - 1) := by ring
  rw [h_lhs, h_rhs]
  suffices h : (r*q + s*p - 1)^2 - (2*r*s - 1) * (2*p*q - 1) ≥ 0 by linarith
  have h_id : (r*q + s*p - 1)^2 - (2*r*s - 1) * (2*p*q - 1) =
    (r*q - s*p)^2 + 2*(p - r)*(q - s) := by ring
  rw [h_id]
  by_cases h1 : (p - r) * (q - s) ≥ 0
  · linarith [sq_nonneg (r*q - s*p)]
  · push_neg at h1
    rcases le_or_gt p r with hpr | hpr
    · have hqs : q > s := by nlinarith
      have h4 : r*q - s*p ≥ (r - p) + (q - s) := by
        nlinarith [show (r - p)*(q - 1) ≥ 0 from mul_nonneg (by linarith) (by linarith),
                   show (q - s)*(p - 1) ≥ 0 from mul_nonneg (by linarith) (by linarith)]
      nlinarith [sq_nonneg ((r - p) - (q - s))]
    · have hqs : q < s := by nlinarith
      have h4 : s*p - r*q ≥ (p - r) + (s - q) := by
        nlinarith [show (p - r)*(q - 1) ≥ 0 from mul_nonneg (by linarith) (by linarith),
                   show (s - q)*(p - 1) ≥ 0 from mul_nonneg (by linarith) (by linarith)]
      nlinarith [sq_nonneg ((p - r) - (s - q))]

lemma neighborhood_reduction_delta_one (w : V) (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hΔ : G.degree w = 1) (hw : G.degree w = G.maxDegree)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) (μ ∘ Subtype.val) +
      η w * Z_G_2 (G.induce {x | x ≠ w}) ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) (μ ∘ Subtype.val) +
      μ w * Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) ≥
    remaining_prod * neighborhood_prod * (A_d (G.degree w + 1) (η w) (μ w)) ^ (1 / ((G.degree w : ℝ) + 1)) := by
  have h_single_neighbor : ∃ v₀, G.neighborFinset w = {v₀} := by
    exact Finset.card_eq_one.mp hΔ;
  obtain ⟨v₀, hv₀⟩ := h_single_neighbor
  have hv₀_deg : G.degree v₀ = 1 := by
    simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
    have := hΔ ▸ G.degree_le_maxDegree v₀; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
    exact le_antisymm this ( Finset.card_pos.mpr ⟨ w, by simpa [ SimpleGraph.adj_comm ] using hv₀.1 ⟩ )
  have hv₀_adj : G.Adj w v₀ := by
    replace hv₀ := Finset.ext_iff.mp hv₀ v₀; aesop;
  have hv₀_not_adj : ∀ u, u ≠ w → u ≠ v₀ → ¬G.Adj w u := by
    intro u hu₁ hu₂ hu₃; replace hv₀ := Finset.ext_iff.mp hv₀ u; simp_all +decide ;
  have hv₀_deg_sub : (G.induce {x | x ≠ w}).degree ⟨v₀, by
    exact fun h => by subst h; exact hv₀_adj.ne rfl;⟩ = 0 := by
    simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] at hv₀_deg ⊢;
    intro a ha h; contrapose! hv₀_deg; simp_all +decide [ Finset.card_eq_one ] ;
    intro x hx; rw [ Finset.eq_singleton_iff_unique_mem ] at hx; simp_all +decide [ SimpleGraph.adj_comm ] ;
  generalize_proofs at *;
  have h_ind : Z_G_2 (induce {x | x ≠ w} G) (η ∘ Subtype.val) (μ ∘ Subtype.val) ≥
    (∏ v ∈ Finset.univ.erase w \ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) * (η v₀ + μ v₀ + 1) := by
        convert h_ih ( { x : V // x ≠ w } ) ( G.induce { x | x ≠ w } ) ( η ∘ Subtype.val ) ( μ ∘ Subtype.val ) _ _ _ using 1;
        · rw [ ← Finset.prod_erase_mul _ _ ( Finset.mem_univ ⟨ v₀, by aesop ⟩ ) ];
          congr! 1;
          · refine' Finset.prod_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ * ];
            · tauto;
            · intro a ha hb; rw [ induce_degree_non_adj ] ; aesop;
          · norm_num [ hv₀_deg_sub ];
        · simp +decide [ Fintype.card_subtype_compl ];
          exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
        · exact fun _ => hη _;
        · exact fun _ => hμ _;
  have h_ind2 : Z_G_2 (induce {x | x ≠ w} G) ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) (μ ∘ Subtype.val) ≥
    (∏ v ∈ Finset.univ.erase w \ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) * (μ v₀ + 1) := by
        convert h_ih ( { x : V // x ≠ w } ) ( G.induce { x | x ≠ w } ) ( ( fun v => if G.Adj w v then 0 else η v ) ∘ Subtype.val ) ( μ ∘ Subtype.val ) _ _ _ using 1;
        · rw [ Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ ⟨ v₀, by tauto ⟩ ];
          congr! 1;
          · refine' Finset.prod_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ * ];
            · tauto;
            · intro a ha hb; simp +decide [ hv₀_not_adj a ha hb ] ;
              rw [ induce_degree_non_adj ] ; aesop;
          · aesop;
        · simp +decide [ Fintype.card_subtype_compl ];
          exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
        · exact fun x => by by_cases hx : G.Adj w x.val; all_goals simp [ hx ]; all_goals exact hη x.val;
        · exact fun _ => hμ _;
  have h_ind3 : Z_G_2 (induce {x | x ≠ w} G) (η ∘ Subtype.val) ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) ≥
    (∏ v ∈ Finset.univ.erase w \ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))) * (η v₀ + 1) := by
        convert h_ih { x : V // x ≠ w } ( induce { x | x ≠ w } G ) ( η ∘ Subtype.val ) ( ( fun v => if G.Adj w v then 0 else μ v ) ∘ Subtype.val ) _ _ _ using 1;
        · rw [ ← non_neighbor_prod_h3_eq ];
          rw [ Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ ⟨ v₀, by tauto ⟩ ] ; norm_num [ hv₀_adj ];
          rw [ show ( Finset.univ \ { ⟨ v₀, by tauto ⟩ } : Finset { x : V // x ≠ w } ) = Finset.filter ( fun x : { x : V // x ≠ w } => ¬G.Adj w x.val ) Finset.univ from ?_ ];
          · norm_num [ hv₀_deg_sub ];
          · grind;
        · simp +decide [ Fintype.card_subtype_compl ];
          exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
        · exact fun _ => hη _;
        · exact fun x => by by_cases hx : G.Adj w x.val; all_goals simp [ hx ]; all_goals exact hμ x.val;
  simp_all +decide [ Finset.prod_singleton, A_d ];
  refine le_trans ?_ ( add_le_add_three h_ind ( mul_le_mul_of_nonneg_left h_ind2 <| hη w ) ( mul_le_mul_of_nonneg_left h_ind3 <| hμ w ) ) ; ring_nf ; norm_num;
  rw [ ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow ];
  have h_sqrt : Real.sqrt (1 + η v₀ * 2 + η v₀ * μ v₀ * 2 + μ v₀ * 2) * Real.sqrt (1 + η w * 2 + η w * μ w * 2 + μ w * 2) ≤ 1 + η v₀ + μ v₀ + η w * (μ v₀ + 1) + μ w * (η v₀ + 1) := by
    rw [ ← Real.sqrt_mul <| by nlinarith only [ show 0 ≤ η v₀ by exact hη v₀, show 0 ≤ μ v₀ by exact hμ v₀ ] ] ; exact Real.sqrt_le_iff.mpr ⟨ by nlinarith only [ show 0 ≤ η v₀ by exact hη v₀, show 0 ≤ μ v₀ by exact hμ v₀, show 0 ≤ η w by exact hη w, show 0 ≤ μ w by exact hμ w ], by nlinarith only [ show 0 ≤ η v₀ by exact hη v₀, show 0 ≤ μ v₀ by exact hμ v₀, show 0 ≤ η w by exact hη w, show 0 ≤ μ w by exact hμ w, delta_one_sq_ineq ( η v₀ ) ( μ v₀ ) ( η w ) ( μ w ) ( hη v₀ ) ( hμ v₀ ) ( hη w ) ( hμ w ) ] ⟩ ;
  convert mul_le_mul_of_nonneg_left h_sqrt ( show 0 ≤ ∏ x ∈ Finset.univ.erase w \ { v₀ }, ( 1 + ( G.degree x : ℝ ) * η x + ( G.degree x : ℝ ) * η x * μ x + ( G.degree x : ℝ ) * μ x + ( G.degree x : ℝ ) ^ 2 * η x * μ x + η x + μ x ) ^ ( 1 + ( G.degree x : ℝ ) ) ⁻¹ from Finset.prod_nonneg fun _ _ => Real.rpow_nonneg ( by nlinarith only [ show 0 ≤ η ‹_› by exact hη _, show 0 ≤ μ ‹_› by exact hμ _, show 0 ≤ ( G.degree ‹_› : ℝ ) * η ‹_› by exact mul_nonneg ( Nat.cast_nonneg _ ) ( hη _ ), show 0 ≤ ( G.degree ‹_› : ℝ ) * μ ‹_› by exact mul_nonneg ( Nat.cast_nonneg _ ) ( hμ _ ) ] ) _ ) using 1 ; ring;
  ring

/-
For Δ ≥ 2, use the full S_d machinery.
-/
lemma neighborhood_reduction_delta_ge_two (w : V) (η μ : V → ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ)
    (hΔ : G.degree w ≥ 2) (hw : G.degree w = G.maxDegree)
    (h_ih : ∀ (V' : Type) [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj] (η' μ' : V' → ℝ),
      Fintype.card V' < Fintype.card V → (0 ≤ η') → (0 ≤ μ') →
      Z_G_2 G' η' μ' ≥ ∏ v : V',
        let d_v := (G'.degree v : ℝ)
        ((d_v + 1) * d_v * η' v * μ' v + (d_v + 1) * (η' v + μ' v) + 1) ^ (1 / (d_v + 1))) :
    let Δ' := G.degree w
    let neighborhood_prod := ∏ v ∈ G.neighborFinset w,
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    let remaining_prod := ∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w),
      let d_v := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
    Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) (μ ∘ Subtype.val) +
      η w * Z_G_2 (G.induce {x | x ≠ w}) ((fun v => if G.Adj w v then 0 else η v) ∘ Subtype.val) (μ ∘ Subtype.val) +
      μ w * Z_G_2 (G.induce {x | x ≠ w}) (η ∘ Subtype.val) ((fun v => if G.Adj w v then 0 else μ v) ∘ Subtype.val) ≥
    remaining_prod * neighborhood_prod * (A_d (Δ' + 1) (η w) (μ w)) ^ (1 / ((Δ' : ℝ) + 1)) := by
  refine' le_trans _ ( add_le_add ( add_le_add ( h_ih _ _ _ _ _ _ _ ) ( mul_le_mul_of_nonneg_left ( h_ih _ _ _ _ _ _ _ ) ( hη _ ) ) ) ( mul_le_mul_of_nonneg_left ( h_ih _ _ _ _ _ _ _ ) ( hμ _ ) ) );
  any_goals intro; simp +decide [ * ];
  any_goals exact hμ _;
  any_goals exact hη _;
  any_goals split_ifs <;> norm_num ; exact hμ _;
  · -- Apply the Sd_membership_finset_ineq lemma with the appropriate parameters.
    have h_apply_ineq : (∏ v ∈ G.neighborFinset w, (A_d (G.degree v) (η v) (μ v)) ^ (1 / (G.degree v : ℝ))) +
                        η w * (∏ v ∈ G.neighborFinset w, (B_d (G.degree v) (μ v)) ^ (1 / (G.degree v : ℝ))) +
                        μ w * (∏ v ∈ G.neighborFinset w, (B_d (G.degree v) (η v)) ^ (1 / (G.degree v : ℝ))) ≥
                        (A_d (G.degree w + 1) (η w) (μ w)) ^ (1 / (G.degree w + 1 : ℝ)) *
                        (∏ v ∈ G.neighborFinset w, (A_d (G.degree v + 1) (η v) (μ v)) ^ (1 / (G.degree v + 1 : ℝ))) := by
                          convert Sd_membership_finset_ineq ( G.degree w ) ( by linarith ) ( G.neighborFinset w ) ( by simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ) ( fun v => G.degree v ) ( fun v hv => ⟨ ?_, ?_ ⟩ ) ( η ) ( μ ) ( fun v hv => ?_ ) ( fun v hv => ?_ ) ( η w ) ( μ w ) ( hη w ) ( hμ w ) using 1;
                          · exact Finset.card_pos.mpr ⟨ w, by simpa [ SimpleGraph.adj_comm ] using hv ⟩;
                          · exact hw.symm ▸ G.degree_le_maxDegree v;
                          · exact hη v;
                          · exact hμ v;
    convert mul_le_mul_of_nonneg_left h_apply_ineq ( show 0 ≤ ∏ v ∈ Finset.univ.erase w \ G.neighborFinset w, ( ( ( G.degree v : ℝ ) + 1 ) * ( G.degree v : ℝ ) * η v * μ v + ( ( G.degree v : ℝ ) + 1 ) * ( η v + μ v ) + 1 ) ^ ( 1 / ( ( G.degree v : ℝ ) + 1 ) ) from ?_ ) using 1;
    · unfold A_d; ring_nf;
      norm_num [ add_assoc, add_left_comm, add_comm ] ; ring_nf;
      ac_rfl;
    · rw [ mul_add, mul_add ];
      congr! 1;
      · rw [ ← mul_add ];
        rw [ mul_add, mul_left_comm ];
        congr! 1;
        · rw [ ← non_neighbor_prod_eq, ← neighbor_prod_h1_eq ];
          rw [ ← Finset.prod_union ];
          · congr! 1;
            grind;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
        · rw [ ← neighbor_prod_h2_eq, ← non_neighbor_prod_h2_eq ];
          rw [ ← Finset.prod_union ];
          · congr! 2;
            grind;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
      · rw [ mul_left_comm, ← neighbor_prod_h3_eq, ← non_neighbor_prod_h3_eq ];
        rw [ ← Finset.prod_union ];
        · congr! 2;
          ext v; by_cases hv : G.Adj w v.val <;> simp +decide [ hv ] ;
        · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by tauto;
    · grind +suggestions;
  · simp +decide;
    exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
  · simp +decide;
    exact Fintype.card_pos_iff.mpr ⟨ w ⟩;
  · split_ifs <;> [ norm_num; exact hη _ ];
  · simp +decide;
    exact Fintype.card_pos_iff.mpr ⟨ w ⟩

end