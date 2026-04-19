import MultivarIndepFormalize.Definitions

/-!
# Partition function base cases

Base-case evaluations of `Z_G_2` for empty and single-vertex graphs,
along with the product decomposition identity used in the inductive step.
-/

set_option linter.style.longLine false
set_option linter.mathlibStandardSet false

open BigOperators SimpleGraph Real

noncomputable section

/-!
## Subset enumeration helpers
-/

/--
For a type `V` with a unique element, the sum of a function `f` over all subsets of `V`
is equal to `f(∅) + f({default})`.
-/
lemma sum_over_subsets_unique {V : Type*} [Fintype V] [Unique V] [DecidableEq V] (f : Set V → ℝ) :
    ∑ I : Set V, f I = f ∅ + f {default} := by
      have h_subsets : ∀ (I : Set V), I = ∅ ∨ I = {Inhabited.default} := by
        exact fun I => by rcases I.eq_empty_or_nonempty with h | h <;> [ exact Or.inl h; exact Or.inr ( Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨ h, fun x hx => Subsingleton.elim x _ ⟩ ) ] ;
      convert Finset.sum_pair ?_ using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
      all_goals try exact (Set.singleton_ne_empty Inhabited.default).symm;
      exact fun I _ hI => False.elim <| hI <| by simpa using h_subsets I;
      exact Classical.typeDecidableEq (Set V)

/-!
## Base cases
-/

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/--
For an empty graph, `Z_G_2 = 1`.
-/
lemma Z_G_2_empty [IsEmpty V] (η μ : V → ℝ) : Z_G_2 G η μ = 1 := by
  unfold Z_G_2; simp +decide ;
  simp +decide [ Inhabited.default ]

omit [DecidableRel G.Adj] in
/--
For a single-vertex graph, `Z_G_2 = η w + μ w + 1`.
-/
lemma semiproper_lower_bd_base [Unique V]
    (η μ : V → ℝ) :
    Z_G_2 G η μ = ∏ v : V, (η v + μ v + 1) := by
  convert sum_over_subsets_unique _ using 1;
  all_goals try infer_instance;
  rw [ sum_over_subsets_unique, sum_over_subsets_unique ] ; simp +decide [ Set.disjoint_singleton_left ] ; ring;

/-!
## Product decomposition
-/

/--
The product `∏ v : V, f v` decomposes into products over non-neighbors, neighbors, and `w`.
-/
lemma product_decomposition (w : V) (f : V → ℝ) :
    (∏ v ∈ (Finset.univ.erase w) \ (G.neighborFinset w), f v) *
    (∏ v ∈ G.neighborFinset w, f v) * f w = ∏ v : V, f v := by
      rw [ ← Finset.prod_union, ← Finset.prod_erase_mul _ _ ( Finset.mem_univ w ) ];
      · rcongr x ; aesop;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₁ |>.2 hx₂

end
