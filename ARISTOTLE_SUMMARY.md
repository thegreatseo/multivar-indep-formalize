# Summary of changes for run 5718dca3-fc97-4a47-a3c9-232c9e28e071
## Completed: All sorries filled in

The remaining sorry in `neighborhood_reduction` (in `MultivarIndepFormalize/MainTheorem.lean`) has been proved. This was the last sorry in the project.

### What was done

The sorry required proving that the partition function Z_G_2, after applying a recurrence and the induction hypothesis, is bounded below by a product involving the dual set S_d membership inequality. This is the core inductive step for Theorem 1.4.

The proof was decomposed into many helper lemmas in a new file `MultivarIndepFormalize/NeighborhoodHelper.lean`:

**Algebraic identities:**
- `A_d_zero_left/right`: A_d(d, 0, μ) = B_d(d, μ) and similarly for η
- `A_d_pos`, `B_d_pos`: Positivity of A_d and B_d

**Graph theory lemmas (degree in induced subgraphs):**
- `induce_degree_non_adj`: For non-neighbors of w, degree is preserved in G \ {w}
- `induce_degree_adj`: For neighbors of w, degree drops by 1 in G \ {w}

**Product manipulation:**
- `prod_subtype_split`: Split products over {x // x ≠ w} into neighbor/non-neighbor parts
- `prod_neighbor_subtype_eq`, `prod_non_neighbor_subtype_eq`: Relate subtype products to Finset products
- `non_neighbor_prod_eq/h2_eq/h3_eq`: Non-neighbor products equal remaining_prod
- `neighbor_prod_h1/h2/h3_eq`: Neighbor products give A_d and B_d terms

**Core S_d machinery:**
- `Sd_membership_product_ineq`: Extract product inequality from S_d membership (algebraic core)
- `Sd_membership_finset_ineq`: Convert from Fin-indexed to Finset-indexed products

**Case-by-case proofs:**
- `neighborhood_reduction_delta_zero`: Δ = 0 (no neighbors), direct factoring
- `neighborhood_reduction_delta_one`: Δ = 1 (one neighbor), uses a new algebraic inequality (`delta_one_sq_ineq`)
- `neighborhood_reduction_delta_ge_two`: Δ ≥ 2, uses the full S_d membership machinery

The key algebraic inequality for the Δ = 1 case, `delta_one_sq_ineq`, proves that (a+b+1+c(b+1)+d(a+1))² ≥ (2cd+2c+2d+1)(2ab+2a+2b+1) for non-negative reals, using the identity that the difference equals (rq-sp)² + 2(p-r)(q-s) where p=a+1, q=b+1, r=c+1, s=d+1.

### Verification

- The full project builds successfully with `lake build` (no errors, no sorry warnings)
- All theorems use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- No `sorry` appears in any proof in the project (the only occurrence is in a comment)

# Summary of changes for run e190d72a-31fa-4fb2-862f-d11bc78b97e9
## Summary of Changes

### Sorries Resolved (2 out of 3)

**1. `multivariate_reduction_to_symmetric` in `MultivarIndepFormalize/DualSetMembershipSeparately/DualSetMembershipSeparately.lean`** — ✅ PROVED

This lemma shows that the gap `w₀ - Φ_Δ(w₁, w₂)` is minimized at the symmetric point. The proof combines:
- `Phi_upper_bound` (from DualSetBoundary.lean, newly imported)
- `dual_gap_minimized_at_symmetry` (already proven)
- Several new helper lemmas

**New helper lemmas added and proved:**
- `Ad_next_sym_eq`: Shows A_d(d+1) is invariant under K-symmetrization
- `weight_prod_sym_eq`: Weight triple product invariance (w.2.1 * w.2.2 = w_sym.2.1²)
- `weight_triple_pos`: Positivity of weight triple components
- `weight_prod_lt_one`: Weight product < 1 when η + μ > 0
- `K_to_η_zero`: K_to_η gives 0 when η = μ = 0

**2. `neighborhood_reduction` in `MultivarIndepFormalize/MainTheorem.lean`** — ❌ PARTIALLY DONE (1 sorry remains)

This is the inductive step reduction for the main theorem. Significant progress was made:
- Fixed a universe constraint issue by changing `variable {V : Type*}` to `variable {V : Type}` (necessary because `h_ih` expects `V' : Type`)
- Successfully applied the induction hypothesis `h_ih` to all three Z_G_2 terms on the induced subgraph (h1, h2, h3)
- The remaining sorry requires a complex graph-theoretic argument: factoring products over vertices of the induced subgraph into neighbor/non-neighbor parts, relating induced subgraph degrees to original graph degrees, and applying `SΔ_membership` to obtain the S_d bound

### Remaining Sorry

One sorry remains in `MultivarIndepFormalize/MainTheorem.lean` at line 135, inside `neighborhood_reduction`. This sorry requires proving that the sum of product lower bounds (from the induction hypothesis) is ≥ `remaining_prod * neighborhood_prod * A_d(Δ+1, η w, μ w)^{1/(Δ+1)}`. The proof involves:
1. Splitting products over `{x : V // x ≠ w}` into neighbor and non-neighbor parts
2. Showing non-neighbor parts match `remaining_prod` (using degree preservation)
3. For neighbors: relating induced degree to original degree - 1, and using A_d(d,0,μ) = B_d(d,μ)
4. Applying `SΔ_membership` with the Δ neighbors to get the S_d membership bound

### Files Modified
- `MultivarIndepFormalize/DualSetMembershipSeparately/DualSetMembershipSeparately.lean` — Added import, 6 new helper lemmas, proved `multivariate_reduction_to_symmetric`
- `MultivarIndepFormalize/MainTheorem.lean` — Fixed universe constraint, added induction hypothesis applications