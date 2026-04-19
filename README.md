# Multivariate semiproper coloring polynomial

This project formalizes the proof of Theorem 1.4 in the paper [Lower bounds for multivariate independence polynomials and their generalisations](https://arxiv.org/abs/2602.02450) by Joonkyung Lee and Jaehyeon Seo. The theorem is on a lower bound of the multivariate semiproper coloring polynomial (with two proper colors), which is tight in terms of degree sequences.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

## The definition of the multipartite semiproper coloring polynomial

The definition can be found in ...

```lean
def Z_G_2 (η μ : V → ℝ) : ℝ :=
  -- Sum over all pairs of sets I and J
  ∑ I : Set V, ∑ J : Set V,
    -- Constraint: Both must be independent sets and they must be disjoint
    if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J then
      (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u)
    else 0
```

## The formal statement of Theorem 1.4

The statement can be found in ...

```lean
theorem semiproper_multiaff_lower_bd (η μ : V → ℝ)
    (h_pos_η : ∀ v, η v ≥ 0)
    (h_pos_μ : ∀ v, μ v ≥ 0) :
    Z_G_2 G η μ ≥ ∏ v : V,
      let d_v : ℝ := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1))
```
