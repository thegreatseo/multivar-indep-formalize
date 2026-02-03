/-
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/


import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.Analytics
import MultivarIndepFormalize.DualSet
import MultivarIndepFormalize.DualSetMembership

set_option linter.style.longLine false

open BigOperators SimpleGraph Real

noncomputable section

/-
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

**Statement**
Let \(\Delta\ge2\) and \(1\le d_i\le \Delta\), \(1\le i\le \Delta\) be integers. Let \(\lambda_i,\mu_i\ge0\) for \(1\le i\le \Delta\). Then
\[
  \biggl(
  \prod_{i=1}^\Delta \frac{A_{d_i}(\lambda_i,\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\lambda_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}}
  \biggr) \in \calS_\Delta.
\]
-/

/--
**Theorem 1.4** `thm:semiprop-multiaff-lower-bd`
The lower bound for the multiaffine polynomial on semiproper colourings with two proper colours

**Statement**
Let \(G\) be a graph and let \(\lambda_v\) and \(\mu_v\), \(v\in V(G)\), be nonnegative reals. Then
\begin{equation}\label{eq:main2}
  Z_G^{(2)}(\blambda,\bmu) \ge \prod_{v \in V(G)} Z_{K_{d_v+1}}^{(2)}(\lambda_v,\mu_v)^{\frac{1}{d_v+1}}
  = \prod_{v \in V(G)} \big( (d_v+1)d_v\lambda_v\mu_v + (d_v+1)(\lambda_v +\mu_v) + 1 \big)^{\frac{1}{d_v+1}}.
\end{equation}
Here \(\blambda = (\lambda_v)_{v\in V(G)}\) and \(\bmu = (\mu_v)_{v\in V(G)}\).
-/
theorem semiproper_multiaff_lower_bd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (η μ : V → ℝ)
    (h_pos_η : ∀ v, η v ≥ 0)
    (h_pos_μ : ∀ v, μ v ≥ 0) :
    Z_G_2 G η μ ≥ ∏ v : V,
      let d_v : ℝ := (G.degree v : ℝ)
      ((d_v + 1) * d_v * η v * μ v + (d_v + 1) * (η v + μ v) + 1) ^ (1 / (d_v + 1)) := by
  sorry
