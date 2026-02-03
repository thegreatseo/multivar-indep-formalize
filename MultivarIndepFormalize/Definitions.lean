import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The set of all independent sets of a graph G.
-/
open SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SimpleGraph.indepSets : Finset (Finset V) :=
  univ.filter (fun s => G.IsIndepSet s)

/-
The partition function Z_G^{(2)}(λ, μ) defined as the sum over pairs of disjoint independent sets (I, J) of (prod_{v in I} λ_v) * (prod_{u in J} μ_u).
-/
noncomputable def SimpleGraph.ZG2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (lambda : V → ℝ) (mu : V → ℝ) : ℝ :=
  ∑ I ∈ G.indepSets, ∑ J ∈ G.indepSets, if Disjoint I J then (∏ v ∈ I, lambda v) * (∏ u ∈ J, mu u) else 0

/-
The term appearing in the lower bound of Theorem 1.4: (d+1)dλμ + (d+1)(λ+μ) + 1.
-/
noncomputable def SimpleGraph.ZG2_lower_bound_term (d : ℕ) (lambda mu : ℝ) : ℝ :=
  (d + 1) * d * lambda * mu + (d + 1) * (lambda + mu) + 1

/-
Definitions of A_d(λ, μ) and B_d(λ) as used in Equation 553 and 556.
-/
noncomputable def A_d (d : ℕ) (lambda mu : ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) - 1) * lambda * mu + (d : ℝ) * (lambda + mu) + 1

noncomputable def B_d (d : ℕ) (lambda : ℝ) : ℝ :=
  (d : ℝ) * lambda + 1

/-
Definition of the dual set S_d.
-/
def S_d (d : ℕ) : Set (ℝ × ℝ × ℝ) :=
  { v | match v with
    | (a₀, a₁, a₂) => a₀ > 0 ∧ a₁ > 0 ∧ a₂ > 0 ∧
    ∀ x y, x ≥ 0 → y ≥ 0
      → a₀ + a₁ * x + a₂ * y ≥ (A_d (d + 1) x y) ^ (1 / ((d : ℝ) + 1)) }

/-
Definition of Φ_Δ(a₁, a₂) as the supremum of (A_{Δ+1}(x,y)^{1/(Δ+1)} - a₁x - a₂y)
over x, y ≥ 0.
-/
noncomputable def Φ_Δ (Δ : ℕ) (a₁ a₂ : ℝ) : ℝ :=
  iSup (λ x => iSup (λ (_ : x ≥ 0) =>
    iSup (λ y => iSup (λ (_ : y ≥ 0) =>
      (A_d (Δ + 1) x y) ^ (1 / ((Δ : ℝ) + 1)) - a₁ * x - a₂ * y
    ))
  ))

/--
The multivariate partition function for semiproper colorings.
Matches the definition: Σ_{I, J ∈ ℐ(G), I ∩ J = ∅} (Π_{v ∈ I} λ_v) (Π_{u ∈ J} μ_u)
-/
def Z_G_2 (η μ : V → ℝ) : ℝ :=
  -- Sum over all pairs of sets I and J
  ∑ I : Set V, ∑ J : Set V,
    -- Constraint: Both must be independent sets and they must be disjoint
    if G.IsIndepSet I ∧ G.IsIndepSet J ∧ Disjoint I J then
      (∏ v ∈ I.toFinset, η v) * (∏ u ∈ J.toFinset, μ u)
    else 0


