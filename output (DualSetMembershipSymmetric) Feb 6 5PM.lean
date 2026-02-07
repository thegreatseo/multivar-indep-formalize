/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 21c19b43-a1b3-4ae5-b89f-cd8079ca86db

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma deriv_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let x_ext : ℝ → ℝ

- lemma log_Rk_diff (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let log_Rk_ext : ℝ → ℝ

- lemma weight_ratio_relation (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    let x

- lemma degree_d_plane_dominance (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (s : ℝ) (hs : 1 ≤ s) (hks : d = 1 → s < 2) :
    let w₁

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately.Uniquexk
import MultivarIndepFormalize.DualSetMembershipSeparately.xkComparison


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option linter.style.longLine false

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

-- Part A: The technical derivative of the scaling function
/-
The implicit derivative of the zero-finding function x_k(s) for s > 1.
Matches equation (3.14) on page 11.
-/
noncomputable section AristotleLemmas

/-
The derivative of H_k(x) with respect to x.
-/
lemma H_k_deriv (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ≥ 0) :
    HasDerivAt (H_k k) (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2) x := by
      convert HasDerivAt.div ( HasDerivAt.comp x ( show HasDerivAt ( fun x : ℝ => ( k : ℝ ) * ( k - 1 ) * x ^ 2 + 2 * k * x + 1 ) _ _ from HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_pow 2 _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_id _ ) ) ( HasDerivAt.comp x ( show HasDerivAt ( fun x : ℝ => ( k : ℝ ) * x + 1 ) _ _ from HasDerivAt.add ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( hasDerivAt_id _ ) ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_id _ ) ) ?_ using 1 <;> norm_num ; ring;
      · ext x; unfold H_k A_d B_d; ring;
        simpa [ div_eq_mul_inv ] using by ring;
      · ring;
      · positivity

/-
Algebraic identity required for the derivative of x_k(s).
-/
lemma deriv_x_k_algebraic_identity (k : ℕ) (hk : 1 ≤ k) (x s : ℝ) (hx : 0 ≤ x) (hs : 0 < s)
    (h_eq : H_k k x = s ^ k) :
    k * s ^ (k - 1) / (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2) =
    s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k) := by
      unfold H_k B_d at *;
      rw [ div_eq_iff ] at h_eq;
      · rw [ div_div_eq_mul_div, div_eq_div_iff ];
        · unfold A_d at h_eq;
          grind;
        · exact mul_ne_zero ( by positivity ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, sq_nonneg ( ( k : ℝ ) * x + 1 ) ] );
        · unfold A_d at h_eq;
          nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * x ≥ 0 by positivity, show ( k : ℝ ) * x ^ 2 ≥ 0 by positivity, show ( k : ℝ ) ^ 2 * x ≥ 0 by positivity, show ( k : ℝ ) ^ 2 * x ^ 2 ≥ 0 by positivity, pow_pos hs k ];
      · positivity

/-
Extension of x_k to the whole real line (0 outside valid range).
-/
def x_k_ext (k : ℕ) (hk : 1 ≤ k) (t : ℝ) : ℝ :=
  if h : 1 ≤ t ∧ (k = 1 → t < 2) then x_k k hk t h.1 h.2 else 0

/-
x_k_ext is a local right inverse of H_k^(1/k).
-/
lemma x_k_ext_is_inverse (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
  ∀ᶠ t in nhds s, (H_k k (x_k_ext k hk t)) ^ (1 / (k : ℝ)) = t := by
    have h_neighborhood : ∀ᶠ t in nhds s, 1 ≤ t ∧ (k = 1 → t < 2) := by
      by_cases hk1 : k = 1 <;> simp_all +decide [ Filter.eventually_inf_principal ];
      · exact ⟨ Ici_mem_nhds hs, Iio_mem_nhds hks ⟩;
      · exact Ici_mem_nhds hs;
    filter_upwards [ h_neighborhood ] with t ht using by rw [ show x_k_ext k hk t = x_k k hk t ht.1 ht.2 from by unfold x_k_ext; aesop ] ; exact ( x_k_spec k hk t ht.1 ht.2 ) |>.2;

/-
Definition of f_k and its strict monotonicity.
-/
def f_k (k : ℕ) (x : ℝ) : ℝ := (H_k k x) ^ (1 / (k : ℝ))

lemma f_k_strictMonoOn (k : ℕ) (hk : 1 ≤ k) : StrictMonoOn (f_k k) (Set.Ici 0) := by
  intro x hx y hy hxy;
  have h_pos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x < y → H_k k x < H_k k y := by
    exact fun x y hx hy hxy => H_k_strictMonoOn k hk hx hy hxy;
  have h_pos : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x < y → (H_k k x) ^ (1 / (k : ℝ)) < (H_k k y) ^ (1 / (k : ℝ)) := by
    exact fun x y hx hy hxy => Real.rpow_lt_rpow ( show 0 ≤ H_k k x from by rw [ H_k_eq ] ; exact div_nonneg ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * ( k - 1 ) * x ^ 2 ≥ 0 by exact mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( sq_nonneg _ ) ] ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * x ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) hx ] ) ) ( h_pos x y hx hy hxy ) ( by positivity );
  convert h_pos x y hx hy hxy using 1

/-
Continuity of f_k on [0, \infty).
-/
lemma f_k_continuousOn (k : ℕ) (hk : 1 ≤ k) : ContinuousOn (f_k k) (Set.Ici 0) := by
  refine ContinuousOn.rpow ( ContinuousOn.div ?_ ?_ ?_ ) ?_ ?_ <;> norm_num;
  · exact Continuous.continuousOn ( by unfold A_d; continuity );
  · exact Continuous.continuousOn ( by unfold B_d; continuity );
  · exact fun x hx => by unfold B_d; positivity;
  · exact continuousOn_const;
  · exact fun x hx => Or.inr hk

/-
Definitions of DomainK and RangeK.
-/
def DomainK (k : ℕ) : Set ℝ := {s | 1 ≤ s ∧ (k = 1 → s < 2)}
def RangeK : Set ℝ := Set.Ici 0

/-
f_k maps [0, \infty) into DomainK.
-/
lemma f_k_mem_DomainK (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    f_k k x ∈ DomainK k := by
      -- Since $H_k$ is strictly increasing on $[0, \infty)$ and $H_k(0) = 1$, we have $H_k(x) \geq 1$ for all $x \geq 0$.
      have h_Hk_ge_one : ∀ x : ℝ, 0 ≤ x → H_k k x ≥ 1 := by
        intro x hx
        have h_Hk_ge_one : H_k k x ≥ H_k k 0 := by
          exact H_k_strictMonoOn k hk |> fun h => h.le_iff_le ( by norm_num ) ( by assumption ) |>.2 hx;
        exact le_trans ( by norm_num [ H_k_eq ] ) h_Hk_ge_one;
      refine' ⟨ _, _ ⟩;
      · exact Real.one_le_rpow ( h_Hk_ge_one x hx ) ( by positivity );
      · unfold f_k; intro hk'; rcases eq_or_ne k 1 with rfl | hk' <;> simp_all +decide [ H_k ] ;
        unfold A_d B_d; norm_num; rw [ div_lt_iff₀ ] <;> nlinarith;

/-
Order isomorphism between RangeK and DomainK using the strictly monotonic function f_k and its inverse x_k.
-/
noncomputable def g_iso (k : ℕ) (hk : 1 ≤ k) : ↥(RangeK) ≃o ↥(DomainK k) :=
  StrictMono.orderIsoOfRightInverse
    (fun x => ⟨f_k k x, f_k_mem_DomainK k hk x x.2⟩)
    (fun x y h => f_k_strictMonoOn k hk x.2 y.2 h)
    (fun s => ⟨x_k k hk s s.2.1 s.2.2, (x_k_spec k hk s s.2.1 s.2.2).1⟩)
    (fun s => Subtype.ext (x_k_spec k hk s s.2.1 s.2.2).2)

/-
DomainK is a neighborhood of s.
-/
lemma DomainK_mem_nhds (k : ℕ) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
  DomainK k ∈ nhds s := by
    rcases eq_or_ne k 1 <;> simp_all +contextual [ DomainK ];
    · exact Ico_mem_nhds hs hks;
    · exact Filter.mem_of_superset ( Ioi_mem_nhds hs ) fun x hx => hx.out.le

/-
x_k_ext agrees with the inverse of the isomorphism on the domain.
-/
lemma x_k_ext_eq_iso_symm (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : t ∈ DomainK k) :
  x_k_ext k hk t = ((g_iso k hk).symm ⟨t, ht⟩).val := by
    unfold x_k_ext;
    -- By definition of $g_iso$, we know that $g_iso k hk (x_k k hk t ...) = ⟨t, ht⟩$.
    have h_g_iso : g_iso k hk (⟨x_k k hk t ht.1 ht.2, (x_k_spec k hk t ht.1 ht.2).1⟩ : ↥(RangeK)) = ⟨t, ht⟩ := by
      exact Subtype.ext ( x_k_spec k hk t ht.1 ht.2 |>.2 );
    rw [ ← h_g_iso, OrderIso.symm_apply_apply ];
    grind

/-
Continuity of the inverse isomorphism.
-/
lemma g_iso_symm_continuous (k : ℕ) (hk : 1 ≤ k) : Continuous (g_iso k hk).symm := by
  have h_iso_cont : Continuous (g_iso k hk).symm := by
    have h_subspace : OrderTopology (DomainK k) := by
      have h_order_top : OrderTopology (Set.Ici (1 : ℝ)) := by
        infer_instance;
      rcases k with ( _ | _ | k ) <;> norm_num at *;
      · rw [ show DomainK 1 = Set.Ico 1 2 from ?_ ];
        · exact?;
        · ext; simp [DomainK];
      · convert h_order_top using 1;
        · congr with x ; simp +decide [ DomainK ];
        · congr! 1;
          ext; simp [DomainK];
        · congr! 1;
          ext; simp [DomainK]
    have h_subspace_range : OrderTopology (RangeK) := by
      simp [RangeK];
      exact?
    exact?;
  exact h_iso_cont

/-
Continuity of x_k_ext on DomainK.
-/
lemma x_k_ext_continuousOn_DomainK (k : ℕ) (hk : 1 ≤ k) :
  ContinuousOn (x_k_ext k hk) (DomainK k) := by
    -- Rewrite the restriction of `x_k_ext` to `DomainK k` using `x_k_ext_eq_iso_symm`.
    have h_restrict : Set.restrict (DomainK k) (x_k_ext k hk) = (fun t => ((g_iso k hk).symm t).val) ∘ (fun t => ⟨t, t.2⟩ : ↥(DomainK k) → ↥(DomainK k)) := by
      exact funext fun x => x_k_ext_eq_iso_symm k hk x x.2;
    convert h_restrict.symm ▸ Continuous.comp _ _ using 1;
    · exact?;
    · exact Continuous.comp ( continuous_subtype_val ) ( g_iso_symm_continuous k hk );
    · fun_prop (disch := solve_by_elim)

/-
Continuity of x_k_ext at s.
-/
lemma x_k_ext_continuousAt (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
  ContinuousAt (x_k_ext k hk) s := by
    exact ContinuousAt.congr ( x_k_ext_continuousOn_DomainK k hk |> ContinuousOn.continuousAt <| Filter.mem_of_superset ( DomainK_mem_nhds k s hs hks ) <| Set.Subset.refl _ ) <| Filter.eventually_of_mem ( DomainK_mem_nhds k s hs hks ) fun x hx => by aesop;

/-
Derivative of f_k.
-/
lemma f_k_hasDerivAt (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ≥ 0) :
  HasDerivAt (f_k k) ((1 / (k : ℝ)) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2)) x := by
    convert HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ using 1 <;> norm_num;
    · rw [ H_k_deriv k hk x hx |> HasDerivAt.deriv ] ; ring;
    · unfold H_k;
      unfold A_d B_d; norm_num [ mul_comm, hx ];
      exact DifferentiableAt.div ( by norm_num ) ( by norm_num ) ( by positivity );
    · exact Or.inl <| div_ne_zero ( by unfold A_d; exact ne_of_gt <| by cases k <;> norm_num [ A_d ] at * ; positivity ) ( by unfold B_d; exact ne_of_gt <| by cases k <;> norm_num [ B_d ] at * ; positivity )

end AristotleLemmas

lemma deriv_x_k (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let x_ext : ℝ → ℝ := fun t => if ht : (1 ≤ t) ∧ (k = 1 → t < 2) then
        x_k k hk t ht.1 ht.2
      else
        0
    let x := x_ext s
    HasDerivAt x_ext
      (s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)) s := by
  /-
  PROOF STRATEGY:
  1. Use the relation A_k(x) = s^k * B_k(x) from the definition of x_k[cite: 990].
  2. Apply the Implicit Function Theorem or 'HasDerivAt.deriv_comp' to the
     identity H_k(x_k(s)) = s^k[cite: 990].
  3. Differentiate both sides with respect to s:
     H_k'(x) * dx/ds = k * s^(k-1)[cite: 695, 990].
  4. Substitute the expression for H_k' from Equation (3.11) and solve for dx/ds[cite: 680, 990].
  -/
  set x_ext := fun t => if ht : 1 ≤ t ∧ (k = 1 → t < 2) then x_k k hk t ht.1 ht.2 else 0
  set x := x_ext s
  have hx : x ≥ 0 := by
    simp +zetaDelta at *;
    split_ifs <;> [ exact ( x_k_spec k hk s hs.le hks ) |>.1; exact le_rfl ]
  have hx_s : H_k k x = s ^ k := by
    -- By definition of $x_k$, we know that $H_k k x = s^k$.
    have hx_eq : (H_k k x) ^ (1 / (k : ℝ)) = s := by
      convert x_k_spec k hk s hs.le ( by aesop ) |>.2;
      grind;
    rw [ ← hx_eq, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact ( show 0 ≤ H_k k x from by exact ( by rw [ H_k_eq ] ; exact div_nonneg ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) * ( k - 1 ) ≥ 0 by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ] ) ( by nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ) ), one_div_mul_cancel ( by positivity ), Real.rpow_one ]
  have hx_deriv : HasDerivAt (fun t => x_ext t) (s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)) s := by
    have hx_deriv : HasDerivAt (fun t => x_ext t) (1 / ((1 / k) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2))) s := by
      have h_inv_deriv : HasDerivAt (fun t => f_k k t) ((1 / k) * (H_k k x) ^ (1 / (k : ℝ) - 1) * (k * (k * (k - 1) * x ^ 2 + 2 * (k - 1) * x + 1) / (k * x + 1) ^ 2)) x := by
        convert f_k_hasDerivAt k hk x hx using 1;
      have := @HasDerivAt.of_local_left_inverse;
      convert this ( show ContinuousAt x_ext s from ?_ ) h_inv_deriv ?_ ?_ using 1;
      · exact?;
      · convert x_k_ext_continuousAt k hk s hs hks using 1;
      · simp +zetaDelta at *;
        refine' ⟨ ⟨ by linarith, _ ⟩, ⟨ by linarith, _ ⟩, _ ⟩;
        · exact ne_of_gt ( Real.rpow_pos_of_pos ( by rw [ hx_s ] ; positivity ) _ );
        · split_ifs <;> norm_num;
          nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( x_k k hk s ( by linarith ) ( by tauto ) : ℝ ) ≥ 0 by exact ( x_k_spec k hk s ( by linarith ) ( by tauto ) ) |>.1, mul_nonneg ( show ( k : ℝ ) ≥ 0 by positivity ) ( sq_nonneg ( x_k k hk s ( by linarith ) ( by tauto ) : ℝ ) ) ];
        · split_ifs <;> linarith [ show ( k : ℝ ) * x_k k hk s ( by linarith ) ( by aesop ) ≥ 0 by exact mul_nonneg ( Nat.cast_nonneg _ ) ( by exact ( x_k_spec k hk s ( by linarith ) ( by aesop ) ) |>.1 ) ];
      · convert x_k_ext_is_inverse k hk s hs hks using 1;
    convert hx_deriv using 1;
    convert deriv_x_k_algebraic_identity k hk x s hx ( by linarith ) hx_s |> Eq.symm using 1;
    rcases k with ( _ | k ) <;> simp_all +decide [ Nat.succ_div ];
    rw [ ← Real.rpow_natCast _ ( k + 1 ), ← Real.rpow_mul ( by positivity ) ] ; norm_num [ Nat.cast_add_one_ne_zero ] ; ring;
    rw [ show ( -1 - ( k : ℝ ) + ( k : ℝ ) * ( 1 + ( k : ℝ ) ) ⁻¹ + ( 1 + ( k : ℝ ) ) ⁻¹ ) = -k by nlinarith [ mul_inv_cancel₀ ( by linarith : ( 1 + ( k : ℝ ) ) ≠ 0 ) ] ] ; norm_num [ Real.rpow_neg ( by positivity : 0 ≤ s ) ] ; ring;
    -- Combine like terms and simplify the expression.
    field_simp
    ring;
  exact hx_deriv

/-
The derivative of log R_k(s) with respect to s for s > 1.
Matches equation (3.15) on page 11 of the paper:
∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)).
-/
noncomputable section AristotleLemmas

/-
Algebraic expansion of A_d k x x.
-/
lemma helper_A_k_eq (k : ℕ) (x : ℝ) : A_d k x x = k * (k - 1) * x ^ 2 + 2 * k * x + 1 := by
  unfold A_d; ring;

/-
Algebraic expansion of B_d k x.
-/
lemma helper_B_k_eq (k : ℕ) (x : ℝ) : B_d k x = k * x + 1 := by
  rfl

/-
Algebraic identities relating A_{k+1}, A_k, and B_k.
-/
lemma helper_Ak_plus_1_eq_Ak_plus_2xBk (k : ℕ) (x : ℝ) :
    A_d (k + 1) x x = A_d k x x + 2 * x * B_d k x := by
      unfold A_d B_d; ring;
      push_cast; ring;

lemma helper_Ak_plus_1_sub_2Bk_sq (k : ℕ) (x : ℝ) :
    A_d (k + 1) x x - 2 * (B_d k x) ^ 2 = -(A_d k x x - 2 * x) := by
      unfold A_d B_d; ring;
      push_cast; ring

/-
Derivatives of A_{k+1}(x,x) and B_k(x).
-/
lemma helper_A_k_plus_1_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => A_d (k + 1) t t) (2 * (k + 1) * B_d k x) x := by
      convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
      exact fun t => ( k + 1 ) * ( k + 1 - 1 ) * t ^ 2 + ( k + 1 ) * ( t + t ) + 1;
      · convert HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.const_mul _ ( hasDerivAt_pow 2 x ) ) ( HasDerivAt.const_mul _ ( HasDerivAt.add ( hasDerivAt_id x ) ( hasDerivAt_id x ) ) ) ) ( hasDerivAt_const _ _ ) using 1 ; norm_num [ B_d ] ; ring;
      · filter_upwards [ ] with t using by unfold A_d; norm_num ; ring;

lemma helper_B_k_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (fun t => B_d k t) k x := by
      convert HasDerivAt.add ( HasDerivAt.const_mul ( k : ℝ ) ( hasDerivAt_id x ) ) ( hasDerivAt_const _ _ ) using 1 ; norm_num [ B_d ]

/-
Positivity of B_k and A_{k+1} for non-negative x.
-/
lemma helper_B_k_pos (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) : 0 < B_d k x := by
  exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one

lemma helper_A_k_plus_1_pos (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) : 0 < A_d (k + 1) x x := by
  unfold A_d;
  norm_num ; positivity

/-
Derivative of log R_k(x) with respect to x.
-/
lemma helper_deriv_log_Rk_x (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t => Real.log ((B_d k t) ^ (1 / (k : ℝ)) / (A_d (k + 1) t t) ^ (1 / ((k : ℝ) + 1))))
      (-(A_d k x x - 2 * x) / (B_d k x * A_d (k + 1) x x)) x := by
        convert HasDerivAt.log ( HasDerivAt.div ( HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ ) ( HasDerivAt.rpow_const ( hasDerivAt_deriv_iff.mpr _ ) _ ) _ ) _ using 1 <;> norm_num [ B_d, A_d ];
        field_simp;
        any_goals first | positivity | norm_num [ mul_assoc, mul_comm, mul_left_comm ];
        · unfold B_d; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; ring;
          rw [ show ( - ( ( k : ℝ ) * ( 1 + k : ℝ ) ⁻¹ ) ) = ( 1 + k : ℝ ) ⁻¹ - 1 by linarith [ inv_mul_cancel₀ ( by positivity : ( 1 + k : ℝ ) ≠ 0 ) ] ] ; rw [ Real.rpow_sub_one ( by positivity ) ] ; ring;
          field_simp;
          rw [ show ( - ( k : ℝ ) + 1 ) / k = 1 / k - 1 by rw [ div_sub_one ] ; ring ; positivity ] ; rw [ Real.rpow_sub_one ( by positivity ) ] ; ring;
          field_simp
          ring;
        · exact DifferentiableAt.add ( differentiableAt_id.const_mul _ ) ( differentiableAt_const _ );
        · exact Or.inl ( by positivity );
        · exact Or.inl ( by positivity );
        · exact ⟨ by positivity, by positivity ⟩

/-
Algebraic identities for the final simplification of the derivative.
-/
lemma helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk (k : ℕ) (x s : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) (hH : H_k k x = s ^ k) :
    A_d (k + 1) x x = (s ^ k + 2 * x) * B_d k x := by
      -- Substitute hH into the equation to get A_d k x x = s^k * B_d k x.
      have h_sub : A_d k x x = s ^ k * B_d k x := by
        rw [ ← hH, H_k ];
        rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) ) ];
      convert helper_Ak_plus_1_eq_Ak_plus_2xBk k x using 1 ; rw [ h_sub ] ; ring

lemma helper_Ak_minus_x_eq (k : ℕ) (x : ℝ) :
    A_d k x x - x = ((k - 1) * x + 1) * B_d k x := by
      unfold A_d B_d; ring;

lemma helper_identity_for_log_deriv (k : ℕ) (x s : ℝ) (hk : 1 ≤ k) (hx : 0 ≤ x) (hH : H_k k x = s ^ k) :
    (A_d k x x - 2 * x) / B_d k x = 2 * (k - 1) * x + 2 - s ^ k := by
      -- Substitute hH into the expression for A_d k x x.
      have hA : A_d k x x = s^k * B_d k x := by
        rw [ ← hH, H_k ];
        rw [ div_mul_cancel₀ _ ( by exact ne_of_gt ( add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) ) ];
      rw [ div_eq_iff ] <;> cases k <;> norm_num [ B_d, A_d ] at * <;> nlinarith

/-
The denominator term in the derivative of x_k is positive.
-/
lemma helper_denom_pos (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (x : ℝ) (hx : 0 ≤ x)
    (hH : H_k k x = s ^ k) (hks : k = 1 → s < 2) :
    2 * (k - 1) * x + 2 - s ^ k > 0 := by
      rcases k with ( _ | _ | k ) <;> norm_num at *;
      · linarith;
      · unfold H_k at hH;
        rw [ div_eq_iff ] at hH <;> norm_num [ A_d, B_d ] at *;
        · nlinarith [ sq_nonneg ( x - 1 ), mul_nonneg hx ( Nat.cast_nonneg k ) ];
        · positivity

/-
Algebraic simplification of the product of derivatives.
-/
lemma helper_product_derivs (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (x : ℝ) (hx : 0 ≤ x)
    (hH : H_k k x = s ^ k) (hks : k = 1 → s < 2) :
    let D_x := -(A_d k x x - 2 * x) / (B_d k x * A_d (k + 1) x x)
    let D_s := s ^ (k - 1) * B_d k x / (2 * (k - 1) * x + 2 - s ^ k)
    D_x * D_s = -s ^ (k - 1) / (s ^ k + 2 * x) := by
      -- Substitute the expression for $A_{k+1}(x,x)$ from `helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk`.
      have hAkp1 : A_d (k + 1) x x = (s ^ k + 2 * x) * B_d k x := by
        convert helper_Ak_plus_1_eq_sk_plus_2x_mul_Bk k x s hk hx hH using 1;
      -- Substitute the expression for $A_k(x,x) - 2x$ from `helper_identity_for_log_deriv`.
      have hAk_minus_2x : A_d k x x - 2 * x = (2 * (k - 1) * x + 2 - s ^ k) * B_d k x := by
        rw [ ← hH ];
        rw [ show H_k k x = A_d k x x / B_d k x from rfl ];
        rw [ sub_mul, div_mul_cancel₀ ] <;> norm_num [ B_d ];
        · unfold A_d; ring;
        · positivity;
      by_cases h : B_d k x = 0 <;> by_cases h' : 2 * ( ( k : ℝ ) - 1 ) * x + 2 - s ^ k = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      · exact absurd h ( ne_of_gt ( by exact add_pos_of_nonneg_of_pos ( mul_nonneg ( Nat.cast_nonneg _ ) hx ) zero_lt_one ) );
      · exact absurd hAkp1 ( ne_of_gt ( helper_A_k_plus_1_pos k x hk hx ) );
      · exact absurd h' ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show s ^ k > 2 * ( k - 1 ) * x + 2 by exact absurd ( helper_denom_pos k hk s hs x hx hH hks ) ( by linarith ) ] );
      · exact Or.inl ( mul_div_cancel₀ _ h' )

/-
Helper lemma: H_k(x_k(s)) = s^k.
-/
lemma helper_Hk_eq_sk (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    H_k k (x_k k hk s hs hks) = s ^ k := by
      have h_exp : (H_k k (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) = s := by
        exact ( Classical.choose_spec ( exists_unique_x_k k hk s hs hks |> ExistsUnique.exists ) ) |>.2;
      convert congr_arg ( · ^ k ) h_exp using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( show 0 ≤ H_k k ( x_k k hk s hs hks ) from _ ), one_div_mul_cancel ( by positivity ), Real.rpow_one ];
      exact div_nonneg ( by rw [ show A_d k ( x_k k hk s hs hks ) ( x_k k hk s hs hks ) = k * ( k - 1 ) * ( x_k k hk s hs hks ) ^ 2 + 2 * k * ( x_k k hk s hs hks ) + 1 by exact? ] ; exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ) ( sq_nonneg _ ) ) ( mul_nonneg ( mul_nonneg zero_le_two ( Nat.cast_nonneg _ ) ) ( show 0 ≤ x_k k hk s hs hks from by linarith [ x_k_spec k hk s hs ‹_› ] ) ) ) zero_le_one ) ( by rw [ show B_d k ( x_k k hk s hs hks ) = k * ( x_k k hk s hs hks ) + 1 by exact? ] ; exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ x_k k hk s hs hks from by linarith [ x_k_spec k hk s hs ‹_› ] ) ) zero_le_one )

end AristotleLemmas

lemma log_Rk_diff (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 < s) (hks : k = 1 → s < 2) :
    let log_Rk_ext : ℝ → ℝ := fun t => if ht: (1 ≤ t) ∧ (k = 1 → t < 2) then
        Real.log (R_k k hk t ht.1 ht.2)
      else
        0
    let x := x_k k hk s hs.le hks
    HasDerivAt log_Rk_ext
      (-s ^ (k - 1) / (s ^ k + 2 * x)) s := by
  /-
  PROOF STRATEGY:
  1. Expand log R_k(s) = (1/k) * log (B_k(x)) - (1/(k+1)) * log (A_{k+1}(x))
     where x = x_k(s)[cite: 986].
  2. Apply the Chain Rule: d/ds [log R_k(s)] = (d/dx [log R_k(x)] * dx/ds)[cite: 987].
  3. Use 'deriv_x_k' for the dx/ds term.
  4. Use the identity A_{k+1}(x) = (s^k + 2x)B_k(x) to simplify the
     d/dx term to (s^k - 2(k-1)x - 2) / ((s^k + 2x) * B_k(x))[cite: 693, 988].
  5. Multiplying the two terms leads to a cancellation of (2(k-1)x + 2 - s^k),
     leaving the target expression -s^(k-1) / (s^k + 2x)[cite: 991, 992].
  -/
  apply_rules [ HasDerivAt.congr_of_eventuallyEq ];
  convert HasDerivAt.comp s ( helper_deriv_log_Rk_x k hk _ _ ) ( deriv_x_k k hk s hs hks ) using 1;
  any_goals tauto;
  · split_ifs <;> simp_all +decide [ ne_of_gt, le_of_lt ];
    convert Eq.symm ( helper_product_derivs k hk s hs ( x_k k hk s hs.le hks ) ( x_k_spec k hk s hs.le hks |>.1 ) ( helper_Hk_eq_sk k hk s hs.le hks ) hks ) using 1;
    ring;
  · split_ifs <;> [ exact x_k_spec _ _ _ _ _ |>.1; exact le_rfl ];
  · filter_upwards [ lt_mem_nhds hs ] with t ht;
    unfold R_k;
    unfold B_d A_d; aesop;

/--
The relationship between the base weight w₀ and the slope weight w₁
in terms of the invariant ratio s. Matches page 11.
-/
lemma weight_ratio_relation (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 1 ≤ s) (hks : k = 1 → s < 2) :
    let x := x_k k hk s hs hks
    let w₁ := (B_d k x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))
    let w₀ := (A_d k x x) ^ (1 / (k : ℝ)) / (A_d (k + 1) x x) ^ (1 / ((k : ℝ) + 1))
    w₀ = w₁ * s := by
  /-
  PROOF STRATEGY:
  1. Use x_k_spec to get (H_k k x)^(1/k) = s.
  2. Substitute H_k k x = A_d k x x / B_d k x.
  3. Simplify the power (A_d / B_d)^(1/k) = s to A_d^(1/k) = s * B_d^(1/k).
  4. Divide both sides by A_{k+1}^{1/(k+1)} to match the definitions of w₀ and w₁.
  -/
  have h_xk : (A_d k (x_k k hk s hs hks) (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) = s * (B_d k (x_k k hk s hs hks)) ^ (1 / (k : ℝ)) := by
    -- Substitute x_k into H_k and use the definition of H_k to relate A_d and B_d.
    have h_Hk : (A_d k (x_k k hk s hs hks) (x_k k hk s hs hks)) / (B_d k (x_k k hk s hs hks)) = s ^ k := by
      convert congr_arg ( · ^ k ) ( x_k_spec k hk s hs hks |>.2 ) using 1 ; norm_num [ H_k ];
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( div_nonneg ( ?_ ) ( ?_ ) ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one ];
      · unfold A_d;
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show 0 ≤ ( k : ℝ ) * x_k k hk s hs hks by exact mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec k hk s hs hks |>.1 ), show 0 ≤ ( ( k : ℝ ) - 1 ) * x_k k hk s hs hks by exact mul_nonneg ( sub_nonneg.mpr ( Nat.one_le_cast.mpr hk ) ) ( x_k_spec k hk s hs hks |>.1 ) ];
      · exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec k hk s hs hks |>.1 ) ) zero_le_one;
    rw [ div_eq_iff ] at h_Hk;
    · rw [ h_Hk, Real.mul_rpow ( by positivity ) ( by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( show 0 ≤ x_k k hk s hs hks by exact x_k_spec k hk s hs hks |>.1 ) ) zero_le_one ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ];
    · intro h; rw [ h ] at h_Hk; norm_num at h_Hk; linarith [ pow_pos ( zero_lt_one.trans_le hs ) k ] ;
  grind

/- Aristotle failed to find a proof. -/
/--
Monotonicity of R_k(s): R_{d+1}(s) ≤ R_d(s) for Δ ≥ d.
Matches the logic leading to equation (3.15) on page 11.
-/
lemma R_k_monotonicity (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs : 1 ≤ s) (hds : d = 1 → s < 2) :
    R_k (d + 1) (by linarith) s hs (by intro h; linarith) ≤ R_k d hd s hs hds := by
  /-
  PROOF STRATEGY:
  1. Compute R_k(1) = 1 for all k ≥ 1.
  2. Use log_Rk_diff (Part A): ∂_s log R_k(s) = -s^(k-1) / (s^k + 2x_k(s)).
  3. Use x_k_comparison (Part B): x_{d+1}(s) ≤ s * x_d(s).
  4. Combine these to show ∂_s log R_{d+1}(s) ≤ ∂_s log R_d(s).
  5. Since R_{d+1}(1) = R_d(1) = 1 (at x=0), integration/monotonicity
     implies R_{d+1}(s) ≤ R_d(s) for all s ≥ 1.
  -/
  sorry

/--
The degree d plane dominates the tangent plane at α.
Matches page 10.
-/
lemma degree_d_plane_dominance (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (s : ℝ) (hs : 1 ≤ s) (hks : d = 1 → s < 2) :
    let w₁ := (R_k d hd s hs hks) ^ (Δ : ℝ)
    let w₀ := w₁ * s ^ (Δ : ℝ)
    let a₁ := (R_k Δ (by linarith) s hs (by intro h; linarith)) ^ (Δ : ℝ)
    let a₀ := a₁ * s ^ (Δ : ℝ)
    w₀ ≥ a₀ ∧ w₁ ≥ a₁ := by
  /-
  PROOF STRATEGY:
  1. Apply R_k_monotonicity repeatedly to show R_Δ(s) ≤ R_d(s).
  2. Since x^Δ is increasing for x ≥ 0, R_Δ(s)^Δ ≤ R_d(s)^Δ, which gives w₁ ≥ a₁.
  3. Since s ≥ 1, multiplying both sides by s^Δ gives w₁ * s^Δ ≥ a₁ * s^Δ, so w₀ ≥ a₀.
  -/
  have h_Rk_monotonic : R_k d hd s hs hks ≥ R_k Δ (by linarith) s hs (by
  aesop_cat) := by
    all_goals generalize_proofs at *;
    -- By induction on $Δ - d$, we can show that $R_k d hd s hs hks ≥ R_k Δ (by linarith) s hs (by sorry)$.
    induction' hd_le with d hd ih;
    · rfl;
    · rcases d with ( _ | _ | d ) <;> simp_all +decide;
      · interval_cases d ; norm_num at *;
        exact?;
      · exact le_trans ( by simpa using R_k_monotonicity ( d + 2 ) ( by linarith ) s hs ( by aesop ) ) ih
  generalize_proofs at *;
  refine' ⟨ mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ) <| by positivity, Real.rpow_le_rpow _ h_Rk_monotonic <| by positivity ⟩;
  · refine' div_nonneg _ _;
    · exact Real.rpow_nonneg ( by exact add_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith [ x_k_spec Δ ‹_› s hs ‹_› ] ) ) zero_le_one ) _;
    · refine' Real.rpow_nonneg _ _;
      have := x_k_spec Δ ( by linarith ) s hs ( by tauto );
      exact add_nonneg ( add_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr ( Nat.one_le_cast.mpr ( by linarith ) ) ) ) ( by linarith ) ) ( by linarith ) ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( by linarith ) ) ) zero_le_one;
  · refine' div_nonneg _ _ <;> norm_num [ B_d, A_d ];
    · exact Real.rpow_nonneg ( by nlinarith [ show ( Δ : ℝ ) ≥ 2 by norm_cast, show ( x_k Δ ‹_› s hs ‹_› : ℝ ) ≥ 0 by exact ( x_k_spec Δ ‹_› s hs ‹_› ) |>.1 ] ) _;
    · exact Real.rpow_nonneg ( by nlinarith [ show 0 ≤ x_k Δ ‹_› s hs ‹_› by exact ( x_k_spec Δ ‹_› s hs ‹_› ) |>.1, show 0 ≤ ( Δ : ℝ ) * x_k Δ ‹_› s hs ‹_› by exact mul_nonneg ( Nat.cast_nonneg _ ) ( x_k_spec Δ ‹_› s hs ‹_› |>.1 ) ] ) _

/- Aristotle ran out of time. -/
-- Part C: Lemma 3.3 Symmetric Case
/--
Lemma 3.3 in the case where η = μ (symmetric case).
Matches the goal on page 10: (A_d^p / A_{d+1}^q, B_d^p / A_{d+1}^q, B_d^p / A_{d+1}^q) ∈ S_Δ.
-/
lemma SΔ_membership_symmetric (Δ d : ℕ) (hΔ : Δ ≥ 2) (hd : 1 ≤ d) (hd_le : d ≤ Δ)
    (η : ℝ) (hη : η ≥ 0) :
    let p := (Δ : ℝ) / (d : ℝ)
    let q := (Δ : ℝ) / ((d : ℝ) + 1)
    let Ad := A_d d η η
    let Bd := B_d d η
    let Ad_next := A_d (d + 1) η η
    (Ad ^ p / Ad_next ^ q, Bd ^ p / Ad_next ^ q, Bd ^ p / Ad_next ^ q) ∈ S_d Δ := by
  /-
  USE THE FOLLOWING MODULAR PROOF STRATEGY:

  1. RATIO INITIALIZATION:
     - Define s := (H_k d η) ^ (1 / d). Note that s ≥ 1 since H_k(0) = 1 and
       H_k is strictly increasing (H_k_strictMonoOn)[cite: 220, 684].
     - If d = 1, show s < 2 (H_1_tendsto)[cite: 910].

  2. SCALING FUNCTION DEFINITION:
     - Let R_d(s) be as defined in R_k. Observe that the weights in the goal
       satisfy: w₁ = R_d(s)^Δ and w₀ = w₁ * s^Δ[cite: 190, 1012].
     - This uses the identity from 'weight_ratio_relation'[cite: 1012].

  3. MONOTONICITY REDUCTION:
     - Apply 'R_k_monotonicity' repeatedly (or by induction on k) to show
       R_Δ(s) ≤ R_{Δ-1}(s) ≤ ... ≤ R_d(s)[cite: 223, 692].
     - This uses the technical derivative 'log_Rk_diff' and the zero comparison
       'x_k_comparison'[cite: 227, 703].

  4. TANGENT PLANE COMPARISON:
     - Let α := x_k Δ hΔ s hs₀ hs₁. Define a comparison triple (a₀, a₁, a₁) where
       a₁ := R_Δ(s)^Δ and a₀ := a₁ * s^Δ[cite: 216, 670].
     - By 'degree_d_plane_dominance', we have w₁ ≥ a₁ and w₀ ≥ a₀[cite: 1021].

  5. BOUNDARY MEMBERSHIP AND GEOMETRY:
     - The triple (a₀, a₁, a₁) represents the tangent plane of z = A_{Δ+1}^{1/(Δ+1)}
       at the point (α, α)[cite: 140, 557].
     - By Lemma 3.1 (concavity), this tangent plane is in S_Δ[cite: 141, 559].
     - Since S_Δ is an upper set and (w₀, w₁, w₁) ≥ (a₀, a₁, a₁) pointwise,
       the degree d plane must also satisfy the membership condition for S_Δ[cite: 1022, 1023].
  -/
  sorry