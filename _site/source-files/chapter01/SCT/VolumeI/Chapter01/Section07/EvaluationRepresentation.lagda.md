# The family square of represented evaluation

The specialization comparison of Evaluation is natural for the actual
evaluation action. We prove its full square by pasting the product,
reassociation, mapping-currying and terminal-decoding squares. This is the
boundary needed to recover families from evaluation; objectwise beta alone
does not supply it.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; preWhisker-id₌; postWhisker-id₌; comp-unitˡ; comp-unitʳ; comp-assoc;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence
open import SCT.VolumeI.Chapter01.Section03.Equivalences
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as Reassociation
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Mapping
open import SCT.VolumeI.Chapter01.Section04.Points
open import SCT.VolumeI.Chapter01.Section04.MappingSpecialization
open import SCT.VolumeI.Chapter01.Section07.Evaluation

private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {u : x″ ＝ y″}
      {l : x =₁ x′} {r : y =₁ y′} {l′ : x′ =₁ x″} {r′ : y′ =₁ y″}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b u (const l′) (const r′)
      → SquareCell₌ t u (const (l′ ∙ l)) (const (r′ ∙ r))
    paste-fixed {l = l} {r} {l′} {r′} p q =
      replace-sides₌ (const-comp l′ l) (const-comp r′ r) (paste-square₌ p q)

    inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
    inverse-fixed {l = l} {r} p =
      replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ p)

    post-fixed : {A B Z : CAT Γ} (H : MAP B Z) {f g f′ g′ : MAP A B}
      {t : f ＝ g} {b : f′ ＝ g′} {l : f =₁ f′} {r : g =₁ g′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ (H ◁ t) (H ◁ b) (const (H ◁ l)) (const (H ◁ r))
    post-fixed H {l = l} {r} p =
      replace-sides₌ (post-constant H l) (post-constant H r) (post-square₌ H p)

    pre-fixed : {A B Z : CAT Γ} (k : MAP A B) {f g f′ g′ : MAP B Z}
      {t : f ＝ g} {b : f′ ＝ g′} {l : f =₁ f′} {r : g =₁ g′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ (t ▷ k) (b ▷ k) (const (l ▷ k)) (const (r ▷ k))
    pre-fixed k {l = l} {r} p =
      replace-sides₌ (pre-constant l k) (pre-constant r k) (pre-square₌ k p)

    pair-fixed : {A B Z : CAT Γ} {f g f′ g′ : MAP A B} {h k h′ k′ : MAP A Z}
      {t : f ＝ g} {b : f′ ＝ g′} {u : h ＝ k} {v : h′ ＝ k′}
      {l : f =₁ f′} {r : g =₁ g′} {l′ : h =₁ h′} {r′ : k =₁ k′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ u v (const l′) (const r′)
      → SquareCell₌ (pair⁼ t u) (pair⁼ b v)
          (const (pair⁼ l l′)) (const (pair⁼ r r′))
    pair-fixed {l = l} {r} {l′} {r′} p q =
      replace-sides₌ (pair⁼-constant l l′) (pair⁼-constant r r′) (pair⁼-square p q)

    constant-identity-square : {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g)
      → SquareCell₌ (const {P = X} (id₌ f)) (const (id₌ g)) (const α) (const α)
    constant-identity-square α = (comp₌-unitˡ (const α)) ⁻¹ ∙ comp₌-unitʳ (const α)

    pre-identity : {A B Z : CAT Γ} (f : MAP B Z) (r : MAP A B)
      → (const {P = X} (id₌ f) ▷ r) =₁ const (id₌ (f ∘ r))
    pre-identity f r = const-cong (preWhisker-id₌ f r) ∙ pre-constant (id₌ f) r

    post-identity : {A B Z : CAT Γ} (f : MAP B Z) (r : MAP A B)
      → (f ◁ const {P = X} (id₌ r)) =₁ const (id₌ (f ∘ r))
    post-identity f r = const-cong (postWhisker-id₌ f r) ∙ post-constant f (id₌ r)

    pair-evaluation-fixed : {A K B Z : CAT Γ} (f : MAP K B) (g : MAP K Z)
      {r s : MAP A K} (δ : r ＝ s) {x x′ : MAP A B} {y y′ : MAP A Z}
      (l : (f ∘ r) =₁ x) (l′ : (f ∘ s) =₁ x′)
      (q : (g ∘ r) =₁ y) (q′ : (g ∘ s) =₁ y′)
      (α : x ＝ x′) (β : y ＝ y′)
      → SquareCell₌ (f ◁ δ) α (const l) (const l′)
      → SquareCell₌ (g ◁ δ) β (const q) (const q′)
      → SquareCell₌ (pair f g ◁ δ) (pair⁼ α β)
          (const (pair⁼ l q ∙ pair-pre f g r)) (const (pair⁼ l′ q′ ∙ pair-pre f g s))
    pair-evaluation-fixed f g {r} {s} δ l l′ q q′ α β p w =
      replace-sides₌ (pair-evaluation-const r l q) (pair-evaluation-const s l′ q′)
        (pair-evaluation-natural f g δ (const l) (const l′) (const q) (const q′) α β p w)
```

## Native restriction squares

These are the product-with-identity restriction squares, postcomposed by
the supplied evaluation. Their sides are precisely `evaluate-restrict`.

```agda
module _ {Γ : Context} {F C D : CAT Γ} (e : MAP (F × C) D) {X : CAT Γ} where
  open Terms.Equalities X using (_＝_)

  evaluate-restrict-inputs : {S T : CAT Γ} {f g : MAP T F}
    (α : f ＝ g) (r : MAP S T)
    → SquareCell₌ (evaluate⁼ e (α ▷ r)) (evaluate⁼ e α ▷ productMap r (id C))
        (const (evaluate-restrict e f r)) (const (evaluate-restrict e g r))
  evaluate-restrict-inputs {f = f} {g} α r =
    paste-fixed
      (post-fixed e (inverse-fixed (productMap-first-comp-inputs α r)))
      (inverse-fixed (whisker-mixed (productMap-cong α (const (id₌ (id C)))) (productMap r (id C)) e))

  evaluate-restrict-substitution : {S T : CAT Γ} (f : MAP T F)
    {r s : MAP S T} (γ : r ＝ s)
    → SquareCell₌ (evaluate⁼ e (f ◁ γ))
        (evaluate e f ◁ productMap-cong γ (const (id₌ (id C))))
        (const (evaluate-restrict e f r)) (const (evaluate-restrict e f s))
  evaluate-restrict-substitution f γ =
    paste-fixed
      (post-fixed e (inverse-fixed (productMap-first-comp-substitution f γ)))
      (inverse-fixed (postWhisker-comp (productMap-cong γ (const (id₌ (id C)))) (productMap f (id C)) e))
```

## Reassociation of the parameter

The two regrouping routes are paired from their three coordinates. The
projection squares and the product-at-pair squares compare them with one
common normal form. All helpers in this coordinate calculation are private.

```agda
private
  module _ {Γ : Context} {A R Y T C : CAT Γ} {σ τ : MAP R Y}
    (γ : MAP A (Equal σ τ)) where
    open Terms.Equalities A using (_＝_)

    rR : MAP (R × (T × C)) ((R × T) × C)
    rR = Associativity.backward R T C
    rY : MAP (Y × (T × C)) ((Y × T) × C)
    rY = Associativity.backward Y T C
    rightChange : MAP R Y → MAP (R × (T × C)) (Y × (T × C))
    rightChange s = productMap s (id (T × C))
    leftChange : MAP R Y → MAP ((R × T) × C) ((Y × T) × C)
    leftChange s = productMap (productMap s (id T)) (id C)
    δ : rightChange σ ＝ rightChange τ
    δ = productMap-cong γ (const (id₌ (id (T × C))))

    first : (s : MAP R Y) → (pr₁ ∘ rightChange s) =₁ (s ∘ pr₁)
    first s = pair-β₁ (s ∘ pr₁) (id (T × C) ∘ pr₂)
    secondProjection : (s : MAP R Y) → (pr₂ ∘ rightChange s) =₁ pr₂
    secondProjection s = comp-unitˡ pr₂ ∙ pair-β₂ (s ∘ pr₁) (id (T × C) ∘ pr₂)
    second : (s : MAP R Y) → ((pr₁ ∘ pr₂) ∘ rightChange s) =₁ (pr₁ ∘ pr₂)
    second s = post-triangle pr₁ pr₂ (rightChange s) (secondProjection s)
    third : (s : MAP R Y) → ((pr₂ ∘ pr₂) ∘ rightChange s) =₁ (pr₂ ∘ pr₂)
    third s = post-triangle pr₂ pr₂ (rightChange s) (secondProjection s)
    normal : MAP R Y → MAP (R × (T × C)) ((Y × T) × C)
    normal s = pair (pair (s ∘ pr₁) (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)
    left-inner : (s : MAP R Y)
      → (pair pr₁ (pr₁ ∘ pr₂) ∘ rightChange s) =₁ pair (s ∘ pr₁) (pr₁ ∘ pr₂)
    left-inner s = pair⁼ (first s) (second s) ∙ pair-pre pr₁ (pr₁ ∘ pr₂) (rightChange s)
    left-normal : (s : MAP R Y) → (rY ∘ rightChange s) =₁ normal s
    left-normal s = pair⁼ (left-inner s) (third s) ∙
      pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (rightChange s)
    normalAction : normal σ ＝ normal τ
    normalAction = pair⁼ (pair⁼ (γ ▷ pr₁) (const (id₌ (pr₁ ∘ pr₂))))
      (const (id₌ (pr₂ ∘ pr₂)))

    first-natural : SquareCell₌ (pr₁ ◁ δ) (γ ▷ pr₁) (const (first σ)) (const (first τ))
    first-natural = pair⁼-triangle₁ (γ ▷ pr₁) (const (id₌ (id (T × C))) ▷ pr₂)
    secondProjection-natural : SquareCell₌ (pr₂ ◁ δ) (const (id₌ pr₂))
      (const (secondProjection σ)) (const (secondProjection τ))
    secondProjection-natural = paste-fixed
      (replace-edges₌ (id₌ (pr₂ ◁ δ)) (pre-identity (id (T × C)) pr₂)
        (pair⁼-triangle₂ (γ ▷ pr₁) (const (id₌ (id (T × C))) ▷ pr₂)))
      (constant-identity-square (comp-unitˡ pr₂))
    second-natural : SquareCell₌ ((pr₁ ∘ pr₂) ◁ δ) (const (id₌ (pr₁ ∘ pr₂)))
      (const (second σ)) (const (second τ))
    second-natural = replace-edges₌ (id₌ ((pr₁ ∘ pr₂) ◁ δ)) (post-identity pr₁ pr₂)
      (post-triangle-inner pr₁ pr₂ δ (const (id₌ pr₂))
        (secondProjection σ) (secondProjection τ) secondProjection-natural)
    third-natural : SquareCell₌ ((pr₂ ∘ pr₂) ◁ δ) (const (id₌ (pr₂ ∘ pr₂)))
      (const (third σ)) (const (third τ))
    third-natural = replace-edges₌ (id₌ ((pr₂ ∘ pr₂) ◁ δ)) (post-identity pr₂ pr₂)
      (post-triangle-inner pr₂ pr₂ δ (const (id₌ pr₂))
        (secondProjection σ) (secondProjection τ) secondProjection-natural)
    left-natural : SquareCell₌ (rY ◁ δ) normalAction (const (left-normal σ)) (const (left-normal τ))
    left-natural = pair-evaluation-fixed (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) δ
      (left-inner σ) (left-inner τ) (third σ) (third τ)
      (pair⁼ (γ ▷ pr₁) (const (id₌ (pr₁ ∘ pr₂)))) (const (id₌ (pr₂ ∘ pr₂)))
      (pair-evaluation-fixed pr₁ (pr₁ ∘ pr₂) δ (first σ) (first τ) (second σ) (second τ)
        (γ ▷ pr₁) (const (id₌ (pr₁ ∘ pr₂))) first-natural second-natural)
      third-natural

    inner : productMap σ (id T) ＝ productMap τ (id T)
    inner = productMap-cong γ (const (id₌ (id T)))
    outer : leftChange σ ＝ leftChange τ
    outer = productMap-cong inner (const (id₌ (id C)))
    point₁ : MAP (R × (T × C)) (R × T)
    point₁ = pair pr₁ (pr₁ ∘ pr₂)
    point₂ : MAP (R × (T × C)) C
    point₂ = pr₂ ∘ pr₂
    right-inner : (s : MAP R Y)
      → (productMap s (id T) ∘ point₁) =₁ pair (s ∘ pr₁) (pr₁ ∘ pr₂)
    right-inner s = pair⁼ (id₌ (s ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)) ∙
      productMap-pair s (id T) pr₁ (pr₁ ∘ pr₂)
    right-start : (s : MAP R Y)
      → (leftChange s ∘ rR) =₁ pair (productMap s (id T) ∘ point₁) (id C ∘ point₂)
    right-start s = productMap-pair (productMap s (id T)) (id C) point₁ point₂
    right-end : (s : MAP R Y)
      → pair (productMap s (id T) ∘ point₁) (id C ∘ point₂) =₁ normal s
    right-end s = pair⁼ (right-inner s) (comp-unitˡ point₂)
    right-normal : (s : MAP R Y) → (leftChange s ∘ rR) =₁ normal s
    right-normal s = right-end s ∙ right-start s
    right-inner-natural : SquareCell₌ (inner ▷ point₁)
      (pair⁼ (γ ▷ pr₁) (const (id₌ (pr₁ ∘ pr₂))))
      (const (right-inner σ)) (const (right-inner τ))
    right-inner-natural = paste-fixed
      (productMap-pair-outer γ (const (id₌ (id T))) pr₁ (pr₁ ∘ pr₂))
      (pair-fixed (identity-square₌ (γ ▷ pr₁))
        (replace-edges₌ ((pre-identity (id T) (pr₁ ∘ pr₂)) ⁻¹)
          (id₌ (const (id₌ (pr₁ ∘ pr₂)))) (constant-identity-square (comp-unitˡ (pr₁ ∘ pr₂)))))
    right-natural : SquareCell₌ (outer ▷ rR) normalAction
      (const (right-normal σ)) (const (right-normal τ))
    right-natural = paste-fixed
      (productMap-pair-outer inner (const (id₌ (id C))) point₁ point₂)
      (pair-fixed right-inner-natural
        (replace-edges₌ ((pre-identity (id C) point₂) ⁻¹) (id₌ (const (id₌ point₂)))
          (constant-identity-square (comp-unitˡ point₂))))

    regroup-comparison : SquareCell₌ (rY ◁ δ) (outer ▷ rR)
      (const (Reassociation.backward-natural σ)) (const (Reassociation.backward-natural τ))
    regroup-comparison = paste-fixed left-natural (inverse-fixed right-natural)
```

## The represented family and its decoding

The six squares follow the six factors in `evaluation-represents`.
Decoding then uses restriction to the terminal first coordinate. No new
inverse is chosen in these comparisons.

```agda
module _ {Γ : Context} {X R Y T C : CAT Γ} where
  open Terms.Equalities X using (_＝_)

  product-regroup-backward-inputs : {σ τ : MAP R Y} (γ : σ ＝ τ)
    → SquareCell₌
        (Associativity.backward Y T C ◁ productMap-cong γ (const (id₌ (id (T × C)))))
        (productMap-cong (productMap-cong γ (const (id₌ (id T)))) (const (id₌ (id C)))
          ▷ Associativity.backward R T C)
        (const (Reassociation.backward-natural σ)) (const (Reassociation.backward-natural τ))
  product-regroup-backward-inputs = regroup-comparison

module _ {Γ : Context} {F C D : CAT Γ} (e : MAP (F × C) D) (T : CAT Γ) where
  module _ {X P : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    evaluation-represents-inputs : {g h : MAP P (Map T F)} (γ : g ＝ h)
      → SquareCell₌ (evaluate⁼ mapEval (evaluation-forward e T ◁ γ))
          (evaluate⁼ e (evaluate⁼ mapEval γ) ▷ Associativity.backward P T C)
          (const (evaluation-represents e T g)) (const (evaluation-represents e T h))
    evaluation-represents-inputs {g} {h} γ =
      paste-fixed (paste-fixed (paste-fixed (paste-fixed (paste-fixed
        (evaluate-restrict-substitution mapEval (evaluation-forward e T) γ)
        (interchange-fixedOuter beta pairAction))
        (postWhisker-comp pairAction (Associativity.backward (Map T F) T C) universal))
        (post-fixed universal (regroup-comparison {T = T} {C = C} γ)))
        (inverse-fixed (whisker-mixed tripleAction regroup universal)))
        (pre-fixed regroup (inverse-fixed (evaluate-restrict-substitution e mapEval innerAction)))
      where
      regroup : MAP (P × (T × C)) ((P × T) × C)
      regroup = Associativity.backward P T C
      universal : MAP ((Map T F × T) × C) D
      universal = evaluate e mapEval
      pairAction : MAP X (Equal (productMap g (id (T × C))) (productMap h (id (T × C))))
      pairAction = productMap-cong γ (const (id₌ (id (T × C))))
      innerAction : MAP X (Equal (productMap g (id T)) (productMap h (id T)))
      innerAction = productMap-cong γ (const (id₌ (id T)))
      tripleAction : MAP X (Equal (productMap (productMap g (id T)) (id C))
        (productMap (productMap h (id T)) (id C)))
      tripleAction = productMap-cong innerAction (const (id₌ (id C)))
      beta : uncurry (evaluation-forward e T) =₁ evaluation-universal e T
      beta = mapCurry-β (map-isAn T F) (evaluation-universal e T)

  private
    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)

      decoded-family : {A B : CAT Γ} {p q : MAP One (Map A B)}
        → p ＝ q → decode p ＝ decode q
      decoded-family {A = A} γ = evaluate⁼ mapEval γ ▷ product-unitˡ-inverse A

      decoded-family-formula : {A B : CAT Γ} {p q : MAP One (Map A B)} (γ : p ＝ q)
        → decode⁼ γ =₁ decoded-family γ
      decoded-family-formula {A = A} γ =
        (preWhisker (product-unitˡ-inverse A) ◁ Mapping.uncurry⁼-evaluate γ) ∙ decode⁼-evaluate γ

      evaluation-decode-inputs : {p q : MAP One (Map T F)} (γ : p ＝ q)
        → SquareCell₌ (decoded-family (evaluation-forward e T ◁ γ))
            (evaluate⁼ e (decoded-family γ))
            (const (evaluation-decode e T p)) (const (evaluation-decode e T q))
      evaluation-decode-inputs {p} {q} γ =
        paste-fixed (paste-fixed (paste-fixed
          (pre-fixed (product-unitˡ-inverse (T × C)) (evaluation-represents-inputs γ))
          (preWhisker-comp (evaluate⁼ e (evaluate⁼ mapEval γ)) regroup (product-unitˡ-inverse (T × C))))
          ((interchange-fixedInner (evaluate⁼ e (evaluate⁼ mapEval γ)) (evaluation-terminal-regroup e T)) ⁻¹))
          (inverse-fixed (evaluate-restrict-inputs e (evaluate⁼ mapEval γ) (product-unitˡ-inverse T)))
        where
        regroup : MAP (One × (T × C)) ((One × T) × C)
        regroup = Associativity.backward One T C

      evaluation-cong-inputs : {P : CAT Γ} {f g f′ g′ : MAP P F}
        {α : f ＝ g} {β : f′ ＝ g′} (p : f =₁ f′) (q : g =₁ g′)
        → SquareCell₌ α β (const p) (const q)
        → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β)
            (const (evaluate-cong e p)) (const (evaluate-cong e q))
      evaluation-cong-inputs p q square = post-fixed e
        (replace-sides₌ (productMap-cong-constant p (id₌ (id C)))
          (productMap-cong-constant q (id₌ (id C)))
          (productMap-cong-square square (identity-square₌ (const (id₌ (id C))))))

      specialization-formula : {f g : MAP T F} (α : f ＝ g)
        → specialize⁼ (evaluation-forward e T) α =₁
            decoded-family (evaluation-forward e T ◁ name⁼ α)
      specialization-formula {f} {g} α =
        let H = evaluation-forward e T
            names = name⁼-functor f g
            action = postWhisker H
            decodes = decode⁼-functor (H ∘ name f) (H ∘ name g)
        in decoded-family-formula (H ◁ name⁼ α) ∙
          ((decodes ◁ ((action ◁ name⁼-functor-evaluate α) ∙ comp-assoc α names action)) ∙
            comp-assoc α (action ∘ names) decodes)
```

## The native realization square

Name the input family, apply the decoded evaluation square, and use the
already proved decoded-name square. This retains the literal components
of `evaluation-specialize` at both endpoints. At the universal family the
square transfers equivalence to the actual native identification functor.

```agda
  module _ {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)

    evaluation-specialize-inputs : {f g : MAP T F} (α : f ＝ g)
      → SquareCell₌ (specialize⁼ (evaluation-forward e T) α) (evaluate⁼ e α)
          (const (evaluation-specialize e T f)) (const (evaluation-specialize e T g))
    evaluation-specialize-inputs {f} {g} α = paste-fixed
      (replace-edges₌ ((specialization-formula α) ⁻¹)
        (evaluate⁼-cong e ((decoded-family-formula (name⁼ α)) ⁻¹))
        (evaluation-decode-inputs (name⁼ α)))
      (evaluation-cong-inputs (decode-name f) (decode-name g) (decode-name-natural α))

  evaluation-action-isEquiv : IsEquiv (evaluation-forward e T) → (f g : MAP T F)
    → IsEquiv (evaluation-action e f g)
  evaluation-action-isEquiv universal f g =
    endpoint-change-preserves-isEquiv (specialize⁼-functor (evaluation-forward e T) f g)
      (evaluation-action e f g) (evaluation-specialize e T f) (evaluation-specialize e T g)
      (replace-edges₌ (comp-unitʳ (specialize⁼-functor (evaluation-forward e T) f g))
        (id₌ (evaluation-action e f g)) (evaluation-specialize-inputs (id (Equal f g))))
      (specialize⁼-isEquiv (evaluation-forward e T) universal f g)
```
