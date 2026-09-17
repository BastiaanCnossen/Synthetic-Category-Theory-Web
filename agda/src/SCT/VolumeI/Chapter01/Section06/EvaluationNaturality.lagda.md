# Naturality of an arbitrary evaluation

The product-with-identity action and its substitution comparisons are
constructed for any evaluation functor. No functor-category axiom is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section02.Parameterized as Param
import SCT.VolumeI.Chapter01.Section02.FamilyNaturality as FN
import SCT.VolumeI.Chapter01.Section02.FamilyPairing as FPair
import SCT.VolumeI.Chapter01.Section02.Whiskering as WhiskeringEquivalences

module SCT.VolumeI.Chapter01.Section06.EvaluationNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M
  using (product-family-square; slice-comparison; slice-comparison-inputs; slice-comparison-substitution; post-family-square)
open import SCT.VolumeI.Chapter01.Section06.Evaluation 𝒯 M using (module Evaluation)
open FP vocabulary terminal products productLaws composition vertical whiskering
open Param vocabulary terminal products productLaws composition vertical
  using (const-cong; unitˡ; unitʳ; assoc; right-cancelʳ)
open Param.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (family-move-square; family-interchange-fixedInner; family-pair-pre-substitution; family-pair-pre-inputs; family-interchange-fixedOuter)
open FPair vocabulary terminal products productLaws composition vertical whiskering
  using (post-constant; post-composition; pairing; pairing-triangle₁; pairing-triangle₂; pre-constant)

module Action {F C D : CAT} (e : MAP (F × C) D) where
  open Evaluation e using (uncurry; uncurry-cong; uncurry-pre)

  isoMap : {T : CAT} (f g : MAP T F) → MAP (f ＝ g) (uncurry f ＝ uncurry g)
  isoMap f g = postWhisker e ∘ productFamily (id (f ＝ g)) (const (idIso (id C)))

  uncurryFamily : {A X : CAT} {f g : MAP X (F)}
    → MAP A (f ＝ g) → MAP A (uncurry f ＝ uncurry g)
  uncurryFamily α = e ◁ productFamily α (const (idIso (id C)))
  
  uncurryFamily-cong : {A X : CAT} {f g : MAP X (F)}
    {α β : MAP A (f ＝ g)} → =₁ α β → =₁ (uncurryFamily α) (uncurryFamily β)
  uncurryFamily-cong p = postWhisker e ◁
    productFamily-cong p (idIso (const (idIso (id C))))
  
  uncurryFamily-at : {A X : CAT} {f g : MAP X (F)}
    (α : MAP A (f ＝ g))
    → =₁ (isoMap f g ∘ α) (uncurryFamily α)
  uncurryFamily-at {f = f} {g} α =
    (postWhisker e ◁
      (productFamily-cong (comp-unitˡ α) (const-pre (idIso (id C)) α) ∙
        productFamily-restrict (id (f ＝ g)) (const (idIso (id C))) α)) ∙
    comp-assoc α (productFamily (id (f ＝ g)) (const (idIso (id C)))) (postWhisker e)
  
  uncurryFamily-identity : {A X : CAT} (f : MAP X (F))
    → =₁ (uncurryFamily (const {P = A} (idIso f))) (const (idIso (uncurry f)))
  uncurryFamily-identity f =
    const-cong (postWhisker-idIso e (productMap f (id C))) ∙
    (post-constant e (idIso (productMap f (id C))) ∙
      (postWhisker e ◁ productFamily-identity f (id C)))
  
  uncurryFamily-composition : {A X : CAT} {f g h : MAP X (F)}
    (β : MAP A (g ＝ h)) (α : MAP A (f ＝ g))
    → =₁ (uncurryFamily (β ∙ α)) (uncurryFamily β ∙ uncurryFamily α)
  uncurryFamily-composition β α =
    let identity = const (idIso (id C))
    in post-composition e (productFamily β identity) (productFamily α identity) ∙
      (postWhisker e ◁
        (productFamily-composition β α identity identity ∙
          productFamily-cong (idIso (β ∙ α)) (invIso (unitˡ identity))))
  
  uncurryFamily-restrict : {A B X : CAT} {f g : MAP X (F)}
    (α : MAP A (f ＝ g)) (r : MAP B A)
    → =₁ (uncurryFamily α ∘ r) (uncurryFamily (α ∘ r))
  uncurryFamily-restrict α r =
    (postWhisker e ◁
      (productFamily-cong (idIso (α ∘ r)) (const-pre (idIso (id C)) r) ∙
        productFamily-restrict α (const (idIso (id C))) r)) ∙
    postWhisker-pre e (productFamily α (const (idIso (id C)))) r
  
  uncurryFamily-constant : {A X : CAT} {f g : MAP X (F)}
    (α : =₁ f g)
    → =₁ (uncurryFamily (const {P = A} α)) (const (uncurry-cong α))
  uncurryFamily-constant α =
    post-constant e (productMap-cong α (idIso (id C))) ∙
      (postWhisker e ◁ productFamily-constant α (idIso (id C)))
  
  uncurry-pre-inputs : {A Y X : CAT} {f g : MAP X (F)}
    (α : MAP A (f ＝ g)) (σ : MAP Y X)
    → =₁ (const (uncurry-pre g σ) ∙ uncurryFamily (α ▷ σ))
        ((uncurryFamily α ▷ productMap σ (id C)) ∙ const (uncurry-pre f σ))
  uncurry-pre-inputs {f = f} {g} α σ =
    let s = productMap σ (id C)
        pf = productMap f (id C)
        pg = productMap g (id C)
        pα = productFamily α (const (idIso (id C)))
        pασ = productFamily (α ▷ σ) (const (idIso (id C)))
        first = post-family-square e
          (invIso (slice-comparison f σ)) (invIso (slice-comparison g σ)) pασ (pα ▷ s)
          (family-move-square (slice-comparison g σ) (pα ▷ s) pασ (slice-comparison f σ)
            (slice-comparison-inputs α σ))
        last = family-move-square (comp-assoc s pg e)
          ((e ◁ pα) ▷ s) (e ◁ (pα ▷ s)) (comp-assoc s pf e)
          (whisker-mixed-general pα s e)
    in paste-family-squares
      (e ◁ invIso (slice-comparison f σ)) (e ◁ invIso (slice-comparison g σ))
      (invIso (comp-assoc s pf e)) (invIso (comp-assoc s pg e))
      (uncurryFamily (α ▷ σ)) (e ◁ (pα ▷ s)) ((uncurryFamily α) ▷ s) first last
  
  
  uncurry-pre-substitution : {A Y X : CAT} (f : MAP X (F))
    {σ τ : MAP Y X} (γ : MAP A (σ ＝ τ))
    → =₁ (const (uncurry-pre f τ) ∙ uncurryFamily (f ◁ γ))
        ((uncurry f ◁ productFamily γ (const (idIso (id C)))) ∙ const (uncurry-pre f σ))
  uncurry-pre-substitution f {σ} {τ} γ =
    let s = productMap σ (id C)
        t = productMap τ (id C)
        pf = productMap f (id C)
        pγ = productFamily γ (const (idIso (id C)))
        pfγ = productFamily (f ◁ γ) (const (idIso (id C)))
        first = post-family-square e
          (invIso (slice-comparison f σ)) (invIso (slice-comparison f τ)) pfγ (pf ◁ pγ)
          (family-move-square (slice-comparison f τ) (pf ◁ pγ) pfγ (slice-comparison f σ)
            (slice-comparison-substitution f γ))
        last = family-move-square (comp-assoc t pf e)
          (uncurry f ◁ pγ) (e ◁ (pf ◁ pγ)) (comp-assoc s pf e)
          (postWhisker-comp-general pγ pf e)
    in paste-family-squares
      (e ◁ invIso (slice-comparison f σ)) (e ◁ invIso (slice-comparison f τ))
      (invIso (comp-assoc s pf e)) (invIso (comp-assoc t pf e))
      (uncurryFamily (f ◁ γ)) (e ◁ (pf ◁ pγ)) (uncurry f ◁ pγ) first last
  
  uncurryIso : {T : CAT} {f g : MAP T F} → =₁ f g → =₁ (uncurry f) (uncurry g)
  uncurryIso {f = f} {g} α = isoMap f g ∘ α

  uncurryIso-at : {T : CAT} {f g : MAP T F} (α : =₁ f g) →
    =₂ (uncurryIso α) (uncurry-cong α)
  uncurryIso-at α = (postWhisker e ◁
    (productFamily-absolute α (idIso (id C)) ∙
      productFamily-cong (idIso α) (const-One (idIso (id C))))) ∙ uncurryFamily-at α

  uncurry-cong-id : {T : CAT} (f : MAP T F) →
    =₂ (uncurry-cong (idIso f)) (idIso (uncurry f))
  uncurry-cong-id f = postWhisker-idIso e (productMap f (id C)) ∙
    (postWhisker e ◁ productMap-cong-id f (id C))

  uncurry-cong-comp : {T : CAT} {f g h : MAP T F}
    (β : =₁ g h) (α : =₁ f g) →
    =₂ (uncurry-cong (β ∙ α)) (uncurry-cong β ∙ uncurry-cong α)
  uncurry-cong-comp β α = postWhisker-isoComp-at e
    (productMap-cong β (idIso (id C))) (productMap-cong α (idIso (id C))) ∙
    (postWhisker e ◁
      (productMap-cong-comp β α (idIso (id C)) (idIso (id C)) ∙
        productMap-cong-Iso₂ (idIso (β ∙ α)) (invIso (isoComp-unitˡ-at (idIso (id C))))))

  uncurryIso-id : {T : CAT} (f : MAP T F) →
    =₂ (uncurryIso (idIso f)) (idIso (uncurry f))
  uncurryIso-id f = uncurry-cong-id f ∙ uncurryIso-at (idIso f)

  uncurryIso-comp : {T : CAT} {f g h : MAP T F}
    (β : =₁ g h) (α : =₁ f g) →
    =₂ (uncurryIso (β ∙ α)) (uncurryIso β ∙ uncurryIso α)
  uncurryIso-comp β α = invIso (isoComp-cong (uncurryIso-at β) (uncurryIso-at α)) ∙
    (uncurry-cong-comp β α ∙ uncurryIso-at (β ∙ α))

open import SCT.VolumeI.Chapter01.Section03.Uncurrying 𝒯 M using (productMap-pair; module Reassociation)
open import SCT.VolumeI.Chapter01.Section03.CompositionNaturality 𝒯 M using (coordinate-at)

coordinate-at-outer-family : {A X K B C : CAT} {F G : MAP B C}
  (α : MAP A (F ＝ G)) (π : MAP K B) (t : MAP X K)
  {p : MAP X B} (b : =₁ (π ∘ t) p) →
  =₁ (const (coordinate-at G π t b) ∙ ((α ▷ π) ▷ t))
    ((α ▷ p) ∙ const (coordinate-at F π t b))
coordinate-at-outer-family {F = F} {G} α π t {p} b =
  paste-family-squares (comp-assoc t π F) (comp-assoc t π G) (F ◁ b) (G ◁ b)
    ((α ▷ π) ▷ t) (α ▷ (π ∘ t)) (α ▷ p)
    (preWhisker-comp-general α π t) (invIso (family-interchange-fixedInner α b))

productMap-pair-outer-family : {A X B C D E : CAT}
  {f f′ : MAP B C} {g g′ : MAP D E}
  (α : MAP A (f ＝ f′)) (β : MAP A (g ＝ g′)) (p : MAP X B) (q : MAP X D) →
  =₁ (const (productMap-pair f′ g′ p q) ∙ (productFamily α β ▷ pair p q))
    (pairing (α ▷ p) (β ▷ q) ∙ const (productMap-pair f g p q))
productMap-pair-outer-family {f = f} {f′} {g} {g′} α β p q =
  let t = pair p q
      b = pair-β₁ p q
      d = pair-β₂ p q
      left = coordinate-at f pr₁ t b
      left′ = coordinate-at f′ pr₁ t b
      right = coordinate-at g pr₂ t d
      right′ = coordinate-at g′ pr₂ t d
  in paste-family-squares (pair-pre (f ∘ pr₁) (g ∘ pr₂) t)
    (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) t)
    (pair-cong left right) (pair-cong left′ right′)
    (productFamily α β ▷ t) (pairing ((α ▷ pr₁) ▷ t) ((β ▷ pr₂) ▷ t))
    (pairing (α ▷ p) (β ▷ q))
    (invIso (family-pair-pre-inputs (α ▷ pr₁) (β ▷ pr₂) t))
    (pair-family-square left left′ right right′ ((α ▷ pr₁) ▷ t) (α ▷ p)
      ((β ▷ pr₂) ▷ t) (β ▷ q)
      (coordinate-at-outer-family α pr₁ t b) (coordinate-at-outer-family β pr₂ t d))

post-evaluation-family : {A X K B C : CAT} (F : MAP B C) (u : MAP K B)
  {r s : MAP X K} (δ : MAP A (r ＝ s)) {x y : MAP X B}
  (b : =₁ (u ∘ r) x) (b′ : =₁ (u ∘ s) y) (η : MAP A (x ＝ y)) →
  =₁ (const b′ ∙ (u ◁ δ)) (η ∙ const b) →
  =₁ (const ((F ◁ b′) ∙ comp-assoc s u F) ∙ ((F ∘ u) ◁ δ))
    ((F ◁ η) ∙ const ((F ◁ b) ∙ comp-assoc r u F))
post-evaluation-family F u {r} {s} δ b b′ η p =
  paste-family-squares (comp-assoc r u F) (comp-assoc s u F) (F ◁ b) (F ◁ b′)
    ((F ∘ u) ◁ δ) (F ◁ (u ◁ δ)) (F ◁ η)
    (postWhisker-comp-general δ u F) (post-family-square F b b′ (u ◁ δ) η p)

pair-evaluation-family : {A X K B C : CAT} (f : MAP K B) (g : MAP K C)
  {r s : MAP X K} (δ : MAP A (r ＝ s))
  {x x′ : MAP X B} {y y′ : MAP X C}
  (b : =₁ (f ∘ r) x) (b′ : =₁ (f ∘ s) x′)
  (d : =₁ (g ∘ r) y) (d′ : =₁ (g ∘ s) y′)
  (α : MAP A (x ＝ x′)) (β : MAP A (y ＝ y′)) →
  =₁ (const b′ ∙ (f ◁ δ)) (α ∙ const b) →
  =₁ (const d′ ∙ (g ◁ δ)) (β ∙ const d) →
  =₁ (const (pair-cong b′ d′ ∙ pair-pre f g s) ∙ (pair f g ◁ δ))
    (pairing α β ∙ const (pair-cong b d ∙ pair-pre f g r))
pair-evaluation-family f g {r} {s} δ b b′ d d′ α β p q =
  paste-family-squares (pair-pre f g r) (pair-pre f g s)
    (pair-cong b d) (pair-cong b′ d′)
    (pair f g ◁ δ) (pairing (f ◁ δ) (g ◁ δ)) (pairing α β)
    (invIso (family-pair-pre-substitution f g δ))
    (pair-family-square b b′ d d′ (f ◁ δ) α (g ◁ δ) β p q)

identity-family-square : {A X Y : CAT} {f g : MAP X Y} (α : MAP A (f ＝ g)) →
  =₁ (const (idIso g) ∙ α) (α ∙ const (idIso f))
identity-family-square α = invIso (unitʳ α) ∙ unitˡ α

constant-family-square : {A X Y : CAT} {f g : MAP X Y} (α : =₁ f g) →
  =₁ (const {P = A} α ∙ const (idIso f)) (const (idIso g) ∙ const α)
constant-family-square α = invIso (unitˡ (const α)) ∙ unitʳ (const α)

pre-identity-family : {A R X Y : CAT} (f : MAP X Y) (r : MAP R X) →
  =₁ ((const {P = A} (idIso f)) ▷ r) (const (idIso (f ∘ r)))
pre-identity-family f r = const-cong (preWhisker-idIso f r) ∙ pre-constant (idIso f) r

post-identity-family : {A R X Y : CAT} (f : MAP X Y) (r : MAP R X) →
  =₁ (f ◁ const {P = A} (idIso r)) (const (idIso (f ∘ r)))
post-identity-family f r = const-cong (postWhisker-idIso f r) ∙ post-constant f (idIso r)

module Regroup {A R Y X C : CAT} {σ τ : MAP R Y} (γ : MAP A (σ ＝ τ)) where
  rR = Associativity.backward R X C
  rY = Associativity.backward Y X C
  rightChange : MAP R Y → MAP (R × (X × C)) (Y × (X × C))
  rightChange s = productMap s (id (X × C))
  leftChange : MAP R Y → MAP ((R × X) × C) ((Y × X) × C)
  leftChange s = productMap (productMap s (id X)) (id C)
  δ = productFamily γ (const (idIso (id (X × C))))
  first : (s : MAP R Y) → =₁ (pr₁ ∘ rightChange s) (s ∘ pr₁)
  first s = pair-β₁ (s ∘ pr₁) (id (X × C) ∘ pr₂)
  secondProjection : (s : MAP R Y) → =₁ (pr₂ ∘ rightChange s) pr₂
  secondProjection s = comp-unitˡ pr₂ ∙ pair-β₂ (s ∘ pr₁) (id (X × C) ∘ pr₂)
  second : (s : MAP R Y) → =₁ ((pr₁ ∘ pr₂) ∘ rightChange s) (pr₁ ∘ pr₂)
  second s = (pr₁ ◁ secondProjection s) ∙ comp-assoc (rightChange s) pr₂ pr₁
  third : (s : MAP R Y) → =₁ ((pr₂ ∘ pr₂) ∘ rightChange s) (pr₂ ∘ pr₂)
  third s = (pr₂ ◁ secondProjection s) ∙ comp-assoc (rightChange s) pr₂ pr₂
  normal : MAP R Y → MAP (R × (X × C)) ((Y × X) × C)
  normal s = pair (pair (s ∘ pr₁) (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)
  left-inner : (s : MAP R Y) → =₁ ((pair pr₁ (pr₁ ∘ pr₂)) ∘ rightChange s) (pair (s ∘ pr₁) (pr₁ ∘ pr₂))
  left-inner s = pair-cong (first s) (second s) ∙ pair-pre pr₁ (pr₁ ∘ pr₂) (rightChange s)
  left-normal : (s : MAP R Y) → =₁ (rY ∘ rightChange s) (normal s)
  left-normal s = pair-cong (left-inner s) (third s) ∙
    pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) (rightChange s)
  normalAction : MAP A (normal σ ＝ normal τ)
  normalAction = pairing (pairing (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂))))
    (const (idIso (pr₂ ∘ pr₂)))

  first-natural : =₁ (const (first τ) ∙ (pr₁ ◁ δ)) ((γ ▷ pr₁) ∙ const (first σ))
  first-natural = pairing-triangle₁ (γ ▷ pr₁) (const (idIso (id (X × C))) ▷ pr₂)

  secondProjection-natural : =₁ (const (secondProjection τ) ∙ (pr₂ ◁ δ))
    (const (idIso pr₂) ∙ const (secondProjection σ))
  secondProjection-natural = paste-family-squares
    (pair-β₂ (σ ∘ pr₁) (id (X × C) ∘ pr₂)) (pair-β₂ (τ ∘ pr₁) (id (X × C) ∘ pr₂))
    (comp-unitˡ pr₂) (comp-unitˡ pr₂) (pr₂ ◁ δ)
    (const (idIso (id (X × C) ∘ pr₂))) (const (idIso pr₂))
    (isoComp-cong (pre-identity-family (id (X × C)) pr₂) (idIso _) ∙
      pairing-triangle₂ (γ ▷ pr₁) (const (idIso (id (X × C))) ▷ pr₂))
    (constant-family-square (comp-unitˡ pr₂))

  second-natural : =₁ (const (second τ) ∙ ((pr₁ ∘ pr₂) ◁ δ))
    (const (idIso (pr₁ ∘ pr₂)) ∙ const (second σ))
  second-natural = isoComp-cong (post-identity-family pr₁ pr₂) (idIso _) ∙
    post-evaluation-family pr₁ pr₂ δ (secondProjection σ) (secondProjection τ)
      (const (idIso pr₂)) secondProjection-natural

  third-natural : =₁ (const (third τ) ∙ ((pr₂ ∘ pr₂) ◁ δ))
    (const (idIso (pr₂ ∘ pr₂)) ∙ const (third σ))
  third-natural = isoComp-cong (post-identity-family pr₂ pr₂) (idIso _) ∙
    post-evaluation-family pr₂ pr₂ δ (secondProjection σ) (secondProjection τ)
      (const (idIso pr₂)) secondProjection-natural

  left-natural : =₁ (const (left-normal τ) ∙ (rY ◁ δ))
    (normalAction ∙ const (left-normal σ))
  left-natural = pair-evaluation-family (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) δ
    (left-inner σ) (left-inner τ) (third σ) (third τ)
    (pairing (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂)))) (const (idIso (pr₂ ∘ pr₂)))
    (pair-evaluation-family pr₁ (pr₁ ∘ pr₂) δ (first σ) (first τ) (second σ) (second τ)
      (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂))) first-natural second-natural)
    third-natural

  inner = productFamily γ (const (idIso (id X)))
  outer = productFamily inner (const (idIso (id C)))
  point₁ : MAP (R × (X × C)) (R × X)
  point₁ = pair pr₁ (pr₁ ∘ pr₂)
  point₂ : MAP (R × (X × C)) C
  point₂ = pr₂ ∘ pr₂
  right-inner : (s : MAP R Y) → =₁ (productMap s (id X) ∘ point₁) (pair (s ∘ pr₁) (pr₁ ∘ pr₂))
  right-inner s = pair-cong (idIso (s ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)) ∙
    productMap-pair s (id X) pr₁ (pr₁ ∘ pr₂)
  right-start : (s : MAP R Y) → =₁ (leftChange s ∘ rR) (pair (productMap s (id X) ∘ point₁) (id C ∘ point₂))
  right-start s = productMap-pair (productMap s (id X)) (id C) point₁ point₂
  right-end : (s : MAP R Y) → =₁ (pair (productMap s (id X) ∘ point₁) (id C ∘ point₂)) (normal s)
  right-end s = pair-cong (right-inner s) (comp-unitˡ point₂)
  right-normal : (s : MAP R Y) → =₁ (leftChange s ∘ rR) (normal s)
  right-normal s = right-end s ∙ right-start s

  right-inner-natural : =₁ (const (right-inner τ) ∙ (inner ▷ point₁))
    (pairing (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂))) ∙ const (right-inner σ))
  right-inner-natural = paste-family-squares
    (productMap-pair σ (id X) pr₁ (pr₁ ∘ pr₂)) (productMap-pair τ (id X) pr₁ (pr₁ ∘ pr₂))
    (pair-cong (idIso (σ ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)))
    (pair-cong (idIso (τ ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)))
    (inner ▷ point₁) (pairing (γ ▷ pr₁) (const (idIso (id X)) ▷ (pr₁ ∘ pr₂)))
    (pairing (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂))))
    (productMap-pair-outer-family γ (const (idIso (id X))) pr₁ (pr₁ ∘ pr₂))
    (pair-family-square (idIso (σ ∘ pr₁)) (idIso (τ ∘ pr₁))
      (comp-unitˡ (pr₁ ∘ pr₂)) (comp-unitˡ (pr₁ ∘ pr₂))
      (γ ▷ pr₁) (γ ▷ pr₁) (const (idIso (id X)) ▷ (pr₁ ∘ pr₂)) (const (idIso (pr₁ ∘ pr₂)))
      (identity-family-square (γ ▷ pr₁))
      (constant-family-square (comp-unitˡ (pr₁ ∘ pr₂)) ∙
        isoComp-cong (idIso _) (pre-identity-family (id X) (pr₁ ∘ pr₂))))

  right-natural : =₁ (const (right-normal τ) ∙ (outer ▷ rR))
    (normalAction ∙ const (right-normal σ))
  right-natural = paste-family-squares (right-start σ) (right-start τ) (right-end σ) (right-end τ)
    (outer ▷ rR) (pairing (inner ▷ point₁) (const (idIso (id C)) ▷ point₂)) normalAction
    (productMap-pair-outer-family inner (const (idIso (id C))) point₁ point₂)
    (pair-family-square (right-inner σ) (right-inner τ) (comp-unitˡ point₂) (comp-unitˡ point₂)
      (inner ▷ point₁) (pairing (γ ▷ pr₁) (const (idIso (pr₁ ∘ pr₂))))
      (const (idIso (id C)) ▷ point₂) (const (idIso point₂)) right-inner-natural
      (constant-family-square (comp-unitˡ point₂) ∙
        isoComp-cong (idIso _) (pre-identity-family (id C) point₂)))

  comparison : =₁ (const (Reassociation.backward-natural τ) ∙ (rY ◁ δ))
    ((outer ▷ rR) ∙ const (Reassociation.backward-natural σ))
  comparison = paste-family-squares (left-normal σ) (left-normal τ)
    (invIso (right-normal σ)) (invIso (right-normal τ))
    (rY ◁ δ) normalAction (outer ▷ rR) left-natural
    (family-move-square (right-normal τ) (outer ▷ rR) normalAction (right-normal σ) right-natural)

open import SCT.VolumeI.Chapter01.Section03.DecodingNaturality 𝒯 M using (pre-family-square; decodeFamily; decodeFamily-at)
open import SCT.VolumeI.Chapter01.Section03.Compatibility 𝒯 M
  using () renaming (uncurryFamily to mapFamily; uncurry-pre-substitution to mapPreSub)

open WhiskeringEquivalences vocabulary terminal products productLaws composition vertical whiskering
  using (square-right; leftMultiply; rightMultiply; left-evaluate)
open import SCT.VolumeI.Chapter01.Section03.CoherenceTransport 𝒯 using (changeEndpoints-map; changeEndpoints-map-isEquiv)

module Represented {F C D : CAT} (e : MAP (F × C) D) (T : CAT) where
  module E = Evaluation e
  module A = Action e
  open E.At T

  represents-inputs : {K X : CAT} {g h : MAP X parameter} (γ : MAP K (g ＝ h)) →
    =₁ (const (represents h) ∙ mapFamily (forward ◁ γ))
      ((A.uncurryFamily (mapFamily γ) ▷ Associativity.backward X T C) ∙ const (represents g))
  represents-inputs {K} {X} {g} {h} γ =
    paste-family-squares (r5g ∙ (r4g ∙ (r3g ∙ (r2g ∙ r1g))))
      (r5h ∙ (r4h ∙ (r3h ∙ (r2h ∙ r1h)))) r6g r6h action0 action5 action6
      (paste-family-squares (r4g ∙ (r3g ∙ (r2g ∙ r1g)))
        (r4h ∙ (r3h ∙ (r2h ∙ r1h))) r5g r5h action0 action4 action5
        (paste-family-squares (r3g ∙ (r2g ∙ r1g)) (r3h ∙ (r2h ∙ r1h)) r4g r4h action0 action3 action4
          (paste-family-squares (r2g ∙ r1g) (r2h ∙ r1h) r3g r3h action0 action2 action3
            (paste-family-squares r1g r1h r2g r2h action0 action1 action2 square1 square2)
            square3) square4) square5) square6
    where
    regroup = Associativity.backward X T C
    universal = E.uncurry mapEval
    changeg = productMap g (id (T × C))
    changeh = productMap h (id (T × C))
    tripleg = productMap (productMap g (id T)) (id C)
    tripleh = productMap (productMap h (id T)) (id C)
    pairAction = productFamily γ (const (idIso (id (T × C))))
    innerAction = productFamily γ (const (idIso (id T)))
    tripleAction = productFamily innerAction (const (idIso (id C)))
    beta = mapCurry-β (map-isAn T F) evaluation
    r1g = mapUncurry-pre forward g
    r1h = mapUncurry-pre forward h
    r2g = beta ▷ changeg
    r2h = beta ▷ changeh
    r3g = comp-assoc changeg (Associativity.backward parameter T C) universal
    r3h = comp-assoc changeh (Associativity.backward parameter T C) universal
    r4g = universal ◁ Reassociation.backward-natural g
    r4h = universal ◁ Reassociation.backward-natural h
    r5g = invIso (comp-assoc regroup tripleg universal)
    r5h = invIso (comp-assoc regroup tripleh universal)
    r6g = invIso (E.uncurry-pre mapEval (productMap g (id T))) ▷ regroup
    r6h = invIso (E.uncurry-pre mapEval (productMap h (id T))) ▷ regroup
    action0 = mapFamily (forward ◁ γ)
    action1 = mapUncurry forward ◁ pairAction
    action2 = evaluation ◁ pairAction
    action3 = universal ◁ (Associativity.backward parameter T C ◁ pairAction)
    action4 = universal ◁ (tripleAction ▷ regroup)
    action5 = (universal ◁ tripleAction) ▷ regroup
    action6 = A.uncurryFamily (mapFamily γ) ▷ regroup
    square1 = mapPreSub forward γ
    square2 = family-interchange-fixedOuter beta pairAction
    square3 = postWhisker-comp-general pairAction (Associativity.backward parameter T C) universal
    square4 = post-family-square universal (Reassociation.backward-natural g) (Reassociation.backward-natural h)
      (Associativity.backward parameter T C ◁ pairAction) (tripleAction ▷ regroup)
      (Regroup.comparison {X = T} {C = C} γ)
    square5 = family-move-square (comp-assoc regroup tripleh universal) action5 action4
      (comp-assoc regroup tripleg universal) (whisker-mixed-general tripleAction regroup universal)
    square6 = pre-family-square regroup
      (invIso (E.uncurry-pre mapEval (productMap g (id T))))
      (invIso (E.uncurry-pre mapEval (productMap h (id T))))
      (universal ◁ tripleAction) (A.uncurryFamily (mapFamily γ))
      (family-move-square (E.uncurry-pre mapEval (productMap h (id T)))
        (A.uncurryFamily (mapFamily γ)) (universal ◁ tripleAction)
        (E.uncurry-pre mapEval (productMap g (id T))) (A.uncurry-pre-substitution mapEval innerAction))

  decode-forward-inputs : {K : CAT} {p q : Obj-abs parameter} (γ : MAP K (p ＝ q)) →
    =₁ (const (decode-forward q) ∙ decodeFamily (forward ◁ γ))
      (A.uncurryFamily (decodeFamily γ) ∙ const (decode-forward p))
  decode-forward-inputs {p = p} {q} γ =
    paste-family-squares (r3p ∙ (r2p ∙ r1p)) (r3q ∙ (r2q ∙ r1q)) r4p r4q action0 action3 action4
      (paste-family-squares (r2p ∙ r1p) (r2q ∙ r1q) r3p r3q action0 action2 action3
        (paste-family-squares r1p r1q r2p r2q action0 action1 action2
          (pre-family-square (oneProduct-in (T × C)) (represents p) (represents q)
            (mapFamily (forward ◁ γ)) (A.uncurryFamily (mapFamily γ) ▷ regroup)
            (represents-inputs γ))
          (preWhisker-comp-general (A.uncurryFamily (mapFamily γ)) regroup (oneProduct-in (T × C))))
        (invIso (family-interchange-fixedInner (A.uncurryFamily (mapFamily γ)) terminal-regroup)))
      (family-move-square (E.uncurry-pre (mapUncurry q) (oneProduct-in T)) action4 action3
        (E.uncurry-pre (mapUncurry p) (oneProduct-in T))
        (A.uncurry-pre-inputs (mapFamily γ) (oneProduct-in T)))
    where
    regroup = Associativity.backward One T C
    r1p = represents p ▷ oneProduct-in (T × C)
    r1q = represents q ▷ oneProduct-in (T × C)
    r2p = comp-assoc (oneProduct-in (T × C)) regroup (E.uncurry (mapUncurry p))
    r2q = comp-assoc (oneProduct-in (T × C)) regroup (E.uncurry (mapUncurry q))
    r3p = E.uncurry (mapUncurry p) ◁ terminal-regroup
    r3q = E.uncurry (mapUncurry q) ◁ terminal-regroup
    r4p = invIso (E.uncurry-pre (mapUncurry p) (oneProduct-in T))
    r4q = invIso (E.uncurry-pre (mapUncurry q) (oneProduct-in T))
    action0 = decodeFamily (forward ◁ γ)
    action1 = (A.uncurryFamily (mapFamily γ) ▷ regroup) ▷ oneProduct-in (T × C)
    action2 = A.uncurryFamily (mapFamily γ) ▷ (regroup ∘ oneProduct-in (T × C))
    action3 = A.uncurryFamily (mapFamily γ) ▷ productMap (oneProduct-in T) (id C)
    action4 = A.uncurryFamily (decodeFamily γ)

  opaque
    decoded-isoMap-isEquiv : IsEquiv forward → (p q : Obj-abs parameter) →
      IsEquiv (A.isoMap (decodeMap p) (decodeMap q))
    decoded-isoMap-isEquiv forwardEquiv p q =
      equiv-cancel-right decodeAction targetAction (decodeMap-isoMap-isEquiv p q)
        (square-right sourceAction (targetAction ∘ decodeAction)
          (decode-forward p) (decode-forward q) square sourceEquiv)
      where
      decodeAction : MAP (p ＝ q) (decodeMap p ＝ decodeMap q)
      decodeAction = decodeMap-isoMap p q
      targetAction : MAP (decodeMap p ＝ decodeMap q) (E.uncurry (decodeMap p) ＝ E.uncurry (decodeMap q))
      targetAction = A.isoMap (decodeMap p) (decodeMap q)
      targetDecode : MAP ((forward ∘ p) ＝ (forward ∘ q))
        (decodeMap (forward ∘ p) ＝ decodeMap (forward ∘ q))
      targetDecode = decodeMap-isoMap (forward ∘ p) (forward ∘ q)
      sourceAction : MAP (p ＝ q) (decodeMap (forward ∘ p) ＝ decodeMap (forward ∘ q))
      sourceAction = targetDecode ∘ postWhisker forward
      sourceEquiv : IsEquiv sourceAction
      sourceEquiv = equiv-compose (postWhisker forward) targetDecode
        (postWhisker-isEquiv forward forwardEquiv p q)
        (decodeMap-isoMap-isEquiv (forward ∘ p) (forward ∘ q))
      leftNormalize : =₁ sourceAction (decodeFamily (forward ◁ id (p ＝ q)))
      leftNormalize = decodeFamily-at (forward ◁ id (p ＝ q)) ∙
        (targetDecode ◁ invIso (comp-unitʳ (postWhisker forward)))
      decodedNormalize : =₁ decodeAction (decodeFamily (id (p ＝ q)))
      decodedNormalize = decodeFamily-at (id (p ＝ q)) ∙ invIso (comp-unitʳ decodeAction)
      rightNormalize : =₁ (targetAction ∘ decodeAction) (A.uncurryFamily (decodeFamily (id (p ＝ q))))
      rightNormalize = A.uncurryFamily-cong decodedNormalize ∙ A.uncurryFamily-at decodeAction
      square : =₁ (const (decode-forward q) ∙ sourceAction)
        ((targetAction ∘ decodeAction) ∙ const (decode-forward p))
      square = isoComp-cong (invIso rightNormalize) (idIso (const (decode-forward p))) ∙
        (decode-forward-inputs (id (p ＝ q)) ∙
          isoComp-cong (idIso (const (decode-forward q))) leftNormalize)

endpoint-map-square : {X Y : CAT} {f f′ g g′ : MAP X Y}
  (p : =₁ f f′) (q : =₁ g g′) →
  =₁ (const q ∙ id (f ＝ g)) (changeEndpoints-map p q ∙ const p)
endpoint-map-square p q = invIso
  (isoComp-cong (idIso (const q)) (right-cancelʳ p (id _)) ∙
    (assoc (const q) (id _ ∙ const (invIso p)) (const p) ∙
      isoComp-cong (left-evaluate q (rightMultiply (invIso p))) (idIso (const p))))

module ChangeEndpoints {F C D : CAT} (e : MAP (F × C) D) where
  module E = Evaluation e
  module A = Action e

  opaque
    preserves-equivalence : {T : CAT} {f f′ g g′ : MAP T F}
      (p : =₁ f f′) (q : =₁ g g′) →
      IsEquiv (A.isoMap f g) → IsEquiv (A.isoMap f′ g′)
    preserves-equivalence {f = f} {f′} {g} {g′} p q oldEquiv =
      equiv-cancel-right endpoint newAction (changeEndpoints-map-isEquiv p q)
        (equiv-transport (invIso (A.uncurryFamily-at endpoint))
          (square-right oldFamily newFamily (E.uncurry-cong p) (E.uncurry-cong q) square oldFamilyEquiv))
      where
      endpoint : MAP (f ＝ g) (f′ ＝ g′)
      endpoint = changeEndpoints-map p q
      oldFamily : MAP (f ＝ g) (E.uncurry f ＝ E.uncurry g)
      oldFamily = A.uncurryFamily (id (f ＝ g))
      newFamily : MAP (f ＝ g) (E.uncurry f′ ＝ E.uncurry g′)
      newFamily = A.uncurryFamily endpoint
      newAction : MAP (f′ ＝ g′) (E.uncurry f′ ＝ E.uncurry g′)
      newAction = A.isoMap f′ g′
      oldFamilyEquiv : IsEquiv oldFamily
      oldFamilyEquiv = equiv-transport (A.uncurryFamily-at (id (f ＝ g)))
        (equiv-compose (id (f ＝ g)) (A.isoMap f g) (id-isEquiv (f ＝ g)) oldEquiv)
      square : =₁ (const (E.uncurry-cong q) ∙ oldFamily) (newFamily ∙ const (E.uncurry-cong p))
      square = post-family-square e
        (productMap-cong p (idIso (id C))) (productMap-cong q (idIso (id C)))
        (productFamily (id (f ＝ g)) (const (idIso (id C))))
        (productFamily endpoint (const (idIso (id C))))
        (product-family-square p q (idIso (id C)) (idIso (id C))
          (id (f ＝ g)) endpoint (const (idIso (id C))) (const (idIso (id C)))
          (endpoint-map-square p q) (identity-family-square (const (idIso (id C)))))

opaque
  evaluation-isoMap-isEquiv : {F C D : CAT} (e : MAP (F × C) D) (T : CAT) →
    IsEquiv (Evaluation.At.forward e T) → (f g : MAP T F) →
    IsEquiv (Action.isoMap e f g)
  evaluation-isoMap-isEquiv e T universal f g =
    ChangeEndpoints.preserves-equivalence e (decode-name f) (decode-name g)
      (Represented.decoded-isoMap-isEquiv e T universal (nameMap f) (nameMap g))
```


