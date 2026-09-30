# Naturality of evaluation and composition

The comparison between uncurrying a composite and composing evaluations
has a prescribed action on isomorphisms. We construct its naturality square
by pasting the squares for pairing and the specified beta comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.CoordinateNaturality as CoordinateNaturality

import SCT.VolumeI.Chapter01.Section03.ProductCalculus.BinaryFunctorCalculus as BinaryFunctorCalculus

module SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-Iso₂; pair-cong-comp; pair-cong-triangle₁; pair-cong-triangle₂)
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (pair-pre-natural-inputs; pair-pre-natural-substitution; move-square)
open Structural vocabulary terminal products productLaws composition whiskering

open CoordinateNaturality vocabulary terminal products productLaws composition vertical whiskering
  public using (post-square; identity-square; coordinate-at; coordinate-at-outer; coordinate-at-inner)

apply-square : {X C D : CAT}
  {f f′ g g′ : MAP X (Map C D)} {x x′ y y′ : MAP X C}
  (u : f =₁ g) (u′ : f′ =₁ g′)
  (v : x =₁ y) (v′ : x′ =₁ y′)
  (α : f =₁ f′) (β : g =₁ g′)
  (γ : x =₁ x′) (δ : y =₁ y′)
  → (u′ ∙ α) =₂ (β ∙ u) → (v′ ∙ γ) =₂ (δ ∙ v)
  → (applyTerm-cong u′ v′ ∙ applyTerm-cong α γ) =₂
      (applyTerm-cong β δ ∙ applyTerm-cong u v)
apply-square u u′ v v′ α β γ δ p q =
  post-square mapEval (pair-cong u v) (pair-cong u′ v′)
    (pair-cong α γ) (pair-cong β δ) (pair-square u u′ v v′ α β γ δ p q)

apply-cong-Iso₂ : {X C D : CAT}
  {f f′ : MAP X (Map C D)} {x x′ : MAP X C}
  {α α′ : f =₁ f′} {β β′ : x =₁ x′}
  → α =₂ α′ → β =₂ β′
  → (applyTerm-cong α β) =₂ (applyTerm-cong α′ β′)
apply-cong-Iso₂ p q =
  BinaryFunctorCalculus.binary-cong-Iso₂ vocabulary terminal products productLaws composition vertical whiskering
    mapEval p q

open BinaryFunctorCalculus vocabulary terminal products productLaws composition vertical whiskering
  public using (binary-pre-inputs; binary-pre-substitution)

productMap-pair-outer : {X A B C D : CAT}
  {f f′ : MAP A B} {g g′ : MAP C D}
  (α : f =₁ f′) (β : g =₁ g′) (p : MAP X A) (q : MAP X C)
  → (productMap-pair f′ g′ p q ∙ (productMap-cong α β ▷ pair p q)) =₂
      (pair-cong (α ▷ p) (β ▷ q) ∙ productMap-pair f g p q)
productMap-pair-outer {f = f} {f′} {g} {g′} α β p q =
  let t = pair p q
      b = pair-β₁ p q
      d = pair-β₂ p q
      left = coordinate-at f pr₁ t b
      left′ = coordinate-at f′ pr₁ t b
      right = coordinate-at g pr₂ t d
      right′ = coordinate-at g′ pr₂ t d
  in paste-squares (pair-pre (f ∘ pr₁) (g ∘ pr₂) t)
    (pair-pre (f′ ∘ pr₁) (g′ ∘ pr₂) t)
    (pair-cong left right) (pair-cong left′ right′)
    (productMap-cong α β ▷ t) (pair-cong ((α ▷ pr₁) ▷ t) ((β ▷ pr₂) ▷ t))
    (pair-cong (α ▷ p) (β ▷ q))
    ((pair-pre-natural-inputs (α ▷ pr₁) (β ▷ pr₂) t) ⁻¹)
    (pair-square left left′ right right′ ((α ▷ pr₁) ▷ t) (α ▷ p)
      ((β ▷ pr₂) ▷ t) (β ▷ q)
      (coordinate-at-outer α pr₁ t b) (coordinate-at-outer β pr₂ t d))

productMap-pair-inner : {X A B C D : CAT} (f : MAP A B) (g : MAP C D)
  {p p′ : MAP X A} {q q′ : MAP X C} (σ : p =₁ p′) (τ : q =₁ q′)
  → (productMap-pair f g p′ q′ ∙ (productMap f g ◁ pair-cong σ τ)) =₂
      (pair-cong (f ◁ σ) (g ◁ τ) ∙ productMap-pair f g p q)
productMap-pair-inner f g {p} {p′} {q} {q′} σ τ =
  let t = pair p q
      t′ = pair p′ q′
      δ = pair-cong σ τ
      left = coordinate-at f pr₁ t (pair-β₁ p q)
      left′ = coordinate-at f pr₁ t′ (pair-β₁ p′ q′)
      right = coordinate-at g pr₂ t (pair-β₂ p q)
      right′ = coordinate-at g pr₂ t′ (pair-β₂ p′ q′)
  in paste-squares (pair-pre (f ∘ pr₁) (g ∘ pr₂) t)
    (pair-pre (f ∘ pr₁) (g ∘ pr₂) t′)
    (pair-cong left right) (pair-cong left′ right′)
    (productMap f g ◁ δ) (pair-cong ((f ∘ pr₁) ◁ δ) ((g ∘ pr₂) ◁ δ))
    (pair-cong (f ◁ σ) (g ◁ τ))
    ((pair-pre-natural-substitution (f ∘ pr₁) (g ∘ pr₂) δ) ⁻¹)
    (pair-square left left′ right right′ ((f ∘ pr₁) ◁ δ) (f ◁ σ)
      ((g ∘ pr₂) ◁ δ) (g ◁ τ)
      (coordinate-at-inner f pr₁ (pair-β₁ p q) (pair-β₁ p′ q′) δ σ
        (pair-cong-triangle₁ σ τ))
      (coordinate-at-inner g pr₂ (pair-β₂ p q) (pair-β₂ p′ q′) δ τ
        (pair-cong-triangle₂ σ τ)))

unit-input-square : {X C : CAT} (x : MAP X C)
  → (comp-unitˡ x ∙ (idIso (id C) ▷ x)) =₂ (idIso x ∙ comp-unitˡ x)
unit-input-square {C = C} x = (isoComp-unitˡ-at (comp-unitˡ x)) ⁻¹ ∙
  (isoComp-unitʳ-at (comp-unitˡ x) ∙
    isoComp-cong (idIso (comp-unitˡ x)) (preWhisker-idIso (id C) x))

mapUncurry-at-outer : {Γ X C D : CAT} {f g : MAP X (Map C D)}
  (α : f =₁ g) (p : MAP Γ X) (x : MAP Γ C)
  → (mapUncurry-at g p x ∙ (mapUncurry-cong α ▷ pair p x)) =₂
      (applyTerm-cong (α ▷ p) (idIso x) ∙ mapUncurry-at f p x)
mapUncurry-at-outer {C = C} {f = f} {g} α p x =
  let input = productMap-cong α (idIso (id C))
      middle = pair-cong (α ▷ p) (idIso (id C) ▷ x)
      output = pair-cong (α ▷ p) (idIso x)
      normalize = pair-cong (idIso (f ∘ p)) (comp-unitˡ x)
      normalize′ = pair-cong (idIso (g ∘ p)) (comp-unitˡ x)
      square = paste-squares (productMap-pair f (id C) p x)
        (productMap-pair g (id C) p x) normalize normalize′
        (input ▷ pair p x) middle output
        (productMap-pair-outer α (idIso (id C)) p x)
        (pair-square (idIso (f ∘ p)) (idIso (g ∘ p)) (comp-unitˡ x) (comp-unitˡ x)
          (α ▷ p) (α ▷ p) (idIso (id C) ▷ x) (idIso x)
          (identity-square (α ▷ p)) (unit-input-square x))
  in paste-squares (comp-assoc (pair p x) (productMap f (id C)) mapEval)
    (comp-assoc (pair p x) (productMap g (id C)) mapEval)
    (mapEval ◁ (normalize ∙ productMap-pair f (id C) p x))
    (mapEval ◁ (normalize′ ∙ productMap-pair g (id C) p x))
    (mapUncurry-cong α ▷ pair p x) (mapEval ◁ (input ▷ pair p x))
    (mapEval ◁ output) (whisker-mixed-at input (pair p x) mapEval)
    (post-square mapEval (normalize ∙ productMap-pair f (id C) p x)
      (normalize′ ∙ productMap-pair g (id C) p x) (input ▷ pair p x) output square)

mapUncurry-at-inner : {Γ X C D : CAT} (f : MAP X (Map C D))
  {p p′ : MAP Γ X} {x x′ : MAP Γ C} (σ : p =₁ p′) (τ : x =₁ x′)
  → (mapUncurry-at f p′ x′ ∙ (mapUncurry f ◁ pair-cong σ τ)) =₂
      (applyTerm-cong (f ◁ σ) τ ∙ mapUncurry-at f p x)
mapUncurry-at-inner {C = C} f {p} {p′} {x} {x′} σ τ =
  let input = pair-cong σ τ
      middle = pair-cong (f ◁ σ) (id C ◁ τ)
      output = pair-cong (f ◁ σ) τ
      normalize = pair-cong (idIso (f ∘ p)) (comp-unitˡ x)
      normalize′ = pair-cong (idIso (f ∘ p′)) (comp-unitˡ x′)
      square = paste-squares (productMap-pair f (id C) p x)
        (productMap-pair f (id C) p′ x′) normalize normalize′
        (productMap f (id C) ◁ input) middle output
        (productMap-pair-inner f (id C) σ τ)
        (pair-square (idIso (f ∘ p)) (idIso (f ∘ p′)) (comp-unitˡ x) (comp-unitˡ x′)
          (f ◁ σ) (f ◁ σ) (id C ◁ τ) τ
          (identity-square (f ◁ σ)) (postWhisker-id-at τ))
  in paste-squares (comp-assoc (pair p x) (productMap f (id C)) mapEval)
    (comp-assoc (pair p′ x′) (productMap f (id C)) mapEval)
    (mapEval ◁ (normalize ∙ productMap-pair f (id C) p x))
    (mapEval ◁ (normalize′ ∙ productMap-pair f (id C) p′ x′))
    (mapUncurry f ◁ input) (mapEval ◁ (productMap f (id C) ◁ input))
    (mapEval ◁ output) (postWhisker-comp-at input (productMap f (id C)) mapEval)
    (post-square mapEval (normalize ∙ productMap-pair f (id C) p x)
      (normalize′ ∙ productMap-pair f (id C) p′ x′) (productMap f (id C) ◁ input) output square)

mapUncurry-as-apply-natural : {X C D : CAT} {f g : MAP X (Map C D)}
  (α : f =₁ g)
  → (mapUncurry-as-apply g ∙ mapUncurry-cong α) =₂
      (applyTerm-cong (α ▷ pr₁) (idIso pr₂) ∙ mapUncurry-as-apply f)
mapUncurry-as-apply-natural {f = f} {g} α =
  post-square mapEval (pair-cong (idIso (f ∘ pr₁)) (comp-unitˡ pr₂))
    (pair-cong (idIso (g ∘ pr₁)) (comp-unitˡ pr₂))
    (pair-cong (α ▷ pr₁) (idIso (id _) ▷ pr₂)) (pair-cong (α ▷ pr₁) (idIso pr₂))
    (pair-square (idIso (f ∘ pr₁)) (idIso (g ∘ pr₁)) (comp-unitˡ pr₂) (comp-unitˡ pr₂)
      (α ▷ pr₁) (α ▷ pr₁) (idIso (id _) ▷ pr₂) (idIso pr₂)
      (identity-square (α ▷ pr₁)) (unit-input-square pr₂))

apply-compose-natural : {Γ C D E : CAT}
  {g g′ : MAP Γ (Map D E)} {f f′ : MAP Γ (Map C D)} {x x′ : MAP Γ C}
  (α : g =₁ g′) (β : f =₁ f′) (τ : x =₁ x′)
  → (apply-compose g′ f′ x′ ∙ applyTerm-cong (composeTerm-cong α β) τ) =₂
      (applyTerm-cong α (applyTerm-cong β τ) ∙ apply-compose g f x)
apply-compose-natural {g = g} {g′} {f} {f′} {x} {x′} α β τ =
  let point = pair (pair g f) x
      point′ = pair (pair g′ f′) x′
      changed = pair-cong (pair-cong α β) τ
      first = pair-β₁ g f ∙ coordinate-at pr₁ pr₁ point (pair-β₁ (pair g f) x)
      first′ = pair-β₁ g′ f′ ∙ coordinate-at pr₁ pr₁ point′ (pair-β₁ (pair g′ f′) x′)
      second = pair-β₂ g f ∙ coordinate-at pr₂ pr₁ point (pair-β₁ (pair g f) x)
      second′ = pair-β₂ g′ f′ ∙ coordinate-at pr₂ pr₁ point′ (pair-β₁ (pair g′ f′) x′)
      third = pair-β₂ (pair g f) x
      third′ = pair-β₂ (pair g′ f′) x′
      first-square = paste-squares
        (coordinate-at pr₁ pr₁ point (pair-β₁ (pair g f) x))
        (coordinate-at pr₁ pr₁ point′ (pair-β₁ (pair g′ f′) x′))
        (pair-β₁ g f) (pair-β₁ g′ f′)
        ((pr₁ ∘ pr₁) ◁ changed) (pr₁ ◁ pair-cong α β) α
        (coordinate-at-inner pr₁ pr₁ (pair-β₁ (pair g f) x)
          (pair-β₁ (pair g′ f′) x′) changed (pair-cong α β)
          (pair-cong-triangle₁ (pair-cong α β) τ))
        (pair-cong-triangle₁ α β)
      second-square = paste-squares
        (coordinate-at pr₂ pr₁ point (pair-β₁ (pair g f) x))
        (coordinate-at pr₂ pr₁ point′ (pair-β₁ (pair g′ f′) x′))
        (pair-β₂ g f) (pair-β₂ g′ f′)
        ((pr₂ ∘ pr₁) ◁ changed) (pr₂ ◁ pair-cong α β) β
        (coordinate-at-inner pr₂ pr₁ (pair-β₁ (pair g f) x)
          (pair-β₁ (pair g′ f′) x′) changed (pair-cong α β)
          (pair-cong-triangle₁ (pair-cong α β) τ))
        (pair-cong-triangle₂ α β)
      inner = applyTerm-cong second third ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point
      inner′ = applyTerm-cong second′ third′ ∙ applyTerm-pre (pr₂ ∘ pr₁) pr₂ point′
      inner-square = paste-squares
        (applyTerm-pre (pr₂ ∘ pr₁) pr₂ point) (applyTerm-pre (pr₂ ∘ pr₁) pr₂ point′)
        (applyTerm-cong second third) (applyTerm-cong second′ third′)
        (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed)
        (applyTerm-cong ((pr₂ ∘ pr₁) ◁ changed) (pr₂ ◁ changed))
        (applyTerm-cong β τ)
        (binary-pre-substitution mapEval (pr₂ ∘ pr₁) pr₂ changed)
        (apply-square second second′ third third′ ((pr₂ ∘ pr₁) ◁ changed) β
          (pr₂ ◁ changed) τ second-square (pair-cong-triangle₂ (pair-cong α β) τ))
      outer = applyTerm-cong first inner ∙
        applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point
      outer′ = applyTerm-cong first′ inner′ ∙
        applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point′
      outer-square = paste-squares
        (applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point)
        (applyTerm-pre (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) point′)
        (applyTerm-cong first inner) (applyTerm-cong first′ inner′)
        (doubleEvaluation ◁ changed)
        (applyTerm-cong ((pr₁ ∘ pr₁) ◁ changed) (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed))
        (applyTerm-cong α (applyTerm-cong β τ))
        (binary-pre-substitution mapEval (pr₁ ∘ pr₁) (applyTerm (pr₂ ∘ pr₁) pr₂) changed)
        (apply-square first first′ inner inner′ ((pr₁ ∘ pr₁) ◁ changed) α
          (applyTerm (pr₂ ∘ pr₁) pr₂ ◁ changed) (applyTerm-cong β τ)
          first-square inner-square)
      before = mapUncurry-at mapComp (pair g f) x
      after = mapUncurry-at mapComp (pair g′ f′) x′
      initial = applyTerm-cong (composeTerm-cong α β) τ
      middle = mapUncurry mapComp ◁ changed
      start-square = move-square after middle initial before
        (mapUncurry-at-inner mapComp (pair-cong α β) τ)
      beta-square = paste-squares (before ⁻¹) (after ⁻¹)
        (mapComp-β ▷ point) (mapComp-β ▷ point′)
        initial middle (doubleEvaluation ◁ changed)
        start-square (interchange-at mapComp-β changed)
  in paste-squares ((mapComp-β ▷ point) ∙ before ⁻¹)
    ((mapComp-β ▷ point′) ∙ after ⁻¹) outer outer′ initial
    (doubleEvaluation ◁ changed) (applyTerm-cong α (applyTerm-cong β τ))
    beta-square outer-square

apply-cong-comp : {X C D : CAT}
  {f₀ f₁ f₂ : MAP X (Map C D)} {x₀ x₁ x₂ : MAP X C}
  (α₂ : f₁ =₁ f₂) (α₁ : f₀ =₁ f₁)
  (β₂ : x₁ =₁ x₂) (β₁ : x₀ =₁ x₁)
  → (applyTerm-cong (α₂ ∙ α₁) (β₂ ∙ β₁)) =₂
      (applyTerm-cong α₂ β₂ ∙ applyTerm-cong α₁ β₁)
apply-cong-comp α₂ α₁ β₂ β₁ =
  BinaryFunctorCalculus.binary-cong-comp vocabulary terminal products productLaws composition vertical whiskering
    mapEval α₂ α₁ β₂ β₁

chain-input-squares : {X Y : CAT} {a b c d e f : MAP X Y}
  (u : a =₁ d) (v : b =₁ e) (w : c =₁ f)
  (α : a =₁ b) (β : b =₁ c)
  (γ : d =₁ e) (δ : e =₁ f)
  → (v ∙ α) =₂ (γ ∙ u) → (w ∙ β) =₂ (δ ∙ v)
  → (w ∙ (β ∙ α)) =₂ ((δ ∙ γ) ∙ u)
chain-input-squares u v w α β γ δ p q =
  (isoComp-assoc-at δ γ u) ⁻¹ ∙
    (isoComp-cong (idIso δ) p ∙
      (isoComp-assoc-at δ v α ∙
        (isoComp-cong q (idIso α) ∙ (isoComp-assoc-at w β α) ⁻¹)))

evaluate-compose-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : g =₁ g′) (β : f =₁ f′)
  → (evaluate-compose g′ f′ ∙ mapUncurry-cong (composeTerm-cong α β)) =₂
      (applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂)) ∙
        evaluate-compose g f)
evaluate-compose-natural {g = g} {g′} {f} {f′} α β =
  let κ = composeTerm-cong α β
      initial = mapUncurry-cong κ
      first = applyTerm-cong (κ ▷ pr₁) (idIso pr₂)
      second = applyTerm-cong (composeTerm-cong (α ▷ pr₁) (β ▷ pr₁)) (idIso pr₂)
      third = applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
      u = mapUncurry-as-apply (composeTerm g f)
      u′ = mapUncurry-as-apply (composeTerm g′ f′)
      v = applyTerm-cong (composeTerm-pre g f pr₁) (idIso pr₂)
      v′ = applyTerm-cong (composeTerm-pre g′ f′ pr₁) (idIso pr₂)
      w = apply-compose (g ∘ pr₁) (f ∘ pr₁) pr₂
      w′ = apply-compose (g′ ∘ pr₁) (f′ ∘ pr₁) pr₂
      square = apply-square (composeTerm-pre g f pr₁) (composeTerm-pre g′ f′ pr₁)
        (idIso pr₂) (idIso pr₂) (κ ▷ pr₁) (composeTerm-cong (α ▷ pr₁) (β ▷ pr₁))
        (idIso pr₂) (idIso pr₂) (binary-pre-inputs mapComp α β pr₁)
        (identity-square (idIso pr₂))
  in paste-squares (v ∙ u) (v′ ∙ u′) w w′ initial second third
    (paste-squares u u′ v v′ initial first second (mapUncurry-as-apply-natural κ) square)
    (apply-compose-natural (α ▷ pr₁) (β ▷ pr₁) (idIso pr₂))

mapUncurry-at-fixedParameter : {Γ X C D : CAT} {f g : MAP X (Map C D)}
  (α : f =₁ g) (p : MAP Γ X) {x y : MAP Γ C} (τ : x =₁ y)
  → (mapUncurry-at g p y ∙ (mapUncurry-cong α ⋆ pair-cong (idIso p) τ)) =₂
      (applyTerm-cong (α ▷ p) τ ∙ mapUncurry-at f p x)
mapUncurry-at-fixedParameter {f = f} {g} α p {x} {y} τ =
  let before = mapUncurry-at f p x
      middle = mapUncurry-at f p y
      after = mapUncurry-at g p y
      source-inner = mapUncurry f ◁ pair-cong (idIso p) τ
      source-outer = mapUncurry-cong α ▷ pair p y
      target-inner = applyTerm-cong (idIso (f ∘ p)) τ
      target-outer = applyTerm-cong (α ▷ p) (idIso y)
      normalized-inner = isoComp-cong
        (apply-cong-Iso₂ (postWhisker-idIso f p) (idIso τ)) (idIso before) ∙
        mapUncurry-at-inner f (idIso p) τ
      normalized-target = apply-cong-Iso₂ (isoComp-unitʳ-at (α ▷ p)) (isoComp-unitˡ-at τ) ∙
        (apply-cong-comp (α ▷ p) (idIso (f ∘ p)) (idIso y) τ) ⁻¹
  in isoComp-cong normalized-target (idIso before) ∙
    chain-input-squares before middle after source-inner source-outer target-inner target-outer
      normalized-inner (mapUncurry-at-outer α p y)

uncurry-compose-cong-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : g =₁ g′) (β : f =₁ f′)
  → (uncurry-compose g′ f′ ∙ mapUncurry-cong (composeTerm-cong α β)) =₂
      ((mapUncurry-cong α ⋆ ParameterRetaining.retain-cong P (mapUncurry-cong β)) ∙
        uncurry-compose g f)
uncurry-compose-cong-natural {P = P} {g = g} {g′} {f} {f′} α β =
  let initial = mapUncurry-cong (composeTerm-cong α β)
      first = applyTerm-cong (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
      second = applyTerm-cong (α ▷ pr₁) (mapUncurry-cong β)
      last = mapUncurry-cong α ⋆ ParameterRetaining.retain-cong P (mapUncurry-cong β)
      u = evaluate-compose g f
      u′ = evaluate-compose g′ f′
      v = applyTerm-cong (idIso (g ∘ pr₁)) ((mapUncurry-as-apply f) ⁻¹)
      v′ = applyTerm-cong (idIso (g′ ∘ pr₁)) ((mapUncurry-as-apply f′) ⁻¹)
      w = mapUncurry-at g pr₁ (mapUncurry f)
      w′ = mapUncurry-at g′ pr₁ (mapUncurry f′)
      inner-square = move-square (mapUncurry-as-apply f′) (mapUncurry-cong β)
        (applyTerm-cong (β ▷ pr₁) (idIso pr₂)) (mapUncurry-as-apply f)
        (mapUncurry-as-apply-natural β)
      middle-square = apply-square (idIso (g ∘ pr₁)) (idIso (g′ ∘ pr₁))
        ((mapUncurry-as-apply f) ⁻¹) ((mapUncurry-as-apply f′) ⁻¹)
        (α ▷ pr₁) (α ▷ pr₁) (applyTerm-cong (β ▷ pr₁) (idIso pr₂))
        (mapUncurry-cong β) (identity-square (α ▷ pr₁)) inner-square
      final-square = move-square w′ last second w
        (mapUncurry-at-fixedParameter α pr₁ (mapUncurry-cong β))
  in paste-squares (v ∙ u) (v′ ∙ u′) (w ⁻¹) (w′ ⁻¹) initial second last
    (paste-squares u u′ v v′ initial first second
      (evaluate-compose-natural α β) middle-square) final-square
```

The final statement uses the actual isomorphism functor of the mapping
anima axiom. Its normalization to product action is a proved comparison,
and is inserted on both sides of the square.

```agda
uncurry-compose-natural : {P C D E : CAT}
  {g g′ : MAP P (Map D E)} {f f′ : MAP P (Map C D)}
  (α : g =₁ g′) (β : f =₁ f′)
  → (uncurry-compose g′ f′ ∙ mapUncurryIso (composeTerm-cong α β)) =₂
      ((mapUncurryIso α ⋆ ParameterRetaining.retain-cong P (mapUncurryIso β)) ∙
        uncurry-compose g f)
uncurry-compose-natural {P = P} {g = g} {g′} {f} {f′} α β =
  isoComp-cong
    ((hcomp-cong (mapUncurry-actions-agree α)
      (pair-cong-Iso₂ (idIso (idIso pr₁)) (mapUncurry-actions-agree β))) ⁻¹)
    (idIso (uncurry-compose g f)) ∙
  (uncurry-compose-cong-natural α β ∙
    isoComp-cong (idIso (uncurry-compose g′ f′)) (mapUncurry-actions-agree (composeTerm-cong α β)))
```

