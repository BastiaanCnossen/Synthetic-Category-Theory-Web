# Retained identities and change of parameter

The identity comparison between retained evaluations has both product
coordinates. We first check how the chosen comparison from the pair of
projections to the identity behaves under precomposition and
postcomposition. These checks allow the uncurried identity comparison to
be lifted without discarding the parameter coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Substitution.ProofCalculus as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section04.Currying as Currying
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.Substitution.ParameterChange as ParameterChange
import SCT.VolumeI.Chapter01.Section04.Substitution.UncurriedIdentityParameterChange as UncurriedIdentityParameterChange
import SCT.VolumeI.Chapter01.Section04.CompositionCalculus.CompositionNaturality as CompositionNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as PairingCoherence
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PairingNaturality
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductFunctorUnits
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms

module SCT.VolumeI.Chapter01.Section04.Substitution.RetainedIdentityParameterChange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open Setup 𝒯
open Mapping.MappingAnimae M
open Currying 𝒯 M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open ParameterChange 𝒯 M using (retained-parameter-change)
open UncurriedIdentityParameterChange 𝒯 M using (uncurry-identity-parameter-change)
open CompositionNaturality 𝒯 M using (productMap-pair-inner)
open PairingCoherence vocabulary terminal products productLaws composition vertical whiskering
open PairingNaturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-right; project-composite; pre-square-projection;
         pair-pre-natural-inputs; pair-pre-natural-substitution)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (right-unitor-comp; pair-pre-id; triangle-whiskered)
open ProductFunctorUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-projections-triangle₁; pair-projections-triangle₂;
         pair-pre-cong-triangle₁; pair-pre-cong-triangle₂)
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-comp-at; postWhisker-id-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour)

abstract
  combine-pair : {X A B : CAT} {a₀ a₁ a₂ : MAP X A} {b₀ b₁ b₂ : MAP X B}
    {source : MAP X (A × B)}
    (α : a₁ =₁ a₂) (β : b₁ =₁ b₂)
    (γ : a₀ =₁ a₁) (δ : b₀ =₁ b₁) (base : source =₁ (pair a₀ b₀))
    → (pair-cong α β ∙ (pair-cong γ δ ∙ base)) =₂
        (pair-cong (α ∙ γ) (β ∙ δ) ∙ base)
  combine-pair α β γ δ base =
    isoComp-cong ((pair-cong-comp α γ β δ) ⁻¹) (idIso base) ∙
      (isoComp-assoc-at (pair-cong α β) (pair-cong γ δ) base) ⁻¹

  fixed-pair-comp : {X A B : CAT} (f : MAP X A) {g h k : MAP X B}
    (β : h =₁ k) (α : g =₁ h)
    → (pair-cong (idIso f) (β ∙ α)) =₂
        (pair-cong (idIso f) β ∙ pair-cong (idIso f) α)
  fixed-pair-comp f β α = pair-cong-comp (idIso f) (idIso f) β α ∙
    pair-cong-Iso₂ ((isoComp-unitˡ-at (idIso f)) ⁻¹) (idIso (β ∙ α))

  eta-post-coordinate : {X A B : CAT} (π : MAP X A) (F : MAP A B)
    (H : MAP X X) (η : H =₁ (id X)) (b : (π ∘ H) =₁ π)
    → (comp-unitʳ π ∙ (π ◁ η)) =₂ b
    → (comp-unitʳ (F ∘ π) ∙ ((F ∘ π) ◁ η)) =₂
        ((F ◁ b) ∙ comp-assoc H π F)
  eta-post-coordinate π F H η b triangle =
    isoComp-cong (postWhisker F ◁ triangle) (idIso (comp-assoc H π F)) ∙
    (isoComp-cong ((postWhisker-isoComp-at F (comp-unitʳ π) (π ◁ η)) ⁻¹)
        (idIso (comp-assoc H π F)) ∙
    ((isoComp-assoc-at (F ◁ comp-unitʳ π) (F ◁ (π ◁ η)) (comp-assoc H π F)) ⁻¹ ∙
    (isoComp-cong (idIso (F ◁ comp-unitʳ π)) (postWhisker-comp-at η π F) ∙
    (isoComp-assoc-at (F ◁ comp-unitʳ π) (comp-assoc (id _) π F) ((F ∘ π) ◁ η) ∙
      isoComp-cong (right-unitor-comp π F) (idIso ((F ∘ π) ◁ η))))))

  pair-projections-post : {A B C D : CAT} (f : MAP A B) (g : MAP C D)
    → (comp-unitʳ (productMap f g) ∙ (productMap f g ◁ pair-projections)) =₂
        (productMap-pair f g pr₁ pr₂)
  pair-projections-post f g =
    let a = f ∘ pr₁
        b = g ∘ pr₂
        H = pair pr₁ pr₂
        η = pair-projections
        left = comp-unitʳ a
        right = comp-unitʳ b
        first = a ◁ η
        second = b ◁ η
        outer = pair-cong left right
        inner = pair-cong first second
        pre = pair-pre a b H
        normalize = pair-cong-Iso₂
          (eta-post-coordinate pr₁ f H η (pair-β₁ pr₁ pr₂) pair-projections-triangle₁)
          (eta-post-coordinate pr₂ g H η (pair-β₂ pr₁ pr₂) pair-projections-triangle₂)
    in isoComp-cong normalize (idIso pre) ∙
      (isoComp-cong ((pair-cong-comp left first right second) ⁻¹) (idIso pre) ∙
      ((isoComp-assoc-at outer inner pre) ⁻¹ ∙
      (isoComp-cong (idIso outer) ((pair-pre-natural-substitution a b η) ⁻¹) ∙
      (isoComp-assoc-at outer (pair-pre a b (id _)) (productMap f g ◁ η) ∙
        isoComp-cong ((pair-pre-id a b) ⁻¹) (idIso (productMap f g ◁ η))))))

  eta-pre-coordinate : {R X C : CAT} (π : MAP X C) (s : MAP R X)
    (H : MAP X X) (η : H =₁ (id X)) (b : (π ∘ H) =₁ π)
    → (comp-unitʳ π ∙ (π ◁ η)) =₂ b
    → (π ◁ (comp-unitˡ s ∙ (η ▷ s))) =₂
        ((b ▷ s) ∙ (comp-assoc s H π) ⁻¹)
  eta-pre-coordinate π s H η b triangle =
    let A = comp-assoc s (id _) π
        triangle-solved = (cancel-right A (π ◁ comp-unitˡ s) ∙
          isoComp-cong (triangle-whiskered s π) (idIso (A ⁻¹))) ⁻¹
        square = pre-square-projection π η (idIso π) b (comp-unitʳ π) s
          ((isoComp-unitˡ-at b) ⁻¹ ∙ triangle)
        tail = (b ▷ s) ∙ (comp-assoc s H π) ⁻¹
    in isoComp-unitˡ-at tail ∙
      (isoComp-cong (preWhisker-idIso π s) (idIso tail) ∙
      (square ∙
      (isoComp-cong triangle-solved (idIso (π ◁ (η ▷ s))) ∙
        postWhisker-isoComp-at π (comp-unitˡ s) (η ▷ s))))

  pair-projections-pre : {X A B : CAT} (f : MAP X A) (g : MAP X B)
    → let s = pair f g
      in (comp-unitˡ s ∙ (pair-projections ▷ s)) =₂
        (pair-cong (pair-β₁ f g) (pair-β₂ f g) ∙ pair-pre pr₁ pr₂ s)
  pair-projections-pre f g =
    let s = pair f g
        first = pair-β₁ f g
        second = pair-β₂ f g
    in pair-iso-extensionality
      (cancel-left-reflect first
        ((pair-pre-cong-triangle₁ pr₁ pr₂ s first second) ⁻¹ ∙
          isoComp-cong (idIso first)
            (eta-pre-coordinate pr₁ s (pair pr₁ pr₂) pair-projections
              (pair-β₁ pr₁ pr₂) pair-projections-triangle₁)))
      (cancel-left-reflect second
        ((pair-pre-cong-triangle₂ pr₁ pr₂ s first second) ⁻¹ ∙
          isoComp-cong (idIso second)
            (eta-pre-coordinate pr₂ s (pair pr₁ pr₂) pair-projections
              (pair-β₂ pr₁ pr₂) pair-projections-triangle₂)))

  post-retained-identity : {P Q C : CAT} (σ : MAP Q P) {x : MAP (Q × C) C}
    (u : x =₁ pr₂)
    → let s = productMap σ (id C)
      in (comp-unitʳ s ∙ (s ◁ (pair-projections ∙ pair-cong (idIso pr₁) u))) =₂
        (pair-cong (idIso (σ ∘ pr₁)) (id C ◁ u) ∙ productMap-pair σ (id C) pr₁ x)
  post-retained-identity {C = C} σ {x} u =
    let s = productMap σ (id C)
        η = pair-projections
        r = pair-cong (idIso pr₁) u
    in isoComp-cong (pair-cong-Iso₂ (postWhisker-idIso σ pr₁) (idIso (id C ◁ u)))
        (idIso (productMap-pair σ (id C) pr₁ x)) ∙
      (productMap-pair-inner σ (id C) (idIso pr₁) u ∙
      (isoComp-cong (pair-projections-post σ (id C)) (idIso (s ◁ r)) ∙
      ((isoComp-assoc-at (comp-unitʳ s) (s ◁ η) (s ◁ r)) ⁻¹ ∙
        isoComp-cong (idIso (comp-unitʳ s)) (postWhisker-isoComp-at s η r))))

  pre-retained-identity : {X P C : CAT} (f : MAP X P) (g : MAP X C)
    {z : MAP (P × C) C} (u : z =₁ pr₂)
    → let s = pair f g
      in (comp-unitˡ s ∙ ((pair-projections ∙ pair-cong (idIso pr₁) u) ▷ s)) =₂
        (pair-cong (pair-β₁ f g) (pair-β₂ f g ∙ (u ▷ s)) ∙ pair-pre pr₁ z s)
  pre-retained-identity f g {z} u =
    let s = pair f g
        η = pair-projections
        r = pair-cong (idIso pr₁) u
        first = pair-β₁ f g
        second = pair-β₂ f g
        out = pair-cong first second
        pre = pair-pre pr₁ pr₂ s
        normalize = isoComp-unitʳ-at first ∙
          isoComp-cong (idIso first) (preWhisker-idIso pr₁ s)
    in isoComp-cong (pair-cong-Iso₂ normalize (idIso (second ∙ (u ▷ s))))
        (idIso (pair-pre pr₁ z s)) ∙
      (combine-pair first second (idIso pr₁ ▷ s) (u ▷ s) (pair-pre pr₁ z s) ∙
      (isoComp-cong (idIso out) ((pair-pre-natural-inputs (idIso pr₁) u s) ⁻¹) ∙
      (isoComp-assoc-at out pre (r ▷ s) ∙
      (isoComp-cong (pair-projections-pre f g) (idIso (r ▷ s)) ∙
      ((isoComp-assoc-at (comp-unitˡ s) (η ▷ s) (r ▷ s)) ⁻¹ ∙
        isoComp-cong (idIso (comp-unitˡ s)) (preWhisker-isoComp-at η r s))))))

  identity-action-from-square : {X C : CAT} {x y : MAP X C}
    (θ : x =₁ y) (γ : x =₁ (id C ∘ y))
    → θ =₂ (comp-unitˡ y ∙ γ)
    → (id C ◁ θ) =₂ (γ ∙ comp-unitˡ x)
  identity-action-from-square {x = x} {y} θ γ square =
    cancel-left-reflect (comp-unitˡ y)
      (isoComp-assoc-at (comp-unitˡ y) γ (comp-unitˡ x) ∙
      (isoComp-cong square (idIso (comp-unitˡ x)) ∙ postWhisker-id-at θ))
```

We now normalize both routes to the same pair of coordinates. The only
input beyond the preceding product calculations is the stated uncurried
identity square. Thus this lemma identifies precisely what that square
must supply before the retained unit route can be used.

```agda
module IdentitySquare {P Q C : CAT} (σ : MAP Q P) where
  module RP = RetainedEvaluation P
  module RQ = RetainedEvaluation Q

  J = identityTerm {Γ = P} C
  s = productMap σ (id C)
  δ = const-pre (mapId C) σ
  x = mapUncurry (J ∘ σ)
  y = mapUncurry (identityTerm {Γ = Q} C)
  z = mapUncurry J
  deltaImage = mapUncurryIso δ
  p = uncurry-identity P C
  q = uncurry-identity Q C
  v = mapUncurry-restrict J σ
  b₁ = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
  b₂ = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
  b = comp-unitˡ pr₂ ∙ b₂

  Hypothesis : Set m
  Hypothesis = (q ∙ deltaImage) =₂ (b ∙ ((p ▷ s) ∙ v))

  left : (s ∘ RQ.retained (J ∘ σ)) =₁ s
  left = comp-unitʳ s ∙ ((s ◁ RQ.retained-identity C) ∙ (s ◁ RQ.retainedIso δ))

  right : (s ∘ RQ.retained (J ∘ σ)) =₁ s
  right = comp-unitˡ s ∙ ((RP.retained-identity C ▷ s) ∙ retained-parameter-change J σ)

  base = productMap-pair σ (id C) pr₁ x
  input = pair-cong (idIso (σ ∘ pr₁)) (v ∙ comp-unitˡ x) ∙ base
  output = pair-cong b₁ (idIso (z ∘ s)) ∙ pair-pre pr₁ z s
  finish = pair-cong (idIso (σ ∘ pr₁)) (b₂ ∙ (p ▷ s))

  abstract
    left-normalization : left =₂
      (pair-cong (idIso (σ ∘ pr₁)) (id C ◁ (q ∙ deltaImage)) ∙ base)
    left-normalization =
      let η = pair-projections
          rq = pair-cong (idIso pr₁) q
          ra = pair-cong (idIso pr₁) deltaImage
          merge = isoComp-cong (idIso η) ((fixed-pair-comp pr₁ q deltaImage) ⁻¹) ∙
            isoComp-assoc-at η rq ra
      in post-retained-identity σ (q ∙ deltaImage) ∙
        (isoComp-cong (idIso (comp-unitʳ s)) (postWhisker s ◁ merge) ∙
          isoComp-cong (idIso (comp-unitʳ s))
            ((postWhisker-isoComp-at s (RQ.retained-identity C) (RQ.retainedIso δ)) ⁻¹))

    output-normalization :
      (comp-unitˡ s ∙ (RP.retained-identity C ▷ s)) =₂ (finish ∙ output)
    output-normalization =
      let normalize = pair-cong-Iso₂ (isoComp-unitˡ-at b₁) (isoComp-unitʳ-at (b₂ ∙ (p ▷ s)))
      in (combine-pair (idIso (σ ∘ pr₁)) (b₂ ∙ (p ▷ s)) b₁
          (idIso (z ∘ s)) (pair-pre pr₁ z s)) ⁻¹ ∙
        (isoComp-cong (normalize ⁻¹) (idIso (pair-pre pr₁ z s)) ∙
          pre-retained-identity (σ ∘ pr₁) (id C ∘ pr₂) p)

    right-normalization : right =₂
      (pair-cong (idIso (σ ∘ pr₁)) ((b₂ ∙ (p ▷ s)) ∙ (v ∙ comp-unitˡ x)) ∙ base)
    right-normalization =
      let cancel = isoComp-unitˡ-at input ∙
            isoComp-cong (isoComp-inverseʳ-at output) (idIso input)
          clear = isoComp-cong (idIso finish) cancel ∙
            reassociateFour finish output (output ⁻¹) input
          first-normal = isoComp-unitˡ-at (idIso (σ ∘ pr₁))
      in isoComp-cong (pair-cong-Iso₂ first-normal
          (idIso ((b₂ ∙ (p ▷ s)) ∙ (v ∙ comp-unitˡ x)))) (idIso base) ∙
        (combine-pair (idIso (σ ∘ pr₁)) (b₂ ∙ (p ▷ s))
          (idIso (σ ∘ pr₁)) (v ∙ comp-unitˡ x) base ∙
        (clear ∙
        (isoComp-cong output-normalization (idIso (output ⁻¹ ∙ input)) ∙
          (isoComp-assoc-at (comp-unitˡ s) (RP.retained-identity C ▷ s)
            (output ⁻¹ ∙ input)) ⁻¹)))

    from-uncurried : Hypothesis → left =₂ right
    from-uncurried coherence =
      let θ = q ∙ deltaImage
          γ = (b₂ ∙ (p ▷ s)) ∙ v
          square = reassociateFour (comp-unitˡ pr₂) b₂ (p ▷ s) v ∙ coherence
          second = isoComp-assoc-at (b₂ ∙ (p ▷ s)) v (comp-unitˡ x) ∙
            identity-action-from-square θ γ square
      in right-normalization ⁻¹ ∙
        (isoComp-cong (pair-cong-Iso₂ (idIso (idIso (σ ∘ pr₁))) second) (idIso base) ∙
          left-normalization)
```

The uncurried identity square is already proved. Substituting that proof
gives the unconditional retained identity comparison with the original
choices of identity and parameter-change maps.

```agda
retained-identity-parameter-change : {P Q C : CAT} (σ : MAP Q P)
  → (IdentitySquare.left {C = C} σ) =₂ (IdentitySquare.right {C = C} σ)
retained-identity-parameter-change σ =
  IdentitySquare.from-uncurried σ (uncurry-identity-parameter-change σ)
```
