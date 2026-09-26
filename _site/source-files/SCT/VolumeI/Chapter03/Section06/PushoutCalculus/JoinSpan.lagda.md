# The span defining a join

The source of the join pushout is the boundary of the interval times
`C ×Γ D`. We put the interval in the second coordinate. Distributivity
constructs the map to `C ⊔ D`; no coproduct structure over a categorical
context is used. The height cocone retains the matching of `C ×Γ D`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Interval

module SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpan
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (I : Interval.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Interval.WalkingMorphism I
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section06.Distributivity 𝒯 M B P U
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 using (Cocone)

∂[1] : CAT
∂[1] = One ⊔ One

boundary : MAP ∂[1] [1]
boundary = copair zero one

module Span {C D Γ : CAT} (p : MAP C Γ) (q : MAP D Γ) where
  W : CAT
  W = Pullback p q

  base : MAP W Γ
  base = p ∘ pullback₁

  private
    module Distribution = Distributivity W One One
    d : MAP ((W × One) ⊔ (W × One)) (W × ∂[1])
    d = Distribution.distribute
    abstract
      d-equiv : IsEquiv d
      d-equiv = Distribution.distribute-isEquiv
    d-inverse : MAP (W × ∂[1]) ((W × One) ⊔ (W × One))
    d-inverse = IsEquiv.inverse d-equiv

  top : MAP (W × ∂[1]) (W × [1])
  top = productMap (id W) boundary

  left-component : MAP (W × One) (C ⊔ D)
  left-component = in₁ ∘ (pullback₁ ∘ pr₁)
  right-component : MAP (W × One) (C ⊔ D)
  right-component = in₂ ∘ (pullback₂ ∘ pr₁)

  distributed-left : MAP ((W × One) ⊔ (W × One)) (C ⊔ D)
  distributed-left = copair left-component right-component

  left : MAP (W × ∂[1]) (C ⊔ D)
  left = distributed-left ∘ d-inverse

  height-left : MAP C (Γ × [1])
  height-left = pair p (const zero)
  height-right : MAP D (Γ × [1])
  height-right = pair q (const one)

  boundary-height : MAP (C ⊔ D) (Γ × [1])
  boundary-height = copair height-left height-right

  cylinder-height : MAP (W × [1]) (Γ × [1])
  cylinder-height = pair (base ∘ pr₁) pr₂

  module Endpoint {A : CAT} (v : MAP A Γ) (s : MAP W A)
    (e : Obj-abs [1]) (i : MAP One ∂[1]) (β : (boundary ∘ i) =₁ e)
    (b : base =₁ (v ∘ s)) where
    insertion : MAP (W × One) (W × ∂[1])
    insertion = productMap (id W) i
    composite : MAP (W × One) (W × [1])
    composite = top ∘ insertion

    first : (pr₁ ∘ composite) =₁ pr₁
    first = comp-unitˡ pr₁ ∙
      ((id W ◁ (comp-unitˡ pr₁ ∙ pair-β₁ (id W ∘ pr₁) (i ∘ pr₂))) ∙
        (comp-assoc insertion pr₁ (id W) ∙
          project-pair₁ (id W ∘ pr₁) (boundary ∘ pr₂) insertion))

    second : (pr₂ ∘ composite) =₁ (e ∘ pr₂)
    second = (β ▷ pr₂) ∙
      ((comp-assoc pr₂ i boundary) ⁻¹ ∙
        ((boundary ◁ pair-β₂ (id W ∘ pr₁) (i ∘ pr₂)) ∙
          (comp-assoc insertion pr₂ boundary ∙
            project-pair₂ (id W ∘ pr₁) (boundary ∘ pr₂) insertion)))

    comparison : (cylinder-height ∘ composite) =₁ (pair v (const e) ∘ (s ∘ pr₁))
    comparison = (pair-pre v (const e) (s ∘ pr₁)) ⁻¹ ∙
      (pair-cong
        (comp-assoc pr₁ s v ∙ ((b ▷ pr₁) ∙
          ((base ◁ first) ∙ comp-assoc composite pr₁ base)))
        (((comp-assoc (s ∘ pr₁) (terminate A) e) ⁻¹) ∙
          ((e ◁ terminal-iso pr₂ (terminate A ∘ (s ∘ pr₁))) ∙ second)) ∙
        pair-pre (base ∘ pr₁) pr₂ composite)

  abstract
    left-distribute : (left ∘ Distribution.distribute) =₁ distributed-left
    left-distribute = comp-unitʳ distributed-left ∙
      ((distributed-left ◁ (IsEquiv.sectionIso d-equiv) ⁻¹) ∙
        comp-assoc d d-inverse distributed-left)

    height-match : (cylinder-height ∘ top) =₁ (boundary-height ∘ left)
    height-match = FunctorLift.lift (preWhisker-lift d d-equiv distributed-comparison)
      where
      first-comparison : ((cylinder-height ∘ top) ∘ productMap (id W) in₁) =₁
        (boundary-height ∘ left-component)
      first-comparison = (copair-pre₁ height-left height-right (pullback₁ ∘ pr₁)) ⁻¹ ∙
        (Endpoint.comparison p pullback₁ zero in₁ (copair-β₁ zero one) (idIso base) ∙
          comp-assoc (productMap (id W) in₁) top cylinder-height)
      second-comparison : ((cylinder-height ∘ top) ∘ productMap (id W) in₂) =₁
        (boundary-height ∘ right-component)
      second-comparison = (copair-pre₂ height-left height-right (pullback₂ ∘ pr₁)) ⁻¹ ∙
        (Endpoint.comparison q pullback₂ one in₂ (copair-β₂ zero one) pullbackMatch ∙
          comp-assoc (productMap (id W) in₂) top cylinder-height)
      cancel-d : (left ∘ d) =₁ distributed-left
      cancel-d = comp-unitʳ distributed-left ∙
        ((distributed-left ◁ (IsEquiv.sectionIso d-equiv) ⁻¹) ∙
          comp-assoc d d-inverse distributed-left)
      distributed-comparison : ((cylinder-height ∘ top) ∘ d) =₁ ((boundary-height ∘ left) ∘ d)
      distributed-comparison = (comp-assoc d left boundary-height) ⁻¹ ∙
        ((boundary-height ◁ cancel-d) ⁻¹ ∙
          ((copair-post left-component right-component boundary-height) ⁻¹ ∙
            (copair-cong first-comparison second-comparison ∙
              copair-post (productMap (id W) in₁) (productMap (id W) in₂) (cylinder-height ∘ top))))

  height-cocone : Cocone top left (Γ × [1])
  height-cocone = record { left = cylinder-height ; right = boundary-height ; match = height-match }

  abstract
    left-isEquiv : IsEquiv (pullback₁ {f = p} {q}) → IsEquiv (pullback₂ {f = p} {q}) → IsEquiv left
    left-isEquiv first second = equiv-compose d-inverse distributed-left (equiv-inverse d-equiv)
      (coproductMap-isEquiv (pullback₁ ∘ pr₁) (pullback₂ ∘ pr₁)
        (equiv-compose pr₁ pullback₁ (product-unitʳ-isEquiv W) first)
        (equiv-compose pr₁ pullback₂ (product-unitʳ-isEquiv W) second))
```
