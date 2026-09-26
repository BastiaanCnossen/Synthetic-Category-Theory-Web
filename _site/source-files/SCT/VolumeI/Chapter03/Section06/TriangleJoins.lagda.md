# The two cones on the interval

For `ex:Join_Associative_On_Simplices`, collapse either horizontal side of the square and adjoin the unchanged
side. The resulting pushout span is the span defining the join of a
point and the interval, in the corresponding order. Its universal cocone gives the comparison
with the walking triangle, including the attaching maps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk
import SCT.VolumeI.Chapter02.Section05.Recognition as Recognition
import SCT.VolumeI.Chapter01.Section05.Initial as Initial

import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality
import SCT.VolumeI.Chapter03.Section06.JoinAxiom as JoinsAxiom

module SCT.VolumeI.Chapter03.Section06.TriangleJoins
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E)
  (N : Recognition.RecognitionAxiom 𝒯 M ℱ P I E R)
  (O : Initial.InitialStructure 𝒯 M)
  (B : Coproducts.CoproductStructure 𝒯 M)
  (U : Universality.CoproductUniversality 𝒯 M B P)
  (J : JoinsAxiom.JoinAxiom 𝒯 M ℱ B P U I) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M hiding (_⋆_)
open Coproducts.CoproductStructure B
open Pullbacks.PullbackStructure P
open Walking.WalkingMorphism I using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareRetractions 𝒯 M ℱ P I E Q using ([2])
open import SCT.VolumeI.Chapter01.Section05.CoproductCalculus 𝒯 M B
open import SCT.VolumeI.Chapter01.Section05.CoproductEquivalences 𝒯 M O B using (coproductSwap; coproductSwap-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback-converse; pullback-equivalence)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (Cone)
open import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom 𝒯 M ℱ P I E S using (SubcategoryAxiom)
open import SCT.VolumeI.Chapter03.Section03.Localizations 𝒯 M ℱ P I E S Q R using (module WithSubcategories)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.TriangleCollapsePushouts 𝒯 M ℱ P I E S Q R N using (left-square; right-square; module Collapse)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.CoproductAttachment 𝒯 M ℱ P B using (module Attachment)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.SpanEquivalence 𝒯 M ℱ P using (module Transfer)
open import SCT.VolumeI.Chapter03.Section06.PushoutCalculus.JoinSpanCoordinates 𝒯 M ℱ B P U I J using (insert; module Coordinates)
open import SCT.VolumeI.Chapter03.Section06.Joins 𝒯 M ℱ B P U I J using (_⋆_)

abstract
  terminal-map-isEquiv : IsEquiv (terminate One)
  terminal-map-isEquiv = equiv-transport (terminal-iso (id One) (terminate One)) (id-isEquiv One)

module Triangle (L : SubcategoryAxiom) (Z : WithSubcategories.LocalizationAxiom L) where
  module Collapsed = Collapse L Z using (left-isPushout; right-isPushout)
  module Left where
    cone : Cone (terminate One) (terminate [1]) [1]
    cone = record { left = terminate [1] ; right = id [1] ; match = terminal-iso _ _ }
    abstract
      parameter : MAP [1] (Pullback (terminate One) (terminate [1]))
      parameter = pullbackLift cone
      first-image : (pullback₁ ∘ parameter) =₁ Cone.left cone
      first-image = pullbackLift-β₁ cone
      second-image : (pullback₂ ∘ parameter) =₁ Cone.right cone
      second-image = pullbackLift-β₂ cone
      projection-isEquiv : IsEquiv (pullback₂ {f = terminate One} {terminate [1]})
      projection-isEquiv = degenerate-pullback-converse terminal-map-isEquiv
        (coneSwap (pullbackCone (terminate One) (terminate [1])))
        (pullback-swap (pullbackCone (terminate One) (terminate [1]))
          (pullbackCone-isPullback (terminate One) (terminate [1])))
      parameter-isEquiv : IsEquiv parameter
      parameter-isEquiv = equiv-cancel-left parameter pullback₂ projection-isEquiv
        (equiv-transport ((pullbackLift-β₂ cone) ⁻¹) (id-isEquiv [1]))
    module Coordinates′ = Coordinates (terminate One) (terminate [1]) one-isAn
      parameter parameter-isEquiv (terminate [1]) (id [1]) first-image second-image using (top; bottom; module Compare)
    module Attached = Attachment left-square Collapsed.left-isPushout (insert one) using (top; module Left; cocone; extensions)
    bottom-comparison : Coordinates′.bottom =₁ Attached.Left.sum-map
    bottom-comparison = copair-cong (idIso (in₁ ∘ terminate [1])) (comp-unitʳ in₂)
    module Normalized = Transfer Attached.top Attached.Left.sum-map Coordinates′.top Coordinates′.bottom
      (id ([1] ⊔ [1])) (id ([1] × [1])) (id (One ⊔ [1]))
      ((comp-unitˡ Attached.top) ⁻¹ ∙ comp-unitʳ Coordinates′.top)
      ((comp-unitˡ Attached.Left.sum-map) ⁻¹ ∙ (bottom-comparison ∙ comp-unitʳ Coordinates′.bottom))
      (id-isEquiv ([1] ⊔ [1])) (id-isEquiv ([1] × [1])) (id-isEquiv (One ⊔ [1]))
      Attached.cocone Attached.extensions using (cocone; extensions)
    module Result = Coordinates′.Compare Normalized.cocone Normalized.extensions using (forward; isEquiv; comparison)
    open Result public using () renaming (comparison to attaching-comparison)
    comparison : MAP [2] (One ⋆ [1])
    comparison = Result.forward
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = Result.isEquiv

  module Right where
    cone : Cone (terminate [1]) (terminate One) [1]
    cone = record { left = id [1] ; right = terminate [1] ; match = terminal-iso _ _ }
    abstract
      parameter : MAP [1] (Pullback (terminate [1]) (terminate One))
      parameter = pullbackLift cone
      first-image : (pullback₁ ∘ parameter) =₁ Cone.left cone
      first-image = pullbackLift-β₁ cone
      second-image : (pullback₂ ∘ parameter) =₁ Cone.right cone
      second-image = pullbackLift-β₂ cone
      projection-isEquiv : IsEquiv (pullback₁ {f = terminate [1]} {terminate One})
      projection-isEquiv = pullback-equivalence (terminate [1]) (terminate One) terminal-map-isEquiv
      parameter-isEquiv : IsEquiv parameter
      parameter-isEquiv = equiv-cancel-left parameter pullback₁ projection-isEquiv
        (equiv-transport ((pullbackLift-β₁ cone) ⁻¹) (id-isEquiv [1]))
    module Coordinates′ = Coordinates (terminate [1]) (terminate One) one-isAn
      parameter parameter-isEquiv (id [1]) (terminate [1]) first-image second-image using (top; bottom; module Compare)
    module Attached = Attachment right-square Collapsed.right-isPushout (insert zero) using (top; module Left; cocone; extensions)
    abstract
      top-comparison : (Coordinates′.top ∘ coproductSwap) =₁ (id ([1] × [1]) ∘ Attached.top)
      top-comparison = (comp-unitˡ Attached.top) ⁻¹ ∙
        (copair-cong (copair-β₂ (insert zero) (insert one)) (copair-β₁ (insert zero) (insert one)) ∙
          copair-post in₂ in₁ Coordinates′.top)
      bottom-comparison : (Coordinates′.bottom ∘ coproductSwap) =₁
        (coproductSwap ∘ Attached.Left.sum-map)
      bottom-comparison =
        (copair-cong (copair-pre₁ in₂ in₁ (terminate [1])) (copair-β₂ in₂ in₁) ∙
          copair-post (in₁ ∘ terminate [1]) in₂ coproductSwap) ⁻¹ ∙
        (copair-cong (idIso (in₂ ∘ terminate [1])) (comp-unitʳ in₁) ∙
          (copair-cong (copair-β₂ (in₁ ∘ id [1]) (in₂ ∘ terminate [1]))
            (copair-β₁ (in₁ ∘ id [1]) (in₂ ∘ terminate [1])) ∙
            copair-post in₂ in₁ Coordinates′.bottom))
    module Normalized = Transfer Attached.top Attached.Left.sum-map Coordinates′.top Coordinates′.bottom
      (coproductSwap { [1] } { [1] }) (id ([1] × [1])) (coproductSwap {One} {[1]})
      top-comparison bottom-comparison (coproductSwap-isEquiv [1] [1]) (id-isEquiv ([1] × [1]))
      (coproductSwap-isEquiv One [1]) Attached.cocone Attached.extensions using (cocone; extensions)
    module Result = Coordinates′.Compare Normalized.cocone Normalized.extensions using (forward; isEquiv; comparison)
    open Result public using () renaming (comparison to attaching-comparison)
    comparison : MAP [2] ([1] ⋆ One)
    comparison = Result.forward
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = Result.isEquiv
```
