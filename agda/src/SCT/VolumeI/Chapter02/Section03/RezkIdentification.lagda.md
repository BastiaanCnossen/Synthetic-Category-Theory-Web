# Recovering a primitive identification

Lift an arrow to `Iso C`, then apply the inverse of the Rezk equivalence.
This gives an object `z` whose identity arrow is identified with the
given arrow. Its endpoint comparisons give `z = x` and `z = y`, hence
`x = y`. This is the argument of
`cor:Invertible_Morphisms_Induce_Isomorphisms`, with the lift supplied
explicitly.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section03.RezkIdentification
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open Rezk 𝒯 M ℱ P I E public
open RezkAxiom R
open import SCT.VolumeI.Chapter02.Section03.InverseTriangleLift 𝒯 M ℱ P I E using (invertible-lift)
open import SCT.VolumeI.Chapter02.Section03.ConstantArrows 𝒯 M ℱ I using (constant-frame)

module Identify {Γ C : CAT} {x y : MAP Γ C}
  (f : MorphismExpression x y) (w : IsoLift (MorphismExpression.arrow f)) where
  module F = MorphismExpression f
  module W = IsoLift w
  chosen = equiv-lift (rezk-isEquiv C) W.lift

  center : MAP Γ C
  center = FunctorLift.lift chosen

  constant-comparison : (identityArrow ∘ center) =₁ F.arrow
  constant-comparison = W.comparison ∙
    ((isoArrow ◁ FunctorLift.comparison chosen) ∙
      (comp-assoc center identityIso isoArrow ∙ (identityIso-arrow ⁻¹ ▷ center)))

  endpoint : (v : Obj-abs [1]) →
    (evaluate v ∘ identityArrow) =₁ (id C) →
    (evaluate v ∘ F.arrow) =₁ center
  endpoint v β = comp-unitˡ center ∙
    ((β ▷ center) ∙
      ((comp-assoc center identityArrow (evaluate v)) ⁻¹ ∙
        (evaluate v ◁ constant-comparison ⁻¹)))

  source-identification : center =₁ x
  source-identification = F.source-frame ∙
    ((ev₀ ◁ constant-comparison) ∙ (constant-frame ev₀ identity-source center) ⁻¹)

  target-identification : center =₁ y
  target-identification = F.target-frame ∙
    ((ev₁ ◁ constant-comparison) ∙ (constant-frame ev₁ identity-target center) ⁻¹)

  identification : x =₁ y
  identification = target-identification ∙ source-identification ⁻¹

lifted-morphism-identification : {C : CAT} {x y : Obj-abs C}
  (f : Morphism x y) → IsoLift (nameFun (Morphism.diagram f)) → x =₁ y
lifted-morphism-identification f w = Identify.identification
  (record
    { arrow = nameFun (Morphism.diagram f)
    ; source-frame = Morphism.source-identification f ∙ evaluate-name zero (Morphism.diagram f)
    ; target-frame = Morphism.target-identification f ∙ evaluate-name one (Morphism.diagram f) }) w

invertible-morphism-identification : {C : CAT} {x y : Obj-abs C}
  (f : Morphism x y) → IsInvertible f → x =₁ y
invertible-morphism-identification f w = lifted-morphism-identification f (invertible-lift f w)
```
