# Recovery after currying a transformation

The opposite recovery comparison is proved separately. The coordinate
exchange is an equivalence, so the iterated evaluation comparison lifts
back to the original diagram. Its retained image and the two endpoint
triangles verify the required endpoint conditions.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingCurryingRecovery
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.UncurryingDiagramEndpoints as Normalization
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingExpressions as Currying
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurryingEndpointImages as Images
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CurriedRestrictionFrames as Frames
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramExpressionIdentifications as Diagrams
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-compose; expressionIso-inverse)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointNaturality 𝒯 M ℱ
  using (application-natural)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.NestedSymmetry as Symmetry
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)

module At {Γ X C : CAT} (f g : MAP Γ (Fun X C))
  (α : MorphismExpression (funUncurry f) (funUncurry g)) where
  module A = Currying.Curry 𝒯 M ℱ I f g α
    using (arrow; diagram; first-curry; original; permutation; value; module Endpoint)
  module Original = MorphismExpression α
    using (arrow; source-frame; target-frame)
  module N = Normalization.At 𝒯 M ℱ P I E A.value
  module Recovered = Diagrams.Recovery 𝒯 M ℱ P I E N.uncurried
    using (comparison; p; q)
  module OriginalRecovery = Diagrams.Recovery 𝒯 M ℱ P I E α
    using (comparison; p; q)
  β₁ : funUncurry A.arrow =₁ A.first-curry
  β₁ = funCurry-β A.first-curry
  β₂ : funUncurry A.first-curry =₁ A.diagram
  β₂ = funCurry-β A.diagram
  ε : (N.original ∘ A.permutation) =₁ (A.original ∘ A.permutation)
  ε = β₂ ∙ (funUncurryIso β₁ ∙ N.comparison)

  abstract
    lifted : FunctorLift (preWhisker A.permutation) ε
    lifted = preWhisker-lift A.permutation (Symmetry.exchange-isEquiv 𝒯 Γ [1] X) ε
    comparison : N.original =₁ A.original
    comparison = FunctorLift.lift lifted
    comparison-image : (comparison ▷ A.permutation) =₂ ε
    comparison-image = FunctorLift.comparison lifted

  module Endpoint (z : Obj-abs [1]) (h : MAP Γ (Fun X C))
    (a : (evaluate z ∘ Original.arrow) =₁ funUncurry h)
    (b : (evaluate z ∘ N.B.arrow) =₁ funUncurry h) where
    module AE = A.Endpoint z h a
      using (comparison; insertion-comparison; reflected)
    module NE = N.Endpoint z AE.comparison (b ∙ (evaluate-uncurry z N.B.arrow) ⁻¹)
      using (R)
    module Image = Images.At.Endpoint 𝒯 M ℱ I f g α z h a
    module Frame = Frames.At 𝒯 M ℱ I A.first-curry z AE.reflected
      using (comparison)
    i = insert {X = Γ} z
    j = insert {X = Γ × X} z
    s = productMap i (id X)
    κ = AE.insertion-comparison
    front : (A.original ∘ j) =₁ funUncurry h
    front = a ∙ (evaluate-uncurry z Original.arrow) ⁻¹
    target-front : (N.original ∘ j) =₁ funUncurry h
    target-front = b ∙ (evaluate-uncurry z N.B.arrow) ⁻¹
    before : ((N.original ∘ A.permutation) ∘ s) =₁ (N.original ∘ j)
    before = (N.original ◁ κ) ∙ comp-assoc s A.permutation N.original
    after : ((A.original ∘ A.permutation) ∘ s) =₁ (A.original ∘ j)
    after = (A.original ◁ κ) ∙ comp-assoc s A.permutation A.original
    short : ((A.original ∘ A.permutation) ∘ s) =₁ funUncurry h
    short = front ∙ after
    B = β₂ ▷ s
    U = funUncurryIso β₁ ▷ s
    V = N.comparison ▷ s

    abstract
      frame-normalization : NE.R =₂ ((short ∙ B) ∙ U)
      frame-normalization = isoComp-cong Image.comparison (idIso U) ∙ Frame.comparison

      before-normalization : (short ∙ (ε ▷ s)) =₂ (NE.R ∙ V)
      before-normalization = isoComp-cong (frame-normalization ⁻¹) (idIso V) ∙
        (isoComp-assoc-at (short ∙ B) U V) ⁻¹ ∙
        (isoComp-assoc-at short B (U ∙ V)) ⁻¹ ∙
        isoComp-cong (idIso short)
          (isoComp-cong (idIso B) (preWhisker-isoComp-at (funUncurryIso β₁) N.comparison s)) ∙
        isoComp-cong (idIso short) (preWhisker-isoComp-at β₂ (funUncurryIso β₁ ∙ N.comparison) s)

      compatible : (NE.R ∙ V) =₂ (target-front ∙ before) →
        (front ∙ (comparison ▷ j)) =₂ target-front
      compatible same = cancel-right-reflect before
        (same ∙ before-normalization ∙
          isoComp-cong (idIso short) (preWhisker s ◁ comparison-image) ∙
          (isoComp-assoc-at front after ((comparison ▷ A.permutation) ▷ s)) ⁻¹ ∙
          isoComp-cong (idIso front)
            ((application-natural A.permutation s κ comparison) ⁻¹) ∙
          isoComp-assoc-at front (comparison ▷ j) before)

  module Source = Endpoint zero f Original.source-frame N.B.source-frame
    using (compatible)
  module Target = Endpoint one g Original.target-frame N.B.target-frame
  diagram-comparison = Diagrams.At.comparison 𝒯 M ℱ P I E N.original A.original comparison
    Recovered.p Recovered.q OriginalRecovery.p OriginalRecovery.q
    (Source.compatible N.source-compatible) (Target.compatible N.target-compatible)

  value : ExpressionIso N.uncurried α
  value = expressionIso-compose (expressionIso-inverse OriginalRecovery.comparison)
    (expressionIso-compose diagram-comparison Recovered.comparison)
```
