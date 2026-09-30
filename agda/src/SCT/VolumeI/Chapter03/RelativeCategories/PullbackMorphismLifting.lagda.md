# Lifting a relative interval diagram through a pullback

A whole cone at every endpoint gives a morphism in the pullback. When
its right leg is constant in the interval and the endpoint comparisons
have the stated right-leg computations, the lifted morphism lies over
the base. The arbitrary comparison of the chosen pullback factor cancels
through the projection computation; it is not assumed to be normalized.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter03.RelativeCategories.PullbackMorphismLifting
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PullbackDiagramLifting as Lifting
import SCT.VolumeI.Chapter03.RelativeCategories.DiagramMorphisms as Diagrams

module At {C D B T Γ : CAT} {f : MAP C B} {g : MAP D B}
  (t : Cone f g T) (et : IsPullback t) (q : MAP Γ D)
  (H : MAP (Γ × [1]) C) (δ : (f ∘ H) =₁ (g ∘ (q ∘ pr₁))) where
  L : Cone f g (Γ × [1])
  L = record { left = H ; right = q ∘ pr₁ ; match = δ }
  module Lift = Lifting.At 𝒯 M ℱ P I E t et L
    using (H; β; module Endpoint; module WithEndpoints)
  p = Cone.right t
  family : FunctorOver (q ∘ pr₁ {C = Γ} {D = [1]}) p
  family = record { lift = Lift.H ; comparison = ConeIso.rightIso Lift.β }
  insertion : (z : Obj-abs [1]) → FunctorOver q (q ∘ pr₁ {C = Γ} {D = [1]})
  insertion z = record { lift = insert z ; comparison = identity-boundary z q }

  module Endpoint (z : Obj-abs [1]) (u : FunctorOver q p)
    (Φ : ConeIso (conePre (insert z) L) (conePre (FunctorLift.lift u) t))
    (χ : (FunctorLift.comparison u ∙ ConeIso.rightIso Φ) =₂ identity-boundary z q) where
    module Found = Lift.Endpoint z (FunctorLift.lift u) Φ using (value; right-frame)
    i = insert {X = Γ} z
    edge = p ◁ Found.value
    ass = comp-assoc i Lift.H p
    b = ConeIso.rightIso Lift.β ▷ i
    r = ConeIso.rightIso Φ
    τ = FunctorLift.comparison u
    end = identity-boundary z q

    abstract
      cancellation : ((end ∙ (b ∙ ass ⁻¹)) ∙ ass) =₂ (end ∙ b)
      cancellation = cancel-inverse-tail (end ∙ b) ass ∙
        isoComp-cong (isoComp-assoc-at end b (ass ⁻¹) ⁻¹) (idIso ass)

      compatible : (τ ∙ edge) =₂ FunctorLift.comparison (compose-over family (insertion z))
      compatible = cancel-right-reflect ass
        (cancellation ⁻¹ ∙
        (isoComp-cong χ (idIso b) ∙
        (isoComp-assoc-at τ r b ⁻¹ ∙
        (isoComp-cong (idIso τ) Found.right-frame ∙ isoComp-assoc-at τ edge ass))))

    value : FunctorOverIso (compose-over family (insertion z)) u
    value = record { underlying = Found.value ; compatible = compatible }

  module WithEndpoints (u v : FunctorOver q p)
    (source : ConeIso (conePre (insert zero) L) (conePre (FunctorLift.lift u) t))
    (target : ConeIso (conePre (insert one) L) (conePre (FunctorLift.lift v) t))
    (source-right : (FunctorLift.comparison u ∙ ConeIso.rightIso source) =₂ identity-boundary zero q)
    (target-right : (FunctorLift.comparison v ∙ ConeIso.rightIso target) =₂ identity-boundary one q) where
    module Source = Endpoint zero u source source-right using (value)
    module Target = Endpoint one v target target-right using (value)
    module Raw = Lift.WithEndpoints (FunctorLift.lift u) (FunctorLift.lift v) source target
      using (value; left; right; left-image; right-image)
    module Relative = Diagrams.FromDiagram.WithEndpoints 𝒯 M ℱ P I E S family u v Source.value Target.value
      using (over-base)

    underlying : MorphismExpression (FunctorLift.lift u) (FunctorLift.lift v)
    underlying = Raw.value
    over-base : Over.IsOver q p u v underlying
    over-base = Relative.over-base
    value : Over.MorphismOver q p u v
    value = record { underlying = underlying ; over-base = over-base }
    left-image : ExpressionIso (post-expression (Cone.left t) underlying) Raw.left
    left-image = Raw.left-image
    right-image : ExpressionIso (post-expression p underlying) Raw.right
    right-image = Raw.right-image
```
