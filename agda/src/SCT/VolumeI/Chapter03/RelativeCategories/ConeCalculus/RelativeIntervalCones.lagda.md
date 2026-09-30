# Cones associated to relative interval diagrams

A transformation over the composite base map `g ∘ q` gives an interval
cone with constant right leg `q`. Its endpoint identifications are whole
cone comparisons. The right projection is the chosen constant boundary;
its compatibility follows from the relative endpoint triangle and the
composition law for constant boundaries.

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

module SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.RelativeIntervalCones
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter03.RelativeCategories.Morphisms 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P using (FunctorOverIso)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductAssociativity 𝒯 M using (cancel-inverse-tail)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯 using (section-comp)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (cancel-right-reflect)
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismDiagrams as Diagrams
import SCT.VolumeI.Chapter03.RelativeCategories.DiagramMorphisms as Morphisms

module At {C D B Γ : CAT} (f : MAP C B) (g : MAP D B) (q : MAP Γ D)
  {u v : FunctorOver (g ∘ q) f} (α : Over.MorphismOver (g ∘ q) f u v) where
  module Diagram = Diagrams.Diagram 𝒯 M ℱ P I E S α
    using (family; module Source; module Target)
  H = FunctorLift.lift Diagram.family
  ρ = FunctorLift.comparison Diagram.family
  aH = comp-assoc (pr₁ {C = Γ} {D = [1]}) q g
  value : Cone f g (Γ × [1])
  value = record { left = H ; right = q ∘ pr₁ ; match = aH ∙ ρ }
  at-endpoint : FunctorOver (g ∘ q) f → Cone f g Γ
  at-endpoint w = record { left = FunctorLift.lift w ; right = q ; match = FunctorLift.comparison w }
  module Converted = Morphisms.FromDiagram 𝒯 M ℱ P I E S Diagram.family u v
    using (insertion; module Endpoint)

  module Endpoint (z : Obj-abs [1]) (w : FunctorOver (g ∘ q) f)
    (ξ : FunctorOverIso (compose-over Diagram.family (Converted.insertion z)) w) where
    module Old = Converted.Endpoint z w ξ using (boundary; comparison)
    i = insert {X = Γ} z
    af = comp-assoc i H f
    ag = comp-assoc i (q ∘ pr₁) g
    ai = aH ▷ i
    ri = ρ ▷ i
    end = identity-boundary z q
    endBase = identity-boundary z (g ∘ q)
    outer = g ◁ end
    matching = Cone.match (conePre i value)
    τ = FunctorLift.comparison w
    edge = f ◁ Old.boundary

    abstract
      right-normal : ((outer ∙ matching) ∙ af) =₂ (endBase ∙ ri)
      right-normal = isoComp-cong ((section-comp pr₁ i (pair-β₁ _ _) q g) ⁻¹) (idIso ri) ∙
        (isoComp-assoc-at (outer ∙ ag) ai ri ⁻¹ ∙
        (isoComp-assoc-at outer ag (ai ∙ ri) ⁻¹ ∙
        (isoComp-cong (idIso outer)
          (isoComp-cong (idIso ag) (preWhisker-isoComp-at aH ρ i)) ∙
        (isoComp-cong (idIso outer)
          (cancel-inverse-tail (ag ∙ ((aH ∙ ρ) ▷ i)) af ∙
            isoComp-cong (isoComp-assoc-at ag ((aH ∙ ρ) ▷ i) (af ⁻¹) ⁻¹) (idIso af)) ∙
          isoComp-assoc-at outer matching af))))

      compatible : (τ ∙ edge) =₂ (outer ∙ matching)
      compatible = cancel-right-reflect af
        (right-normal ⁻¹ ∙ (Old.comparison ⁻¹ ∙ isoComp-assoc-at τ edge af))

    comparison : ConeIso (conePre i value) (at-endpoint w)
    comparison = record { leftIso = Old.boundary ; rightIso = end ; compatible = compatible }

  module Source = Endpoint zero u Diagram.Source.comparison
  module Target = Endpoint one v Diagram.Target.comparison
```
