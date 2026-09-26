# The point-restriction square over a base

Postcompose the retained projection square by the structure functor.
The target triangle is exactly the restriction of the point triangle;
the source triangle is its composite with the product restriction.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PU
import SCT.VolumeI.Chapter03.Section05.Currying.PointRestrictionSquare as PointSquare

module SCT.VolumeI.Chapter03.Section05.Currying.PointRestrictionOverBase
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (change-middle)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (restriction-over)
open PU vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (triangle-whiskered)
module PS = Projections 𝒯

module Over {X A B S : CAT} (z : Obj-abs X) (r : MAP A B) (f : MAP B S) where
  module Square = PointSquare.Square 𝒯 M ℱ P z r
  open Square using (module Source; module Target; R; comparison)
  source : ((f ∘ pr₂) ∘ (R ∘ Source.K)) =₁ (f ∘ r)
  source = PS.lift-base f pr₂ (R ∘ Source.K) Square.w₀
  target : ((f ∘ pr₂) ∘ (Target.K ∘ r)) =₁ (f ∘ r)
  target = (Target.triangle f ▷ r) ∙ (comp-assoc r Target.K (f ∘ pr₂)) ⁻¹
  head : ((f ∘ pr₂) ∘ Target.K) =₁ (f ∘ id B)
  head = PS.lift-base f pr₂ Target.K Target.projection
  tail : ((f ∘ id B) ∘ r) =₁ (f ∘ r)
  tail = PS.lift-base f (id B) r (comp-unitˡ r)
  normalized-target : ((f ∘ pr₂) ∘ (Target.K ∘ r)) =₁ (f ∘ r)
  normalized-target = ((comp-unitʳ f ∙ head) ▷ r) ∙ (comp-assoc r Target.K (f ∘ pr₂)) ⁻¹

  abstract
    target-normalization : target =₂ PS.lift-base f pr₂ (Target.K ∘ r) Square.w₅
    target-normalization = PS.lift-compose f pr₂ Target.K r Target.projection (comp-unitˡ r) ∙
      (isoComp-unitˡ-at (PS.compose-base (f ∘ pr₂) Target.K head r tail) ∙
        (change-middle (f ∘ pr₂) Target.K r head tail
          (comp-unitʳ f) (idIso (f ∘ r)) (idIso (f ∘ r))
          (isoComp-cong (idIso (idIso (f ∘ r))) ((triangle-whiskered r f) ⁻¹)) ∙
          ((isoComp-unitˡ-at normalized-target) ⁻¹ ∙
            isoComp-cong (preWhisker r ◁ Target.normalization f)
              (idIso ((comp-assoc r Target.K (f ∘ pr₂)) ⁻¹)))))

    projection : (target ∙ ((f ∘ pr₂) ◁ comparison)) =₂ source
    projection = PS.lift-square f pr₂ Square.w₀ Square.w₅ comparison Square.projection ∙
      isoComp-cong target-normalization (idIso ((f ∘ pr₂) ◁ comparison))

    source-normalization : source =₂
      PS.compose-base (f ∘ pr₂) R (restriction-over X r f) Source.K
        (PS.lift-base f (r ∘ pr₂) Source.K (Source.triangle r))
    source-normalization = (PS.lift-compose f pr₂ R Source.K Square.br (Source.triangle r)) ⁻¹
```
