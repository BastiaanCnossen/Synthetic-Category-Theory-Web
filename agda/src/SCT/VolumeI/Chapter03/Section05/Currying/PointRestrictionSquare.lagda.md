# Restriction commutes with inserting a point

Insert the point in the first coordinate and restrict the second
coordinate. Product separation and the terminal-product comparison
identify the two orders. The second-projection calculation is retained
so the comparison can be used in triangles over a base.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Decoding.UnitRestrictionData as Unit
import SCT.VolumeI.Chapter03.Section05.Currying.PointParameterProjection as Points

module SCT.VolumeI.Chapter03.Section05.Currying.PointRestrictionSquare
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.ProductSquares 𝒯
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M
  using (parameter-base; restriction-base; separation)
open import SCT.VolumeI.Chapter01.Section04.Substitution.DecodingNaturality 𝒯 M using (oneProduct-natural)
module PS = Projections 𝒯

module Square {X A B : CAT} (z : Obj-abs X) (r : MAP A B) where
  module Source = Points.Point 𝒯 M ℱ P {A = A} z
  module Target = Points.Point 𝒯 M ℱ P {A = B} z
  module Terminal = Unit.Coordinates 𝒯 M r
  R : MAP (X × A) (X × B)
  R = productRestriction X r
  R₀ : MAP (One × A) (One × B)
  R₀ = productRestriction One r
  br : (pr₂ ∘ R) =₁ (r ∘ pr₂)
  br = restriction-base X r
  br₀ : (pr₂ ∘ R₀) =₁ (r ∘ pr₂)
  br₀ = restriction-base One r
  bA : (pr₂ ∘ Source.H) =₁ pr₂
  bA = parameter-base z A
  bB : (pr₂ ∘ Target.H) =₁ pr₂
  bB = parameter-base z B
  bAr : ((r ∘ pr₂) ∘ Source.H) =₁ (r ∘ pr₂)
  bAr = PS.lift-base r pr₂ Source.H bA
  e₀ : ((r ∘ pr₂) ∘ Source.i) =₁ r
  e₀ = Terminal.endpoint

  w₀ : (pr₂ ∘ (R ∘ Source.K)) =₁ r
  w₀ = PS.compose-base pr₂ R br Source.K (Source.triangle r)
  b₁ : (pr₂ ∘ (R ∘ Source.H)) =₁ (r ∘ pr₂)
  b₁ = PS.compose-base pr₂ R br Source.H bAr
  w₁ : (pr₂ ∘ ((R ∘ Source.H) ∘ Source.i)) =₁ r
  w₁ = PS.compose-base pr₂ (R ∘ Source.H) b₁ Source.i e₀
  b₂ : (pr₂ ∘ (Target.H ∘ R₀)) =₁ (r ∘ pr₂)
  b₂ = PS.compose-base pr₂ Target.H bB R₀ br₀
  w₂ : (pr₂ ∘ ((Target.H ∘ R₀) ∘ Source.i)) =₁ r
  w₂ = PS.compose-base pr₂ (Target.H ∘ R₀) b₂ Source.i e₀
  w₃ : (pr₂ ∘ (Target.H ∘ (R₀ ∘ Source.i))) =₁ r
  w₃ = PS.compose-base pr₂ Target.H bB (R₀ ∘ Source.i) Terminal.source
  w₄ : (pr₂ ∘ (Target.H ∘ (Target.i ∘ r))) =₁ r
  w₄ = PS.compose-base pr₂ Target.H bB (Target.i ∘ r) Terminal.target
  w₅ : (pr₂ ∘ (Target.K ∘ r)) =₁ r
  w₅ = PS.compose-base pr₂ Target.K Target.projection r (comp-unitˡ r)

  η₁ : (R ∘ Source.K) =₁ ((R ∘ Source.H) ∘ Source.i)
  η₁ = (comp-assoc Source.i Source.H R) ⁻¹
  η₂ : ((R ∘ Source.H) ∘ Source.i) =₁ ((Target.H ∘ R₀) ∘ Source.i)
  η₂ = productMap-separate z r ▷ Source.i
  η₃ : ((Target.H ∘ R₀) ∘ Source.i) =₁ (Target.H ∘ (R₀ ∘ Source.i))
  η₃ = comp-assoc Source.i R₀ Target.H
  η₄ : (Target.H ∘ (R₀ ∘ Source.i)) =₁ (Target.H ∘ (Target.i ∘ r))
  η₄ = Target.H ◁ oneProduct-natural r
  η₅ : (Target.H ∘ (Target.i ∘ r)) =₁ (Target.K ∘ r)
  η₅ = (comp-assoc r Target.i Target.H) ⁻¹
  comparison : (R ∘ Source.K) =₁ (Target.K ∘ r)
  comparison = η₅ ∙ (η₄ ∙ (η₃ ∙ (η₂ ∙ η₁)))

  abstract
    first : PS.Square pr₂ w₀ w₁ η₁
    first = PS.inverse-square pr₂ w₁ w₀ (comp-assoc Source.i Source.H R)
      (PS.associator-square pr₂ R Source.H Source.i br bAr e₀)
    second : PS.Square pr₂ w₁ w₂ η₂
    second = PS.pre-square pr₂ Source.i b₁ b₂ e₀ (productMap-separate z r) (separation z r)
    third : PS.Square pr₂ w₂ w₃ η₃
    third = PS.associator-square pr₂ Target.H R₀ Source.i bB br₀ e₀
    fourth : PS.Square pr₂ w₃ w₄ η₄
    fourth = PS.post-square pr₂ Target.H bB Terminal.source Terminal.target
      (oneProduct-natural r) Terminal.projection₂
    fifth : PS.Square pr₂ w₄ w₅ η₅
    fifth = PS.inverse-square pr₂ w₅ w₄ (comp-assoc r Target.i Target.H)
      (PS.associator-square pr₂ Target.H Target.i r bB (oneProduct-retraction B) (comp-unitˡ r))

    projection : PS.Square pr₂ w₀ w₅ comparison
    projection = PS.compose-square pr₂ w₀ w₄ w₅ η₅ (η₄ ∙ (η₃ ∙ (η₂ ∙ η₁))) fifth
      (PS.compose-square pr₂ w₀ w₃ w₄ η₄ (η₃ ∙ (η₂ ∙ η₁)) fourth
        (PS.compose-square pr₂ w₀ w₂ w₃ η₃ (η₂ ∙ η₁) third
          (PS.compose-square pr₂ w₀ w₁ w₂ η₂ η₁ second first)))
```
