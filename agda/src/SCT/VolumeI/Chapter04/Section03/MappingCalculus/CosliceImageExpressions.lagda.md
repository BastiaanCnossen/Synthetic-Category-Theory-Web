# The framed-arrow computation of a coslice functor

The usual functor on coslices sends their universal arrow to its image.
We obtain this statement from its whole source-endpoint computation.
Both endpoint frames and the resulting target-projection comparison are
retained, with no appeal to pointwise uniqueness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceImageExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter04.Section03.MappingCalculus.EndpointSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (Cone; ConeIso; conePre; coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I using (post-boundary-normal)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)
import SCT.VolumeI.Chapter04.Section03.CosliceFunctors as Functors
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.CosliceExpressions as Reading
import SCT.VolumeI.Chapter04.Section03.MappingCalculus.SourceConeExpressions as Decoding
import SCT.VolumeI.Chapter01.Section06.Cospans.FixedParameterConeAction as Map

module Image {C D : CAT} (F : MAP C D) (x : Obj-abs C) where
  private
    module Source = CosliceEndpoint x using (square)
    module U = Reading.At 𝒯 M ℱ P I x using (universal)
    module Actual = Functors.Image 𝒯 M ℱ P I F x using (functor; image; computation)
    module Normal = Map.Along 𝒯 P ev₀ x (funPost F) ev₀ F (F ∘ x)
      (evaluate-post zero F) (idIso (F ∘ x)) using (value; module At)
    normalized = Normal.value Source.square
    q = coslice-projection x
    a₀ = MorphismExpression.arrow U.universal
    σ = MorphismExpression.source-frame U.universal
    γ = constant-image (Coslice C x) F x
    v = post-boundary zero F a₀ σ
    w = (F ◁ σ) ∙ evaluate-post-at zero F a₀

  image-expression : MorphismExpression (const (F ∘ x)) (F ∘ q)
  image-expression = retarget-expression (post-expression F U.universal) γ (idIso (F ∘ q))

  image-cone : Cone ev₀ (F ∘ x) (Coslice C x)
  image-cone = record { left = MorphismExpression.arrow image-expression
    ; right = terminate (Coslice C x) ; match = MorphismExpression.source-frame image-expression }

  private
    abstract
      matching : Cone.match normalized =₂ Cone.match image-cone
      matching = isoComp-cong (idIso γ) ((post-boundary-normal zero F a₀ σ) ⁻¹) ∙
        (isoComp-unitˡ-at (γ ∙ w) ∙
          isoComp-cong (preWhisker-idIso (F ∘ x) (terminate (Coslice C x))) (idIso (γ ∙ w)))

  abstract
    computation : ConeIso (conePre Actual.functor (CosliceEndpoint.square (F ∘ x))) image-cone
    computation = coneIso-compose (cone-match-change _ _ _ _ matching)
      (coneIso-compose (Normal.At.comparison Source.square) Actual.computation)

  private
    module Read = Decoding.FromCone 𝒯 M ℱ P I (F ∘ x) Actual.functor image-expression computation
      using (comparison; target-comparison)
  open Read public renaming (comparison to expression-computation; target-comparison to projection)
```


A specified identification of source objects can be retained as well. The
source frame below includes the restriction of that identification;
it is not replaced by the identity-source convention above.

```agda
module At {C D : CAT} (F : MAP C D) (x : Obj-abs C) (y : Obj-abs D)
  (α : (F ∘ x) =₁ y) where
  private
    module Source = CosliceEndpoint x using (square)
    module U = Reading.At 𝒯 M ℱ P I x using (universal)
    module Actual = Functors.At 𝒯 M ℱ P I F x y α using (functor; image; computation)
    module Normal = Map.Along 𝒯 P ev₀ x (funPost F) ev₀ F y
      (evaluate-post zero F) α using (value; module At)
    normalized = Normal.value Source.square
    q = coslice-projection x
    a₀ = MorphismExpression.arrow U.universal
    σ = MorphismExpression.source-frame U.universal
    γ₀ = constant-image (Coslice C x) F x
    δ = α ▷ terminate (Coslice C x)
    γ = δ ∙ γ₀
    v = post-boundary zero F a₀ σ
    w = (F ◁ σ) ∙ evaluate-post-at zero F a₀

  image-expression : MorphismExpression (const y) (F ∘ q)
  image-expression = retarget-expression (post-expression F U.universal) γ (idIso (F ∘ q))

  image-cone : Cone ev₀ y (Coslice C x)
  image-cone = record { left = MorphismExpression.arrow image-expression
    ; right = terminate (Coslice C x) ; match = MorphismExpression.source-frame image-expression }

  private
    abstract
      matching : Cone.match normalized =₂ Cone.match image-cone
      matching = isoComp-cong (idIso γ) ((post-boundary-normal zero F a₀ σ) ⁻¹) ∙
        (isoComp-assoc-at δ γ₀ w) ⁻¹

  abstract
    computation : ConeIso (conePre Actual.functor (CosliceEndpoint.square y)) image-cone
    computation = coneIso-compose (cone-match-change _ _ _ _ matching)
      (coneIso-compose (Normal.At.comparison Source.square) Actual.computation)

  private
    module Read = Decoding.FromCone 𝒯 M ℱ P I y Actual.functor image-expression computation
      using (comparison; target-comparison)
  open Read public renaming (comparison to expression-computation; target-comparison to projection)
```
