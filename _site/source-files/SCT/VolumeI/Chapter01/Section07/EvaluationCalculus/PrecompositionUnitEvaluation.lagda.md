# Evaluating the precomposition unit frame

Precomposition of the identity functor evaluates compatibly with the
chosen uncurrying unit and the right unitor of the precomposition functor.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.PrecompositionUnitEvaluation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ public
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.ProductSeparationUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluatedUnitSquare as Evaluated
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingUnits as Images

module At {C D : CAT} (K : CAT) (r : MAP D C) where
  X = Fun C K
  L : MAP X (Fun D K)
  L = funPre {D = K} r
  e : MAP (X × C) K
  e = funEval
  W : MAP (X × D) (X × C)
  W = productMap (id X) r
  JD : MAP (X × D) (X × D)
  JD = productMap (id X) (id D)
  JC : MAP (X × C) (X × C)
  JC = productMap (id X) (id C)
  β : funUncurry L =₁ (e ∘ W)
  β = funPre-β r
  Q : funUncurry (L ∘ id X) =₁ (funUncurry L ∘ JD)
  Q = funUncurry-restrict L (id X)
  module Product = ProductUnits.At 𝒯 M ℱ X r
  module Unit = Evaluated.At 𝒯 JD JC (productMap-id X D) (productMap-id X C)
    W Product.separation Product.value e β
  module Image = Images.At 𝒯 M ℱ L
  core = Unit.before ⁻¹ ∙ ((e ◁ Product.separation) ∙ (Unit.after ∙ (β ▷ JD)))

  abstract
    normalize : funPre-uncurry r (id X) =₂ (core ∙ Q)
    normalize = (isoComp-assoc-at (Unit.before ⁻¹) ((e ◁ Product.separation) ∙ (Unit.after ∙ (β ▷ JD))) Q) ⁻¹ ∙
      isoComp-cong (idIso (Unit.before ⁻¹))
        ((isoComp-assoc-at (e ◁ Product.separation) (Unit.after ∙ (β ▷ JD)) Q) ⁻¹) ∙
      isoComp-cong (idIso (Unit.before ⁻¹))
        (isoComp-cong (idIso (e ◁ Product.separation)) ((isoComp-assoc-at Unit.after (β ▷ JD) Q) ⁻¹))

    value : ((funUncurry-id C K ▷ W) ∙ funPre-uncurry r (id X)) =₂
      (β ∙ funUncurryIso (comp-unitʳ L))
    value = isoComp-cong (idIso β) (Image.right ⁻¹) ∙
      isoComp-cong (idIso β) (isoComp-assoc-at (comp-unitʳ (funUncurry L)) (funUncurry L ◁ productMap-id X D) Q) ∙
      isoComp-assoc-at β Unit.tU Q ∙
      isoComp-cong Unit.value (idIso Q) ∙
      (isoComp-assoc-at (funUncurry-id C K ▷ W) core Q) ⁻¹ ∙
      isoComp-cong (idIso (funUncurry-id C K ▷ W)) normalize
```
