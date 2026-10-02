# Recovering an identification from a normalized identity

An expression that becomes the identity under two endpoint identifications
is the expression of their composite, with the target identification inverted.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.NormalizedIdentityExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-cancel)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations 𝒯 M ℱ P I E
  using (isomorphism-cong; isomorphism-id; framed-identity)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (inverse-inverse)

abstract
  normalized-identity : {Γ C : CAT} {x y z : MAP Γ C}
    (f : MorphismExpression x y) (p : x =₁ z) (q : y =₁ z) →
    ExpressionIso (retarget-expression f p q) (identity-expression z) →
    ExpressionIso f (isomorphism-expression (q ⁻¹ ∙ p))
  normalized-identity f p q normalized = expressionIso-compose
    (isomorphism-cong (isoComp-cong (idIso (q ⁻¹)) (inverse-inverse p)))
    (expressionIso-compose (framed-identity (p ⁻¹) (q ⁻¹))
      (expressionIso-compose (retarget-expressionIso normalized (p ⁻¹) (q ⁻¹))
        (expressionIso-inverse (retarget-cancel f p q))))

  identity-reflect : {Γ C : CAT} {x y : MAP Γ C}
    (f : MorphismExpression x x) (p : x =₁ y) →
    ExpressionIso (retarget-expression f p p) (identity-expression y) →
    ExpressionIso f (identity-expression x)
  identity-reflect {x = x} f p normalized = expressionIso-compose (isomorphism-id x)
    (expressionIso-compose (isomorphism-cong (isoComp-inverseˡ-at p))
      (normalized-identity f p p normalized))
```

When the two endpoint identifications coincide, this recovers the original
identity law. A later triangle calculation can therefore normalize its object
first and reflect the identity law after the normalized calculation.
