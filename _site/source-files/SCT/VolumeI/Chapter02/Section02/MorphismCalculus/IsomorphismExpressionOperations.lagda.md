# Primitive identifications under operations on expressions

The expression of a primitive identification is compatible with
postcomposition, restriction, and changes of endpoint frames. These
comparisons let an adjunction with invertible unit or counit be written
using its actual section identification, without forgetting endpoint data.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IsomorphismExpressionOperations
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I
  using (same-arrow; retarget-id; retarget-cong; retarget-assoc; post-retarget; restrict-retarget)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcomposition 𝒯 M ℱ I
  using (post-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionRestriction 𝒯 M ℱ I
  using (restrict-expressionIso)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionPostcomposition 𝒯 M ℱ P I E
  using (post-identity)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionRetargeting as Change
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityExpressionSubstitution as Restrict

abstract
  isomorphism-normal : {Γ C : CAT} {x y : MAP Γ C} (α : x =₁ y) →
    ExpressionIso (retarget-expression (identity-expression x) (idIso x) α)
      (isomorphism-expression α)
  isomorphism-normal {x = x} α = same-arrow (MorphismExpression.arrow (identity-expression x)) _ _ _ _
    ((isoComp-unitˡ-at (MorphismExpression.source-frame (identity-expression x))) ⁻¹)
    (idIso (α ∙ MorphismExpression.target-frame (identity-expression x)))

  isomorphism-cong : {Γ C : CAT} {x y : MAP Γ C} {α β : x =₁ y} → α =₂ β →
    ExpressionIso (isomorphism-expression α) (isomorphism-expression β)
  isomorphism-cong {x = x} {α = α} {β = β} same = expressionIso-compose (isomorphism-normal β)
    (expressionIso-compose (retarget-cong (identity-expression x) (idIso (idIso x)) same)
      (expressionIso-inverse (isomorphism-normal α)))

  isomorphism-id : {Γ C : CAT} (x : MAP Γ C) →
    ExpressionIso (isomorphism-expression (idIso x)) (identity-expression x)
  isomorphism-id x = expressionIso-compose (retarget-id (identity-expression x))
    (expressionIso-inverse (isomorphism-normal (idIso x)))

  isomorphism-post : {Γ C D : CAT} (F : MAP C D) {x y : MAP Γ C} (α : x =₁ y) →
    ExpressionIso (post-expression F (isomorphism-expression α)) (isomorphism-expression (F ◁ α))
  isomorphism-post F {x} α = expressionIso-compose (isomorphism-normal (F ◁ α))
    (expressionIso-compose (retarget-cong (identity-expression (F ∘ x))
      (postWhisker-idIso F x) (idIso (F ◁ α)))
      (expressionIso-compose (retarget-expressionIso (post-identity F x) (F ◁ idIso x) (F ◁ α))
        (expressionIso-compose (post-retarget F (identity-expression x) (idIso x) α)
          (post-expressionIso F (expressionIso-inverse (isomorphism-normal α))))))

  isomorphism-restrict : {Γ Δ C : CAT} {x y : MAP Γ C} (α : x =₁ y) (h : MAP Δ Γ) →
    ExpressionIso (restrict-expression (isomorphism-expression α) h) (isomorphism-expression (α ▷ h))
  isomorphism-restrict {x = x} α h = expressionIso-compose (isomorphism-normal (α ▷ h))
    (expressionIso-compose (retarget-cong (identity-expression (x ∘ h))
      (preWhisker-idIso x h) (idIso (α ▷ h)))
      (expressionIso-compose (retarget-expressionIso (Restrict.Restrict.comparison 𝒯 M ℱ P I E x h)
        (idIso x ▷ h) (α ▷ h))
        (expressionIso-compose (restrict-retarget (identity-expression x) (idIso x) α h)
          (restrict-expressionIso (expressionIso-inverse (isomorphism-normal α)) h))))

  framed-identity : {Γ C : CAT} {x x′ y′ : MAP Γ C} (p : x =₁ x′) (q : x =₁ y′) →
    ExpressionIso (retarget-expression (identity-expression x) p q) (isomorphism-expression (q ∙ p ⁻¹))
  framed-identity {x = x} {x′} p q = expressionIso-compose (isomorphism-normal (q ∙ p ⁻¹))
    (expressionIso-compose (retarget-expressionIso (Change.At.comparison 𝒯 M ℱ P I E p)
      (idIso x′) (q ∙ p ⁻¹))
      (expressionIso-inverse (expressionIso-compose
        (retarget-cong (identity-expression x) (isoComp-unitˡ-at p)
          (isoComp-unitʳ-at q ∙
            isoComp-cong (idIso q) (isoComp-inverseˡ-at p) ∙
            isoComp-assoc-at q (p ⁻¹) p))
        (retarget-assoc (identity-expression x) p p (idIso x′) (q ∙ p ⁻¹)))))

  isomorphism-retarget : {Γ C : CAT} {x y x′ y′ : MAP Γ C}
    (α : x =₁ y) (p : x =₁ x′) (q : y =₁ y′) →
    ExpressionIso (retarget-expression (isomorphism-expression α) p q)
      (isomorphism-expression ((q ∙ α) ∙ p ⁻¹))
  isomorphism-retarget {x = x} α p q = expressionIso-compose (framed-identity p (q ∙ α))
    (expressionIso-compose (retarget-cong (identity-expression x) (isoComp-unitʳ-at p) (idIso (q ∙ α)))
      (expressionIso-compose (retarget-assoc (identity-expression x) (idIso x) α p q)
        (retarget-expressionIso (expressionIso-inverse (isomorphism-normal α)) p q)))
```
