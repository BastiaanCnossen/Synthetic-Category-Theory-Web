# Invertible morphisms act by equivalences on hom categories

At each absolute parameter, inverse triangles give cancellation and a lift.
The naive bijection criterion turns these two properties into an equivalence.
No coherent choice of inverse triangles over varying parameters is required.

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
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter02.Section06.HomCompositionEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.ExpressionCancellation 𝒯 M ℱ P I E S Q using (module InverseEquation; compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section03.LiftedInverseExpressions 𝒯 M ℱ P I E S
  using (lift-invertible-expression; IsInvertibleExpression; IsoLift; isoArrow)

module InvertiblePoint {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y))
  (w : IsoLift (MorphismExpression.arrow (hom-expression e))) where
  module F = At e
  module H = EndpointFiber x y
  module W = IsoLift w

  family-lift : (Γ : CAT) → IsoLift (MorphismExpression.arrow (F.family Γ))
  family-lift Γ = record { lift = W.lift ∘ terminate Γ
    ; comparison = comp-assoc (terminate Γ) e H.arrow ∙
        ((W.comparison ▷ terminate Γ) ∙ (comp-assoc (terminate Γ) W.lift isoArrow) ⁻¹) }

  family-invertible : (Γ : CAT) → IsInvertibleExpression (F.family Γ)
  family-invertible Γ = lift-invertible-expression (F.family Γ) (family-lift Γ)

  module AtParameter (Γ : CAT) where
    module V = IsInvertibleExpression (family-invertible Γ)
    module Left = InverseEquation (F.family Γ) V.left-inverse V.left-inverse-law
    module Right = InverseEquation V.right-inverse (F.family Γ) V.right-inverse-law

    post-reflect : (z : Obj-abs C) (h k : MAP Γ (Hom C z x)) →
      (F.postcompose z ∘ h) =₁ (F.postcompose z ∘ k) → h =₁ k
    post-reflect z h k α = hom-reflect (Left.reflect-after (hom-expression h) (hom-expression k)
      (expressionIso-compose (F.postcompose-β z k)
        (expressionIso-compose (hom-expression-cong α) (expressionIso-inverse (F.postcompose-β z h)))))

    post-lift : (z : Obj-abs C) (h : MAP Γ (Hom C z y)) → FunctorLift (F.postcompose z) h
    post-lift z h = record { lift = hom-intro candidate
      ; comparison = hom-reflect (expressionIso-compose (Right.cancel-after (hom-expression h))
          (expressionIso-compose (compose-expression-cong (hom-β candidate) (expressionIso-id (F.family Γ)))
            (F.postcompose-β z (hom-intro candidate)))) }
      where candidate = compose-expression (hom-expression h) V.right-inverse

    pre-reflect : (z : Obj-abs C) (h k : MAP Γ (Hom C y z)) →
      (F.precompose z ∘ h) =₁ (F.precompose z ∘ k) → h =₁ k
    pre-reflect z h k α = hom-reflect (Right.reflect-before (hom-expression h) (hom-expression k)
      (expressionIso-compose (F.precompose-β z k)
        (expressionIso-compose (hom-expression-cong α) (expressionIso-inverse (F.precompose-β z h)))))

    pre-lift : (z : Obj-abs C) (h : MAP Γ (Hom C x z)) → FunctorLift (F.precompose z) h
    pre-lift z h = record { lift = hom-intro candidate
      ; comparison = hom-reflect (expressionIso-compose (Left.cancel-before (hom-expression h))
          (expressionIso-compose (compose-expression-cong (expressionIso-id (F.family Γ)) (hom-β candidate))
            (F.precompose-β z (hom-intro candidate)))) }
      where candidate = compose-expression V.left-inverse (hom-expression h)

  postcompose-isEquiv : (z : Obj-abs C) → IsEquiv (F.postcompose z)
  postcompose-isEquiv z = naive-bijection-isEquiv
    (record { reflect = λ {Γ} → AtParameter.post-reflect Γ z
            ; lift = λ {Γ} → AtParameter.post-lift Γ z })

  precompose-isEquiv : (z : Obj-abs C) → IsEquiv (F.precompose z)
  precompose-isEquiv z = naive-bijection-isEquiv
    (record { reflect = λ {Γ} → AtParameter.pre-reflect Γ z
            ; lift = λ {Γ} → AtParameter.pre-lift Γ z })
```
