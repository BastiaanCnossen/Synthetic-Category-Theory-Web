# Fixing one coordinate of a paired expression

Pairing with an identity agrees with applying the corresponding
fixed-coordinate insertion. The endpoint identifications are constructed
from the two projection comparisons and are independent of the arrow.

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

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.FixedCoordinateExpressions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.Morphisms 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFrameCalculus 𝒯 M ℱ I using (retarget-assoc; retarget-cong; post-retarget)
open import SCT.VolumeI.Chapter02.Section02.ProductComposition 𝒯 M ℱ P I E S using (retarget-reflect)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressionReflection 𝒯 M ℱ I using (product-expression-reflect)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions 𝒯 M ℱ I using (pair-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.IdentityFunctorExpressions 𝒯 M ℱ P I E using (post-id)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions 𝒯 M ℱ P I E using (constant-point-frame)
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ProductExpressions as Pairs
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionPostcompositionPasting as Pasting
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantFunctorExpressions as Constant
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Iso
open Iso vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Pairing {Γ A B C : CAT} (J : MAP A (B × C)) {x y : MAP Γ A} (f : MorphismExpression x y)
  {x₁ y₁ : MAP Γ B} {x₂ y₂ : MAP Γ C} (g : MorphismExpression x₁ y₁) (h : MorphismExpression x₂ y₂)
  (p₁ : (pr₁ ∘ (J ∘ x)) =₁ x₁) (q₁ : (pr₁ ∘ (J ∘ y)) =₁ y₁)
  (p₂ : (pr₂ ∘ (J ∘ x)) =₁ x₂) (q₂ : (pr₂ ∘ (J ∘ y)) =₁ y₂)
  (first : ExpressionIso (retarget-expression (post-expression pr₁ (post-expression J f)) p₁ q₁) g)
  (second : ExpressionIso (retarget-expression (post-expression pr₂ (post-expression J f)) p₂ q₂) h) where
  source-frame : (J ∘ x) =₁ pair x₁ x₂
  source-frame = pair-iso ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)
  target-frame : (J ∘ y) =₁ pair y₁ y₂
  target-frame = pair-iso ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)
  value = retarget-expression (post-expression J f) source-frame target-frame
  module Paired = Pairs.At 𝒯 M ℱ I g h

  module Projection {Y : CAT} (π : MAP (B × C) Y) {u v : MAP Γ Y}
    (s : (π ∘ pair x₁ x₂) =₁ u) (t : (π ∘ pair y₁ y₂) =₁ v)
    (p : (π ∘ (J ∘ x)) =₁ u) (q : (π ∘ (J ∘ y)) =₁ v)
    (source : (s ∙ (π ◁ source-frame)) =₂ p) (target : (t ∙ (π ◁ target-frame)) =₂ q)
    (k : MorphismExpression u v)
    (result : ExpressionIso (retarget-expression (post-expression π (post-expression J f)) p q) k)
    (paired : ExpressionIso (retarget-expression (post-expression π (pair-expression g h)) s t) k) where
    abstract
      comparison : ExpressionIso (post-expression π value) (post-expression π (pair-expression g h))
      comparison = retarget-reflect s t
        (expressionIso-compose (expressionIso-inverse paired)
          (expressionIso-compose result
            (expressionIso-compose (retarget-cong (post-expression π (post-expression J f)) source target)
              (expressionIso-compose
                (retarget-assoc (post-expression π (post-expression J f)) (π ◁ source-frame) (π ◁ target-frame) s t)
                (retarget-expressionIso (post-retarget π (post-expression J f) source-frame target-frame) s t)))))

  abstract
    comparison : ExpressionIso value (pair-expression g h)
    comparison = product-expression-reflect
      (Projection.comparison pr₁ (pair-β₁ x₁ x₂) (pair-β₁ y₁ y₂) p₁ q₁
        (cancel-inverse (pair-β₁ x₁ x₂) p₁ ∙ isoComp-cong (idIso (pair-β₁ x₁ x₂))
          (pair-iso-β₁ ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)))
        (cancel-inverse (pair-β₁ y₁ y₂) q₁ ∙ isoComp-cong (idIso (pair-β₁ y₁ y₂))
          (pair-iso-β₁ ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)))
        g first Paired.first-projection)
      (Projection.comparison pr₂ (pair-β₂ x₁ x₂) (pair-β₂ y₁ y₂) p₂ q₂
        (cancel-inverse (pair-β₂ x₁ x₂) p₂ ∙ isoComp-cong (idIso (pair-β₂ x₁ x₂))
          (pair-iso-β₂ ((pair-β₁ x₁ x₂) ⁻¹ ∙ p₁) ((pair-β₂ x₁ x₂) ⁻¹ ∙ p₂)))
        (cancel-inverse (pair-β₂ y₁ y₂) q₂ ∙ isoComp-cong (idIso (pair-β₂ y₁ y₂))
          (pair-iso-β₂ ((pair-β₁ y₁ y₂) ⁻¹ ∙ q₁) ((pair-β₂ y₁ y₂) ⁻¹ ∙ q₂)))
        h second Paired.second-projection)

module FixRight {A B : CAT} (y : Obj-abs B) where
  insertion : MAP A (A × B)
  insertion = pair (id A) (const y)
  identity-comparison = pair-β₁ (id A) (const y)
  constant-comparison = pair-β₂ (id A) (const y)
  identity-frame : (x : Obj-abs A) → (pr₁ ∘ (insertion ∘ x)) =₁ x
  identity-frame x = comp-unitˡ x ∙ ((identity-comparison ▷ x) ∙ (comp-assoc x insertion pr₁) ⁻¹)
  constant-frame : (x : Obj-abs A) → (pr₂ ∘ (insertion ∘ x)) =₁ y
  constant-frame x = constant-point-frame y x ∙ ((constant-comparison ▷ x) ∙ (comp-assoc x insertion pr₂) ⁻¹)
  frame : (x : Obj-abs A) → (insertion ∘ x) =₁ pair x y
  frame x = pair-iso ((pair-β₁ x y) ⁻¹ ∙ identity-frame x) ((pair-β₂ x y) ⁻¹ ∙ constant-frame x)

  module Arrow {x x′ : Obj-abs A} (f : MorphismExpression x x′) where
    module First = Pasting.At 𝒯 M ℱ P I E insertion pr₁ (id A) identity-comparison f
    module Second = Pasting.At 𝒯 M ℱ P I E insertion pr₂ (const y) constant-comparison f
    first : ExpressionIso
      (retarget-expression (post-expression pr₁ (post-expression insertion f)) (identity-frame x) (identity-frame x′)) f
    first = expressionIso-compose (post-id f)
      (expressionIso-compose (retarget-expressionIso First.comparison (comp-unitˡ x) (comp-unitˡ x′))
        (expressionIso-inverse (retarget-assoc (post-expression pr₁ (post-expression insertion f))
          First.source-change First.target-change (comp-unitˡ x) (comp-unitˡ x′))))
    second : ExpressionIso
      (retarget-expression (post-expression pr₂ (post-expression insertion f)) (constant-frame x) (constant-frame x′))
      (identity-expression y)
    second = expressionIso-compose (Constant.Absolute.comparison 𝒯 M ℱ P I E y f)
      (expressionIso-compose (retarget-expressionIso Second.comparison (constant-point-frame y x) (constant-point-frame y x′))
        (expressionIso-inverse (retarget-assoc (post-expression pr₂ (post-expression insertion f))
          Second.source-change Second.target-change (constant-point-frame y x) (constant-point-frame y x′))))
    module Paired = Pairing insertion f f (identity-expression y)
      (identity-frame x) (identity-frame x′) (constant-frame x) (constant-frame x′) first second
    abstract
      comparison : ExpressionIso (retarget-expression (post-expression insertion f) (frame x) (frame x′))
        (pair-expression f (identity-expression y))
      comparison = Paired.comparison

module FixLeft {A B : CAT} (x : Obj-abs A) where
  insertion : MAP B (A × B)
  insertion = pair (const x) (id B)
  constant-comparison = pair-β₁ (const x) (id B)
  identity-comparison = pair-β₂ (const x) (id B)
  constant-frame : (y : Obj-abs B) → (pr₁ ∘ (insertion ∘ y)) =₁ x
  constant-frame y = constant-point-frame x y ∙ ((constant-comparison ▷ y) ∙ (comp-assoc y insertion pr₁) ⁻¹)
  identity-frame : (y : Obj-abs B) → (pr₂ ∘ (insertion ∘ y)) =₁ y
  identity-frame y = comp-unitˡ y ∙ ((identity-comparison ▷ y) ∙ (comp-assoc y insertion pr₂) ⁻¹)
  frame : (y : Obj-abs B) → (insertion ∘ y) =₁ pair x y
  frame y = pair-iso ((pair-β₁ x y) ⁻¹ ∙ constant-frame y) ((pair-β₂ x y) ⁻¹ ∙ identity-frame y)

  module Arrow {y y′ : Obj-abs B} (f : MorphismExpression y y′) where
    module First = Pasting.At 𝒯 M ℱ P I E insertion pr₁ (const x) constant-comparison f
    module Second = Pasting.At 𝒯 M ℱ P I E insertion pr₂ (id B) identity-comparison f
    first : ExpressionIso
      (retarget-expression (post-expression pr₁ (post-expression insertion f)) (constant-frame y) (constant-frame y′))
      (identity-expression x)
    first = expressionIso-compose (Constant.Absolute.comparison 𝒯 M ℱ P I E x f)
      (expressionIso-compose (retarget-expressionIso First.comparison (constant-point-frame x y) (constant-point-frame x y′))
        (expressionIso-inverse (retarget-assoc (post-expression pr₁ (post-expression insertion f))
          First.source-change First.target-change (constant-point-frame x y) (constant-point-frame x y′))))
    second : ExpressionIso
      (retarget-expression (post-expression pr₂ (post-expression insertion f)) (identity-frame y) (identity-frame y′)) f
    second = expressionIso-compose (post-id f)
      (expressionIso-compose (retarget-expressionIso Second.comparison (comp-unitˡ y) (comp-unitˡ y′))
        (expressionIso-inverse (retarget-assoc (post-expression pr₂ (post-expression insertion f))
          Second.source-change Second.target-change (comp-unitˡ y) (comp-unitˡ y′))))
    module Paired = Pairing insertion f (identity-expression x) f
      (constant-frame y) (constant-frame y′) (identity-frame y) (identity-frame y′) first second
    abstract
      comparison : ExpressionIso (retarget-expression (post-expression insertion f) (frame y) (frame y′))
        (pair-expression (identity-expression x) f)
      comparison = Paired.comparison
```
