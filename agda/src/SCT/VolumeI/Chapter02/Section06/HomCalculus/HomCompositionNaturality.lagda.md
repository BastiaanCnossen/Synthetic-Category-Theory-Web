# Hom-composition squares of a functor

Functorial images preserve composition. Applying this to the universal
hom family gives the commutative squares used to define cartesian and
cocartesian morphisms. The matching is built from framed comparisons,
so its endpoint identifications are retained.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal

module SCT.VolumeI.Chapter02.Section06.HomCalculus.HomCompositionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomComposition 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomPostcomposition 𝒯 M ℱ P I
  using (hom-image; hom-image-cong; hom-post-β; hom-post-computation)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S
  using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S
  using (retarget-composition)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.PostcompositionPresentations 𝒯 M ℱ P I E S
  using (post-composition)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (constant-image)

abstract
  hom-image-composition : {Γ C D : CAT} (F : MAP C D) {x y z : Obj-abs C}
    (α : MorphismExpression (const {P = Γ} x) (const y))
    (β : MorphismExpression (const {P = Γ} y) (const z)) →
    ExpressionIso (hom-image F (compose-expression α β))
      (compose-expression (hom-image F α) (hom-image F β))
  hom-image-composition {Γ} F {x} {y} {z} α β = expressionIso-inverse
    (expressionIso-compose (retarget-expressionIso (post-composition F α β)
      (constant-image Γ F x) (constant-image Γ F z))
      (retarget-composition (post-expression F α) (post-expression F β)
        (constant-image Γ F x) (constant-image Γ F y) (constant-image Γ F z)))

private
  reflect-through-calculation : {Γ C : CAT} {x y : Obj-abs C}
    (h k : MAP Γ (Hom C x y)) (α : MorphismExpression (const {P = Γ} x) (const y)) →
    ExpressionIso (hom-expression h) α → ExpressionIso (hom-expression k) α → h =₁ k
  reflect-through-calculation {Γ} {C} {x} {y} h k α left right =
    hom-reflect {Γ = Γ} {C = C} {x = x} {y = y} {h = h} {k = k}
      (expressionIso-compose {f = hom-expression h} {g = α} {h = hom-expression k}
        (expressionIso-inverse right) left)

  abstract
    reflect-through : {Γ C : CAT} {x y : Obj-abs C}
      (h k : MAP Γ (Hom C x y)) (α : MorphismExpression (const {P = Γ} x) (const y)) →
      ExpressionIso (hom-expression h) α → ExpressionIso (hom-expression k) α → h =₁ k
    reflect-through {Γ} {C} {x} {y} h k α left right =
      reflect-through-calculation {Γ = Γ} {C = C} {x = x} {y = y} h k α left right

    reflect-through-computation : {Γ C : CAT} {x y : Obj-abs C}
      (h k : MAP Γ (Hom C x y)) (α : MorphismExpression (const {P = Γ} x) (const y))
      (left : ExpressionIso (hom-expression h) α) (right : ExpressionIso (hom-expression k) α) →
      reflect-through h k α left right =₂ reflect-through-calculation h k α left right
    reflect-through-computation h k α left right = idIso _

module Image {C D : CAT} (F : MAP C D) {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Original = At {C = C} {x = x} {y = y} e using (family; precompose; postcompose)
    module OriginalComputation = Computation {C = C} {x = x} {y = y} e using (precompose; postcompose)
  point : Obj-abs (Hom D (F ∘ x) (F ∘ y))
  point = hom-post F x y ∘ e
  private
    module Mapped = At {C = D} {x = F ∘ x} {y = F ∘ y} point using (family; precompose; postcompose; precompose-β; postcompose-β)

  abstract
    family-comparison : (Γ : CAT) → ExpressionIso (hom-image F (Original.family Γ)) (Mapped.family Γ)
    family-comparison Γ = expressionIso-compose
      (hom-expression-cong (constant-image Γ (hom-post F x y) e))
      (expressionIso-inverse (hom-post-β F x y (const e)))

  private
    module Precomposition (z : Obj-abs C) where
      H : CAT
      H = Hom C y z
      result : MorphismExpression (const {P = H} (F ∘ x)) (const (F ∘ z))
      result = compose-expression (Mapped.family H) (hom-image F (hom-expression (id H)))

      abstract
        left : ExpressionIso (hom-expression (hom-post F x z ∘ Original.precompose z)) result
        left = expressionIso-compose
          (compose-expression-cong
            {f = hom-image F (Original.family H)} {f′ = Mapped.family H}
            {g = hom-image F (hom-expression (id H))} {g′ = hom-image F (hom-expression (id H))}
            (family-comparison H) (expressionIso-id (hom-image F (hom-expression (id H)))))
          (expressionIso-compose (hom-image-composition F (Original.family H) (hom-expression (id H)))
            (expressionIso-compose (hom-image-cong F (OriginalComputation.precompose z))
              (hom-post-β F x z (Original.precompose z))))
        right : ExpressionIso (hom-expression (Mapped.precompose (F ∘ z) ∘ hom-post F y z)) result
        right = expressionIso-compose (compose-expression-cong
          {f = Mapped.family H} {f′ = Mapped.family H}
          {g = hom-expression (hom-post F y z)} {g′ = hom-image F (hom-expression (id H))}
          (expressionIso-id (Mapped.family H))
          (hom-post-computation F y z))
          (Mapped.precompose-β (F ∘ z) (hom-post F y z))

  precompose-calculation : (z : Obj-abs C) →
    (hom-post F x z ∘ Original.precompose z) =₁
      (Mapped.precompose (F ∘ z) ∘ hom-post F y z)
  precompose-calculation z = reflect-through-calculation {Γ = Hom C y z} {C = D} {x = F ∘ x} {y = F ∘ z}
    (hom-post F x z ∘ Original.precompose z)
    (Mapped.precompose (F ∘ z) ∘ hom-post F y z) (Precomposition.result z) (Precomposition.left z) (Precomposition.right z)

  precompose : (z : Obj-abs C) →
    (hom-post F x z ∘ Original.precompose z) =₁
      (Mapped.precompose (F ∘ z) ∘ hom-post F y z)
  precompose z = reflect-through {Γ = Hom C y z} {C = D} {x = F ∘ x} {y = F ∘ z}
    (hom-post F x z ∘ Original.precompose z)
    (Mapped.precompose (F ∘ z) ∘ hom-post F y z) (Precomposition.result z) (Precomposition.left z) (Precomposition.right z)

  precompose-computation : (z : Obj-abs C) →
    precompose z =₂ precompose-calculation z
  precompose-computation z = reflect-through-computation {Γ = Hom C y z} {C = D} {x = F ∘ x} {y = F ∘ z}
    (hom-post F x z ∘ Original.precompose z)
    (Mapped.precompose (F ∘ z) ∘ hom-post F y z) (Precomposition.result z) (Precomposition.left z) (Precomposition.right z)

  private
    module Postcomposition (z : Obj-abs C) where
      H : CAT
      H = Hom C z x
      result : MorphismExpression (const {P = H} (F ∘ z)) (const (F ∘ y))
      result = compose-expression (hom-image F (hom-expression (id H))) (Mapped.family H)

      abstract
        left : ExpressionIso (hom-expression (hom-post F z y ∘ Original.postcompose z)) result
        left = expressionIso-compose
          (compose-expression-cong
            {f = hom-image F (hom-expression (id H))} {f′ = hom-image F (hom-expression (id H))}
            {g = hom-image F (Original.family H)} {g′ = Mapped.family H}
            (expressionIso-id (hom-image F (hom-expression (id H)))) (family-comparison H))
          (expressionIso-compose (hom-image-composition F (hom-expression (id H)) (Original.family H))
            (expressionIso-compose (hom-image-cong F (OriginalComputation.postcompose z))
              (hom-post-β F z y (Original.postcompose z))))
        right : ExpressionIso (hom-expression (Mapped.postcompose (F ∘ z) ∘ hom-post F z x)) result
        right = expressionIso-compose (compose-expression-cong
          {f = hom-expression (hom-post F z x)} {f′ = hom-image F (hom-expression (id H))}
          {g = Mapped.family H} {g′ = Mapped.family H}
          (hom-post-computation F z x) (expressionIso-id (Mapped.family H)))
          (Mapped.postcompose-β (F ∘ z) (hom-post F z x))

  postcompose-calculation : (z : Obj-abs C) →
    (hom-post F z y ∘ Original.postcompose z) =₁
      (Mapped.postcompose (F ∘ z) ∘ hom-post F z x)
  postcompose-calculation z = reflect-through-calculation {Γ = Hom C z x} {C = D} {x = F ∘ z} {y = F ∘ y}
    (hom-post F z y ∘ Original.postcompose z)
    (Mapped.postcompose (F ∘ z) ∘ hom-post F z x) (Postcomposition.result z) (Postcomposition.left z) (Postcomposition.right z)

  postcompose : (z : Obj-abs C) →
    (hom-post F z y ∘ Original.postcompose z) =₁
      (Mapped.postcompose (F ∘ z) ∘ hom-post F z x)
  postcompose z = reflect-through {Γ = Hom C z x} {C = D} {x = F ∘ z} {y = F ∘ y}
    (hom-post F z y ∘ Original.postcompose z)
    (Mapped.postcompose (F ∘ z) ∘ hom-post F z x) (Postcomposition.result z) (Postcomposition.left z) (Postcomposition.right z)

  postcompose-computation : (z : Obj-abs C) →
    postcompose z =₂ postcompose-calculation z
  postcompose-computation z = reflect-through-computation {Γ = Hom C z x} {C = D} {x = F ∘ z} {y = F ∘ y}
    (hom-post F z y ∘ Original.postcompose z)
    (Mapped.postcompose (F ∘ z) ∘ hom-post F z x) (Postcomposition.result z) (Postcomposition.left z) (Postcomposition.right z)

```
