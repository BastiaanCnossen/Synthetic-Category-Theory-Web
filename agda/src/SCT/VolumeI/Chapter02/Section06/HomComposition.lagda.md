# Composition on hom categories

Fix an absolute point of a hom category. Composition with its constant
family defines postcomposition and precomposition functors. Their computation
rules hold for every absolute parameter category and preserve both endpoints.

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

module SCT.VolumeI.Chapter02.Section06.HomComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section06.HomCalculus.HomRestriction 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionExpressions 𝒯 M ℱ P I E S public using (compose-expression)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionIdentifications 𝒯 M ℱ P I E S using (compose-expression-cong)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.CompositionSubstitution 𝒯 M ℱ P I E S using (restrict-composition; retarget-composition)

hom-reflect : {Γ C : CAT} {x y : Obj-abs C} {h k : MAP Γ (Hom C x y)} →
  ExpressionIso (hom-expression h) (hom-expression k) → h =₁ k
hom-reflect {h = h} {k} Φ = hom-η k ∙ (hom-cong Φ ∙ (hom-η h) ⁻¹)

hom-intro-reflect : {Γ C : CAT} {x y : Obj-abs C}
  {f g : MorphismExpression (const {P = Γ} x) (const y)} →
  hom-intro f =₁ hom-intro g → ExpressionIso f g
hom-intro-reflect {f = f} {g} α = expressionIso-compose (hom-β g)
  (expressionIso-compose (hom-expression-cong α) (expressionIso-inverse (hom-β f)))

hom-restrict-composition : {Γ Δ C : CAT} {x y z : Obj-abs C}
  (f : MorphismExpression (const {P = Γ} x) (const y))
  (g : MorphismExpression (const {P = Γ} y) (const z)) (r : MAP Δ Γ) →
  ExpressionIso (hom-restrict (compose-expression f g) r)
    (compose-expression (hom-restrict f r) (hom-restrict g r))
hom-restrict-composition {x = x} {y} {z} f g r = expressionIso-compose
  (expressionIso-inverse (retarget-composition (restrict-expression f r) (restrict-expression g r)
    (const-pre x r) (const-pre y r) (const-pre z r)))
  (retarget-expressionIso (expressionIso-inverse (restrict-composition f g r)) (const-pre x r) (const-pre z r))

hom-universal-restrict : {Γ C : CAT} {x y : Obj-abs C} (h : MAP Γ (Hom C x y)) →
  ExpressionIso (hom-restrict (hom-expression (id (Hom C x y))) h) (hom-expression h)
hom-universal-restrict h = expressionIso-compose (hom-expression-cong (comp-unitˡ h))
  (expressionIso-inverse (hom-expression-restrict (id _) h))

module At {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  family : (Γ : CAT) → MorphismExpression (const {P = Γ} x) (const y)
  family Γ = hom-expression (const e)

  family-restrict : {Γ Δ : CAT} (r : MAP Δ Γ) →
    ExpressionIso (hom-restrict (family Γ) r) (family Δ)
  family-restrict r = expressionIso-compose (hom-expression-cong (const-pre e r))
    (expressionIso-inverse (hom-expression-restrict (const e) r))

  family-at-point : ExpressionIso (family One) (hom-expression e)
  family-at-point = hom-expression-cong (const-One e)

  postcompose : (z : Obj-abs C) → MAP (Hom C z x) (Hom C z y)
  postcompose z = hom-intro (compose-expression (hom-expression (id (Hom C z x))) (family (Hom C z x)))

  precompose : (z : Obj-abs C) → MAP (Hom C y z) (Hom C x z)
  precompose z = hom-intro (compose-expression (family (Hom C y z)) (hom-expression (id (Hom C y z))))

  postcompose-β : {Γ : CAT} (z : Obj-abs C) (h : MAP Γ (Hom C z x)) →
    ExpressionIso (hom-expression (postcompose z ∘ h)) (compose-expression (hom-expression h) (family Γ))
  postcompose-β z h = expressionIso-compose
    (compose-expression-cong (hom-universal-restrict h) (family-restrict h))
    (expressionIso-compose (hom-restrict-composition (hom-expression (id _)) (family _) h)
      (expressionIso-compose (hom-restrict-cong (hom-β _) h) (hom-expression-restrict (postcompose z) h)))

  precompose-β : {Γ : CAT} (z : Obj-abs C) (h : MAP Γ (Hom C y z)) →
    ExpressionIso (hom-expression (precompose z ∘ h)) (compose-expression (family Γ) (hom-expression h))
  precompose-β z h = expressionIso-compose
    (compose-expression-cong (family-restrict h) (hom-universal-restrict h))
    (expressionIso-compose (hom-restrict-composition (family _) (hom-expression (id _)) h)
      (expressionIso-compose (hom-restrict-cong (hom-β _) h) (hom-expression-restrict (precompose z) h)))
```


The computation comparisons at the identity parameter expose each hom
functor without unfolding its chosen universal lift.

```agda
module Computation {C : CAT} {x y : Obj-abs C} (e : Obj-abs (Hom C x y)) where
  private
    module Action = At e using (family; precompose; postcompose; precompose-β; postcompose-β)
  abstract
    precompose : (z : Obj-abs C) →
      ExpressionIso (hom-expression (Action.precompose z))
        (compose-expression (Action.family (Hom C y z)) (hom-expression (id (Hom C y z))))
    precompose z = expressionIso-compose (Action.precompose-β z (id _))
      (hom-expression-cong ((comp-unitʳ (Action.precompose z)) ⁻¹))
    postcompose : (z : Obj-abs C) →
      ExpressionIso (hom-expression (Action.postcompose z))
        (compose-expression (hom-expression (id (Hom C z x))) (Action.family (Hom C z x)))
    postcompose z = expressionIso-compose (Action.postcompose-β z (id _))
      (hom-expression-cong ((comp-unitʳ (Action.postcompose z)) ⁻¹))
```
