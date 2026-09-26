# Primitive identifications give invertible morphisms

An identification `x = y` frames the constant interval at `x` as an
arrow from `x` to `y`. Frame the same interval in the opposite direction
for its inverse. Reframing the identity triangle gives both inverse
triangles, with all three vertex equations retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter02.Section03.InvertibleIdentifications
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section03.Isomorphisms 𝒯 M ℱ P I E public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.VertexTransport 𝒯 M ℱ P I E
  using (reframe-morphism; reframe-witness; reframe-identity; morphism-left-unit)
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.MorphismComparisons 𝒯 M ℱ P I using (morphismIso-id)

identification-morphism : {C : CAT} {x y : Obj-abs C} → x =₁ y → Morphism x y
identification-morphism {x = x} α = reframe-morphism (identity-morphism x) (idIso x) α

module InvertibleIdentification {C : CAT} {x y : Obj-abs C} (α : x =₁ y) where
  forward = identification-morphism α
  backward = reframe-morphism (identity-morphism x) α (idIso x)
  identity-triangle = morphism-left-unit (identity-morphism x)

  right-triangle : CompositeWitness backward forward (identity-morphism y)
  right-triangle = retarget-witness
    (morphismIso-id backward) (morphismIso-id forward) (reframe-identity α)
    (reframe-witness α (idIso x) α identity-triangle)

  left-triangle : CompositeWitness forward backward (identity-morphism x)
  left-triangle = retarget-witness
    (morphismIso-id forward) (morphismIso-id backward) (reframe-identity (idIso x))
    (reframe-witness (idIso x) α (idIso x) identity-triangle)

  isInvertible : IsInvertible forward
  isInvertible = record
    { right-inverse = backward ; left-inverse = backward
    ; right-inverse-triangle = right-triangle ; left-inverse-triangle = left-triangle }

identity-isInvertible : {C : CAT} (x : Obj-abs C) → IsInvertible (identity-morphism x)
identity-isInvertible x = record
  { right-inverse = identity-morphism x ; left-inverse = identity-morphism x
  ; right-inverse-triangle = morphism-left-unit (identity-morphism x)
  ; left-inverse-triangle = morphism-left-unit (identity-morphism x) }

post-isInvertible : {C D : CAT} (F : MAP C D) {x y : Obj-abs C}
  {f : Morphism x y} → IsInvertible f → IsInvertible (post-morphism F f)
post-isInvertible F {x} {y} {f} w = record
  { right-inverse = post-morphism F W.right-inverse
  ; left-inverse = post-morphism F W.left-inverse
  ; right-inverse-triangle = retarget-witness
      (morphismIso-id (post-morphism F W.right-inverse)) (morphismIso-id (post-morphism F f))
      (post-identity-morphism F y) (post-witness F W.right-inverse-triangle)
  ; left-inverse-triangle = retarget-witness
      (morphismIso-id (post-morphism F f)) (morphismIso-id (post-morphism F W.left-inverse))
      (post-identity-morphism F x) (post-witness F W.left-inverse-triangle) }
  where module W = IsInvertible w
```
