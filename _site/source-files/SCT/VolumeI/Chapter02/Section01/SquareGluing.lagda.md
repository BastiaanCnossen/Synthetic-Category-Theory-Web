# Gluing two triangles along their common edge

The matching is an explicit argument of `glue`. The returned comparison
is a comparison of whole cocones, including the common edge. This is the
absolute form of `cons:Commutative_Square_From_Commutative_Triangles`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares
import SCT.VolumeI.Chapter01.Section08.PushoutExtensions as Extensions

module SCT.VolumeI.Chapter02.Section01.SquareGluing
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.SquareShape 𝒯 M ℱ P I E public
open Squares.CommutativeSquareAxiom Q
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯 public
open import SCT.VolumeI.Chapter01.Section08.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section08.SquareCocones 𝒯 using (squareCocone)

glue : {C : CAT} → Cocone d₁ d₁ C → CommutativeSquare C
glue {C} t = Extensions.Extensions.Lift.value 𝒯 M P gluing-square square-isPushout C t

glue-β : {C : CAT} (t : Cocone d₁ d₁ C) → CoconeIso
  (coconePost (glue t) (squareCocone gluing-square)) t
glue-β {C} = Extensions.Extensions.Lift.comparison 𝒯 M P gluing-square square-isPushout C

glue-left : {C : CAT} (t : Cocone d₁ d₁ C) → (glue t ∘ j₀) =₁ (Cocone.left t)
glue-left t = CoconeIso.leftIso (glue-β t)

glue-right : {C : CAT} (t : Cocone d₁ d₁ C) → (glue t ∘ j₁) =₁ (Cocone.right t)
glue-right t = CoconeIso.rightIso (glue-β t)

square : {C : CAT} (σ τ : MAP [2] C) → (σ ∘ d₁) =₁ (τ ∘ d₁) → CommutativeSquare C
square σ τ φ = glue (record { left = σ ; right = τ ; match = φ })

glue-compare : {C : CAT} (F G : CommutativeSquare C) →
  CoconeIso (coconePost F (squareCocone gluing-square))
    (coconePost G (squareCocone gluing-square)) → F =₁ G
glue-compare {C} = Extensions.Extensions.Compare.comparison 𝒯 M P gluing-square square-isPushout C

glue-bottom : {C : CAT} (t : Cocone d₁ d₁ C) →
  (glue t ∘ insert zero) =₁ (Cocone.right t ∘ d₂)
glue-bottom t = (glue-right t ▷ d₂) ∙
  ((comp-assoc d₂ j₁ (glue t)) ⁻¹ ∙ (glue t ◁ bottom-boundary ⁻¹))

glue-top : {C : CAT} (t : Cocone d₁ d₁ C) →
  (glue t ∘ insert one) =₁ (Cocone.left t ∘ d₀)
glue-top t = (glue-left t ▷ d₀) ∙
  ((comp-assoc d₀ j₀ (glue t)) ⁻¹ ∙ (glue t ◁ top-boundary ⁻¹))
```
