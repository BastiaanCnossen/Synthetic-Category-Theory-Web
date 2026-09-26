# The two maps from the square to the walking triangle

The maps of `cons:Commutative_Squares_Auxiliary2` come from gluing.
Their four restrictions retain the chosen common-edge matching through
`glue-β`. The coordinate formulas of `lem:Commutative_Squares_Auxiliary3`
then follow by recognizing their horizontal boundary values.

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

module SCT.VolumeI.Chapter02.Section01.SquareCalculus.SquareRetractions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section01.SquareGluing 𝒯 M ℱ P I E Q public
open import SCT.VolumeI.Chapter02.Section01.SquareCalculus.LatticeUniqueness 𝒯 M ℱ P I E

collapse-matching : (s : MAP [2] [1]) → (s ∘ d₁) =₁ (id [1]) →
  (id [2] ∘ d₁) =₁ ((d₁ ∘ s) ∘ d₁)
collapse-matching s ε = (comp-assoc d₁ s d₁) ⁻¹ ∙
  ((d₁ ◁ ε ⁻¹) ∙ ((comp-unitʳ d₁) ⁻¹ ∙ comp-unitˡ d₁))

lower-cocone upper-cocone : Cocone d₁ d₁ [2]
lower-cocone = record
  { left = id [2] ; right = d₁ ∘ s₀ ; match = collapse-matching s₀ s₀-d₁ }
upper-cocone = record
  { left = d₁ ∘ s₁ ; right = id [2] ; match = (collapse-matching s₁ s₁-d₁) ⁻¹ }

p₀ p₂ : MAP ([1] × [1]) [2]
p₀ = glue lower-cocone
p₂ = glue upper-cocone

p₀-j₀ : (p₀ ∘ j₀) =₁ (id [2])
p₀-j₀ = glue-left lower-cocone
p₀-j₁ : (p₀ ∘ j₁) =₁ (d₁ ∘ s₀)
p₀-j₁ = glue-right lower-cocone
p₂-j₀ : (p₂ ∘ j₀) =₁ (d₁ ∘ s₁)
p₂-j₀ = glue-left upper-cocone
p₂-j₁ : (p₂ ∘ j₁) =₁ (id [2])
p₂-j₁ = glue-right upper-cocone

coordinate-bottom : (F : MAP [2] [1]) (t : Cocone d₁ d₁ [2]) →
  ((F ∘ glue t) ∘ insert zero) =₁ ((F ∘ Cocone.right t) ∘ d₂)
coordinate-bottom F t = (comp-assoc d₂ (Cocone.right t) F) ⁻¹ ∙
  ((F ◁ glue-bottom t) ∙ comp-assoc (insert zero) (glue t) F)

coordinate-top : (F : MAP [2] [1]) (t : Cocone d₁ d₁ [2]) →
  ((F ∘ glue t) ∘ insert one) =₁ ((F ∘ Cocone.left t) ∘ d₀)
coordinate-top F t = (comp-assoc d₀ (Cocone.left t) F) ⁻¹ ∙
  ((F ◁ glue-top t) ∙ comp-assoc (insert one) (glue t) F)

collapse-coordinate : (s : MAP [2] [1]) → (s ∘ d₁) =₁ (id [1]) →
  (t : MAP [2] [1]) → (s ∘ (d₁ ∘ t)) =₁ t
collapse-coordinate s ε t = comp-unitˡ t ∙ ((ε ▷ t) ∙ (comp-assoc t d₁ s) ⁻¹)

s₀-p₀ : (s₀ ∘ p₀) =₁ min
s₀-p₀ = recognize-min _
  (s₀-d₂ ∙ ((collapse-coordinate s₀ s₀-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₀ lower-cocone))
  (s₀-d₀ ∙ ((comp-unitʳ s₀ ▷ d₀) ∙ coordinate-top s₀ lower-cocone))

s₁-p₀ : (s₁ ∘ p₀) =₁ pr₂
s₁-p₀ = recognize-second-projection _
  (s₀-d₂ ∙ ((collapse-coordinate s₁ s₁-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₁ lower-cocone))
  (s₁-d₀ ∙ ((comp-unitʳ s₁ ▷ d₀) ∙ coordinate-top s₁ lower-cocone))

s₀-p₂ : (s₀ ∘ p₂) =₁ pr₂
s₀-p₂ = recognize-second-projection _
  (s₀-d₂ ∙ ((comp-unitʳ s₀ ▷ d₂) ∙ coordinate-bottom s₀ upper-cocone))
  (s₁-d₀ ∙ ((collapse-coordinate s₀ s₀-d₁ s₁ ▷ d₀) ∙ coordinate-top s₀ upper-cocone))

s₁-p₂ : (s₁ ∘ p₂) =₁ max
s₁-p₂ = recognize-max _
  (s₁-d₂ ∙ ((comp-unitʳ s₁ ▷ d₂) ∙ coordinate-bottom s₁ upper-cocone))
  (s₁-d₀ ∙ ((collapse-coordinate s₁ s₁-d₁ s₁ ▷ d₀) ∙ coordinate-top s₁ upper-cocone))

j₀-p₀ : (j₀ ∘ p₀) =₁ (pair min pr₂)
j₀-p₀ = pair-cong s₀-p₀ s₁-p₀ ∙ pair-pre s₀ s₁ p₀
j₁-p₀ : (j₁ ∘ p₀) =₁ (pair pr₂ min)
j₁-p₀ = pair-cong s₁-p₀ s₀-p₀ ∙ pair-pre s₁ s₀ p₀
j₀-p₂ : (j₀ ∘ p₂) =₁ (pair pr₂ max)
j₀-p₂ = pair-cong s₀-p₂ s₁-p₂ ∙ pair-pre s₀ s₁ p₂
j₁-p₂ : (j₁ ∘ p₂) =₁ (pair max pr₂)
j₁-p₂ = pair-cong s₁-p₂ s₀-p₂ ∙ pair-pre s₁ s₀ p₂
```
