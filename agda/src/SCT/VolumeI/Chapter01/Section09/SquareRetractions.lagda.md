# The two maps from the square to the walking triangle

The maps of `cons:Commutative_Squares_Auxiliary2` come from gluing.
Their four restrictions retain the chosen common-edge matching through
`glue-β`. The coordinate formulas of `lem:Commutative_Squares_Auxiliary3`
then follow by recognizing their horizontal boundary values.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section05.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section09.WalkingMorphism as Walking
import SCT.VolumeI.Chapter01.Section09.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter01.Section09.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter01.Section09.SquareRetractions
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter01.Section09.SquareGluing 𝒯 M ℱ P I E Q public
open import SCT.VolumeI.Chapter01.Section09.LatticeUniqueness 𝒯 M ℱ P I E

collapse-matching : (s : MAP [2] [1]) → =₁ (s ∘ d₁) (id [1]) →
  =₁ (id [2] ∘ d₁) ((d₁ ∘ s) ∘ d₁)
collapse-matching s ε = invIso (comp-assoc d₁ s d₁) ∙
  ((d₁ ◁ invIso ε) ∙ (invIso (comp-unitʳ d₁) ∙ comp-unitˡ d₁))

lower-cocone upper-cocone : Cocone d₁ d₁ [2]
lower-cocone = record
  { left = id [2] ; right = d₁ ∘ s₀ ; match = collapse-matching s₀ s₀-d₁ }
upper-cocone = record
  { left = d₁ ∘ s₁ ; right = id [2] ; match = invIso (collapse-matching s₁ s₁-d₁) }

p₀ p₂ : MAP ([1] × [1]) [2]
p₀ = glue lower-cocone
p₂ = glue upper-cocone

p₀-j₀ : =₁ (p₀ ∘ j₀) (id [2])
p₀-j₀ = glue-left lower-cocone
p₀-j₁ : =₁ (p₀ ∘ j₁) (d₁ ∘ s₀)
p₀-j₁ = glue-right lower-cocone
p₂-j₀ : =₁ (p₂ ∘ j₀) (d₁ ∘ s₁)
p₂-j₀ = glue-left upper-cocone
p₂-j₁ : =₁ (p₂ ∘ j₁) (id [2])
p₂-j₁ = glue-right upper-cocone

coordinate-bottom : (F : MAP [2] [1]) (t : Cocone d₁ d₁ [2]) →
  =₁ ((F ∘ glue t) ∘ insert zero) ((F ∘ Cocone.right t) ∘ d₂)
coordinate-bottom F t = invIso (comp-assoc d₂ (Cocone.right t) F) ∙
  ((F ◁ glue-bottom t) ∙ comp-assoc (insert zero) (glue t) F)

coordinate-top : (F : MAP [2] [1]) (t : Cocone d₁ d₁ [2]) →
  =₁ ((F ∘ glue t) ∘ insert one) ((F ∘ Cocone.left t) ∘ d₀)
coordinate-top F t = invIso (comp-assoc d₀ (Cocone.left t) F) ∙
  ((F ◁ glue-top t) ∙ comp-assoc (insert one) (glue t) F)

collapse-coordinate : (s : MAP [2] [1]) → =₁ (s ∘ d₁) (id [1]) →
  (t : MAP [2] [1]) → =₁ (s ∘ (d₁ ∘ t)) t
collapse-coordinate s ε t = comp-unitˡ t ∙ ((ε ▷ t) ∙ invIso (comp-assoc t d₁ s))

s₀-p₀ : =₁ (s₀ ∘ p₀) min
s₀-p₀ = recognize-min _
  (s₀-d₂ ∙ ((collapse-coordinate s₀ s₀-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₀ lower-cocone))
  (s₀-d₀ ∙ ((comp-unitʳ s₀ ▷ d₀) ∙ coordinate-top s₀ lower-cocone))

s₁-p₀ : =₁ (s₁ ∘ p₀) pr₂
s₁-p₀ = recognize-second-projection _
  (s₀-d₂ ∙ ((collapse-coordinate s₁ s₁-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₁ lower-cocone))
  (s₁-d₀ ∙ ((comp-unitʳ s₁ ▷ d₀) ∙ coordinate-top s₁ lower-cocone))

s₀-p₂ : =₁ (s₀ ∘ p₂) pr₂
s₀-p₂ = recognize-second-projection _
  (s₀-d₂ ∙ ((comp-unitʳ s₀ ▷ d₂) ∙ coordinate-bottom s₀ upper-cocone))
  (s₁-d₀ ∙ ((collapse-coordinate s₀ s₀-d₁ s₁ ▷ d₀) ∙ coordinate-top s₀ upper-cocone))

s₁-p₂ : =₁ (s₁ ∘ p₂) max
s₁-p₂ = recognize-max _
  (s₁-d₂ ∙ ((comp-unitʳ s₁ ▷ d₂) ∙ coordinate-bottom s₁ upper-cocone))
  (s₁-d₀ ∙ ((collapse-coordinate s₁ s₁-d₁ s₁ ▷ d₀) ∙ coordinate-top s₁ upper-cocone))

j₀-p₀ : =₁ (j₀ ∘ p₀) (pair min pr₂)
j₀-p₀ = pair-cong s₀-p₀ s₁-p₀ ∙ pair-pre s₀ s₁ p₀
j₁-p₀ : =₁ (j₁ ∘ p₀) (pair pr₂ min)
j₁-p₀ = pair-cong s₁-p₀ s₀-p₀ ∙ pair-pre s₁ s₀ p₀
j₀-p₂ : =₁ (j₀ ∘ p₂) (pair pr₂ max)
j₀-p₂ = pair-cong s₀-p₂ s₁-p₂ ∙ pair-pre s₀ s₁ p₂
j₁-p₂ : =₁ (j₁ ∘ p₂) (pair max pr₂)
j₁-p₂ = pair-cong s₁-p₂ s₀-p₂ ∙ pair-pre s₁ s₀ p₂
```
