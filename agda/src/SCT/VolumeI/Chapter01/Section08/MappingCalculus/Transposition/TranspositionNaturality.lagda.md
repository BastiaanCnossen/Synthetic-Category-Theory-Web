# Naturality of transposition under restriction

Transposition carries precomposition by `u` to restriction along
`id × u`. The following square retains the specified symmetry comparison
and is natural on a whole anima of identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Parameterized as Parameterized
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.FamilyNaturality as FN

module SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.TranspositionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.MappingCalculus.Transposition.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.Substitution.DecodingNaturality 𝒯 M using (pre-family-square)
open FP vocabulary terminal products productLaws composition vertical whiskering using (paste-family-squares)
open Parameterized.WhiskeringLaws vocabulary terminal products productLaws composition vertical whiskering using (preWhisker-comp-general)
open FN vocabulary terminal products productLaws composition vertical whiskering
  using (family-interchange-fixedInner; family-move-square)

transposeFamily : {K X C E : CAT} {f g : MAP C (Fun X E)} →
  MAP K (f ＝ g) → MAP K (transpose f ＝ transpose g)
transposeFamily γ = uncurryFamily γ ▷ swap

transposeFamily-at : {K X C E : CAT} {f g : MAP C (Fun X E)} (γ : MAP K (f ＝ g)) →
  (transpose-isoMap f g ∘ γ) =₁ (transposeFamily γ)
transposeFamily-at {f = f} {g} γ = (preWhisker swap ◁ uncurryFamily-at γ) ∙
  comp-assoc γ (funUncurry-isoMap f g) (preWhisker swap)

transpose-pre-family : {K X A B E : CAT} (i : MAP A B)
  {f g : MAP B (Fun X E)} (γ : MAP K (f ＝ g)) →
  (const (transpose-pre i g) ∙ transposeFamily (γ ▷ i)) =₁
    ((transposeFamily γ ▷ productMap (id X) i) ∙ const (transpose-pre i f))
transpose-pre-family {X = X} i {f} {g} γ =
  paste-family-squares (r₃f ∙ (r₂f ∙ r₁f)) (r₃g ∙ (r₂g ∙ r₁g)) r₄f r₄g action₀ action₃ action₄
    (paste-family-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) r₃f r₃g action₀ action₂ action₃
      (paste-family-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂
        (pre-family-square swap (funUncurry-restrict f i) (funUncurry-restrict g i)
          (uncurryFamily (γ ▷ i)) (uncurryFamily γ ▷ L) (uncurry-restrict-inputs γ i))
        (preWhisker-comp-general (uncurryFamily γ) L swap))
      ((family-interchange-fixedInner (uncurryFamily γ) (swap-restriction i)) ⁻¹))
    (family-move-square (comp-assoc R swap (funUncurry g)) action₄ action₃
      (comp-assoc R swap (funUncurry f))
      (preWhisker-comp-general (uncurryFamily γ) swap R))
  where
  L = productMap i (id X)
  R = productMap (id X) i
  r₁f = funUncurry-restrict f i ▷ swap
  r₁g = funUncurry-restrict g i ▷ swap
  r₂f = comp-assoc swap L (funUncurry f)
  r₂g = comp-assoc swap L (funUncurry g)
  r₃f = funUncurry f ◁ swap-restriction i
  r₃g = funUncurry g ◁ swap-restriction i
  r₄f = (comp-assoc R swap (funUncurry f)) ⁻¹
  r₄g = (comp-assoc R swap (funUncurry g)) ⁻¹
  action₀ = transposeFamily (γ ▷ i)
  action₁ = (uncurryFamily γ ▷ L) ▷ swap
  action₂ = uncurryFamily γ ▷ (L ∘ swap)
  action₃ = uncurryFamily γ ▷ (swap ∘ R)
  action₄ = transposeFamily γ ▷ R

transpose-pre-natural : {X A B E : CAT} (i : MAP A B)
  {f g : MAP B (Fun X E)} (γ : f =₁ g) →
  (transpose-pre i g ∙ transposeIso (γ ▷ i)) =₂
    ((transposeIso γ ▷ productMap (id X) i) ∙ transpose-pre i f)
transpose-pre-natural {X} i {f} {g} γ =
  isoComp-cong (preWhisker (productMap (id X) i) ◁ (transposeFamily-at γ) ⁻¹)
    (const-One (transpose-pre i f)) ∙
  (transpose-pre-family i γ ∙
    isoComp-cong ((const-One (transpose-pre i g)) ⁻¹) (transposeFamily-at (γ ▷ i)))
```
