# Transposition respects isomorphic restrictions

We vary the restricting functor itself. Uncurrying first transports its
isomorphism to the product; naturality of product symmetry then moves it
to the other coordinate.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section08.SwapRestrictionNaturality as Swap
import SCT.VolumeI.Chapter01.Section02.FamilyProductFunctor as FP
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.PairingNaturality as PN

module SCT.VolumeI.Chapter01.Section08.TranspositionRestrictionNaturality
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section06.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.ComparisonSquares 𝒯 using (post-square)
open FP vocabulary terminal products productLaws composition vertical whiskering
  using (productFamily; productFamily-cong; productFamily-absolute)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; postWhisker-comp-at)
open PN vocabulary terminal products productLaws composition vertical whiskering using (move-square)

uncurry-restriction : {X A B E : CAT} (h : MAP B (Fun X E))
  {f g : MAP A B} (α : NatIso f g) →
  Iso₂ (funUncurry-pre h g ∙ funUncurryIso (h ◁ α))
    ((funUncurry h ◁ productMap-cong α (idIso (id X))) ∙ funUncurry-pre h f)
uncurry-restriction {X} h {f} {g} α =
  isoComp-cong (postWhisker (funUncurry h) ◁
    (productFamily-absolute α (idIso (id X)) ∙
      productFamily-cong (idIso α) (const-One (idIso (id X)))))
    (const-One (funUncurry-pre h f)) ∙
  (uncurry-pre-substitution h α ∙
    isoComp-cong (invIso (const-One (funUncurry-pre h g)))
      (invIso (uncurryFamily-absolute (h ◁ α))))

module Restriction {X A B E : CAT} {f g : MAP A B}
  (α : NatIso f g) (h : MAP B (Fun X E)) where
  S = swap {X} {A}
  T = swap {X} {B}
  e = funUncurry h
  Rf = productMap f (id X)
  Rg = productMap g (id X)
  Lf = productMap (id X) f
  Lg = productMap (id X) g
  Rα = productMap-cong α (idIso (id X))
  Lα = productMap-cong (idIso (id X)) α
  qf = funUncurry-pre h f
  qg = funUncurry-pre h g
  r₁f = qf ▷ S
  r₁g = qg ▷ S
  r₂f = comp-assoc S Rf e
  r₂g = comp-assoc S Rg e
  r₃f = e ◁ swap-restriction f
  r₃g = e ◁ swap-restriction g
  r₄f = invIso (comp-assoc Lf T e)
  r₄g = invIso (comp-assoc Lg T e)
  action₀ = funUncurryIso (h ◁ α) ▷ S
  action₁ = (e ◁ Rα) ▷ S
  action₂ = e ◁ (Rα ▷ S)
  action₃ = e ◁ (T ◁ Lα)
  action₄ = transpose h ◁ Lα

  abstract
    first : Iso₂ (r₁g ∙ action₀) (action₁ ∙ r₁f)
    first = preWhisker-isoComp-at (e ◁ Rα) qf S ∙
      ((preWhisker S ◁ uncurry-restriction h α) ∙
        invIso (preWhisker-isoComp-at qg (funUncurryIso (h ◁ α)) S))

    middle : Iso₂ (r₃g ∙ action₂) (action₃ ∙ r₃f)
    middle = post-square e (swap-restriction f) (swap-restriction g)
      (Rα ▷ S) (T ◁ Lα) (Swap.Naturality.comparison 𝒯 α)

    last : Iso₂ (r₄g ∙ action₃) (action₄ ∙ r₄f)
    last = move-square (comp-assoc Lg T e) action₄ action₃
      (comp-assoc Lf T e) (postWhisker-comp-at Lα T e)

    comparison : Iso₂ (transpose-pre g h ∙ transposeIso (h ◁ α))
      ((transpose h ◁ Lα) ∙ transpose-pre f h)
    comparison = paste-squares (r₃f ∙ (r₂f ∙ r₁f)) (r₃g ∙ (r₂g ∙ r₁g))
      r₄f r₄g action₀ action₃ action₄
      (paste-squares (r₂f ∙ r₁f) (r₂g ∙ r₁g) r₃f r₃g action₀ action₂ action₃
        (paste-squares r₁f r₁g r₂f r₂g action₀ action₁ action₂ first
          (whisker-mixed-at Rα S e)) middle) last ∙
      isoComp-cong (idIso (transpose-pre g h)) (transposeIso-at (h ◁ α))
```
