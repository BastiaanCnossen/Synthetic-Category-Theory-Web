# Exponentiable functors

This is `def:Exponentiable_Functor`. Dependent products must exist after
every base change, and the constructed Beck–Chevalley map must be an
equivalence after a further base change. The second condition is stated
for the supplied dependent products, retaining their evaluation maps.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalley 𝒯 M ℱ P using (module BeckChevalley)
open import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeSquares 𝒯 P using (module Successive)

record IsExponentiable {S T : CAT} (p : MAP S T) : Set (c ⊔ m) where
  field
    over-base-change : {S′ T′ : CAT} (b : MAP T′ T) (square : Cone p b S′) →
      IsPullback square → {C : CAT} (f : MAP C S′) → DependentProduct (Cone.right square) f

    beck-chevalley : {S′ T′ S″ T″ : CAT} (b : MAP T′ T) (first : Cone p b S′) →
      IsPullback first → (b′ : MAP T″ T′) (second : Cone (Cone.right first) b′ S″) →
      IsPullback second → {C : CAT} (f : MAP C S′)
      (Π : DependentProduct (Cone.right first) f)
      (Π′ : DependentProduct (Cone.right second) (pullback₂ {f = f} {Cone.left second})) →
      IsEquiv (BeckChevalley.functor (Cone.right first) b′ second f Π Π′)

module Exponentiable {S T : CAT} {p : MAP S T} (ep : IsExponentiable p) where
  identity-square : Cone p (id T) S
  identity-square = record
    { left = id S ; right = p
    ; match = (comp-unitˡ p) ⁻¹ ∙ comp-unitʳ p }

  identity-square-isPullback : IsPullback identity-square
  identity-square-isPullback = degenerate-pullback (id-isEquiv T) identity-square (id-isEquiv S)

  dependent-product : {C : CAT} (f : MAP C S) → DependentProduct p f
  dependent-product = IsExponentiable.over-base-change ep (id T) identity-square identity-square-isPullback

  module AfterBaseChange {S′ T′ : CAT} (b : MAP T′ T) (first : Cone p b S′)
    (first-isPullback : IsPullback first) where

    abstract
      isExponentiable : IsExponentiable (Cone.right first)
      isExponentiable = record
        { over-base-change = λ b′ second e₂ f → IsExponentiable.over-base-change ep (b ∘ b′)
            (Successive.composite p b first b′ second)
            (Successive.composite-isPullback p b first b′ second first-isPullback e₂) f
        ; beck-chevalley = λ b′ second e₂ b″ third e₃ f Π Π′ →
            IsExponentiable.beck-chevalley ep (b ∘ b′)
              (Successive.composite p b first b′ second)
              (Successive.composite-isPullback p b first b′ second first-isPullback e₂)
              b″ third e₃ f Π Π′ }
```

Closure under base change uses the ordinary pasting theorem for
pullback squares. No new closure axiom is assumed.
