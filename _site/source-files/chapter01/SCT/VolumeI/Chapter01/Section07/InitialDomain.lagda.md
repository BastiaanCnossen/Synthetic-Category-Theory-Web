# Functors from the initial category

Initiality and strictness are used separately. Strictness identifies
`T × Zero` with `Zero`; the chosen inverse transports the initial
identification, retaining its restriction triangle. Native reflection then
contracts `Fun Zero D` (`lem:Functors_Out_Of_Empty_Category`).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section07.InitialDomain where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-inverse)
open import SCT.VolumeI.Chapter01.Section03.Factorizations using (factor; triangle)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-preWhisker)
open import SCT.VolumeI.Chapter01.Section05.Initial
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying

module _ {Γ : Context} where
  zeroProductInverse : (T : CAT Γ) → MAP Zero (T × Zero)
  zeroProductInverse T = IsEquiv.inverse (product-zero-isEquiv T)

  initial-product-comparison : {T D : CAT Γ} (f g : MAP (T × Zero) D) → f =₁ g
  initial-product-comparison {T} f g = factor (factor-through-preWhisker (zeroProductInverse T)
    (equiv-inverse (product-zero-isEquiv T)) (initial-unique (f ∘ zeroProductInverse T) (g ∘ zeroProductInverse T)))

  initial-product-comparison-restriction : {T D : CAT Γ} (f g : MAP (T × Zero) D)
    → (initial-product-comparison f g ▷ zeroProductInverse T) =₂
        initial-unique (f ∘ zeroProductInverse T) (g ∘ zeroProductInverse T)
  initial-product-comparison-restriction {T} f g = triangle
    (factor-through-preWhisker (zeroProductInverse T) (equiv-inverse (product-zero-isEquiv T))
      (initial-unique (f ∘ zeroProductInverse T) (g ∘ zeroProductInverse T)))

  funInitialPoint : (D : CAT Γ) → MAP One (Fun Zero D)
  funInitialPoint D = funCurry {C = Zero} {D = D} (initiate D ∘ pr₂ {C = One} {D = Zero})

  funInitial-contraction-evaluation : (D : CAT Γ)
    → funUncurry {C = Zero} {D = D} (funInitialPoint D ∘ terminate (Fun Zero D)) =₁
        funUncurry {C = Zero} {D = D} (id (Fun Zero D))
  funInitial-contraction-evaluation D = initial-product-comparison _ _

  funInitial-contraction : (D : CAT Γ)
    → (funInitialPoint D ∘ terminate (Fun Zero D)) =₁ id (Fun Zero D)
  funInitial-contraction D = reflect (funEval {C = Zero} {D = D}) (funUniversal Zero D) _ _
    (funInitial-contraction-evaluation D)

  funInitial-contraction-image : (D : CAT Γ)
    → evaluate-cong (funEval {C = Zero} {D = D}) (funInitial-contraction D) =₂
        funInitial-contraction-evaluation D
  funInitial-contraction-image D = reflect-β-One (funEval {C = Zero} {D = D}) (funUniversal Zero D) _ _
    (funInitial-contraction-evaluation D)

  funInitial-isEquiv : (D : CAT Γ) → IsEquiv (terminate (Fun Zero D))
  funInitial-isEquiv D = record
    { inverse = funInitialPoint D
    ; left-inverse-law = (funInitial-contraction D) ⁻¹
    ; right-inverse-law = terminal-identification _ _ }
```
