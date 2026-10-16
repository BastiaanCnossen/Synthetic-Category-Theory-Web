# Core inclusions for categories equivalent to animae

If a category C is equivalent to an anima A, its actual core inclusion
is an equivalence. Naturality identifies the composite of this inclusion
with the given equivalence C → A with a composite of two equivalences:
postcomposition on cores and the core inclusion of A. Cancellation gives
the result, without transferring the primitive anima predicate to C.

The calculation adapts the finite naturality and cancellation proof in the
historical Section01.EvaluationCalculus.CoreInclusions to the rebuilt
Chapter 1 APIs. The concrete application uses the specified intervalCore
copair and the existing anima witness for Core [1]. It asserts no anima
witness for the two-point category and no preservation of coproducts.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.CoreInclusions where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_⊔_)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; module Composition)
open Composition using (_∙_; _⁻¹)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-transport; equiv-compose; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (product-unitʳ-inverse)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (mapEval)
open import SCT.VolumeI.Chapter01.Section04.Functoriality
  using (mapPost; mapPost-β; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section04.Core
  using (Core; core-isAn; coreInclusion; core-evaluation; core-of-anima)
open import SCT.VolumeI.Chapter01.Section05.Coproducts using (_⊔_)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism
  using ([1]; intervalCore; intervalCore-isEquiv)

module _ {Γ : Context} where
  core-inclusion-natural : {C A : CAT Γ} (e : MAP C A)
    → (coreInclusion A ∘ mapPost {C = One} e) =₁ (e ∘ coreInclusion C)
  core-inclusion-natural {C} e =
    comp-assoc (product-unitʳ-inverse (Core C)) mapEval e ∙
      ((mapPost-β {C = One} e ▷ product-unitʳ-inverse (Core C)) ∙
        (core-evaluation (mapPost {C = One} e)) ⁻¹)

  core-inclusion-of-equivalent-anima : {C A : CAT Γ} (e : MAP C A)
    → IsEquiv e → isAn A → IsEquiv (coreInclusion C)
  core-inclusion-of-equivalent-anima {C} {A} e eEquiv aAn =
    equiv-cancel-left (coreInclusion C) e eEquiv
      (equiv-transport (core-inclusion-natural e)
        (equiv-compose (mapPost {C = One} e) (coreInclusion A)
          (mapPost-isEquiv {A = One} e eEquiv) (core-of-anima A aAn)))

  two-point-core-isEquiv : IsEquiv (coreInclusion (One ⊔ One))
  two-point-core-isEquiv = core-inclusion-of-equivalent-anima
    intervalCore intervalCore-isEquiv (core-isAn [1])
```
