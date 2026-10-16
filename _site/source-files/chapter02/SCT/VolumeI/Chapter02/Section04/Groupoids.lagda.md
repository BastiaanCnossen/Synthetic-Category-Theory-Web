# Groupoids and constant arrows

The working groupoid condition says that the actual constant-arrow functor
is an equivalence. A section supplies the missing inverse, since evaluation
at the source already gives a retraction. Conversely an equivalence supplies
a section.

If source evaluation is an equivalence, its composite with the constant-arrow
functor identifies with the identity, so cancellation gives the groupoid
condition. Applied to the empty category, strict initiality provides precisely
that evaluation equivalence. This proves the empty category is a groupoid
without asserting that it is an anima.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.Groupoids where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (Section; Retraction; section-retraction-isEquiv; equiv-section;
    equiv-cancel-left; equiv-transport; id-isEquiv)
open import SCT.VolumeI.Chapter01.Section05.Initial using (Zero; into-zero-isEquiv)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (identityArrow; ev₀; identity-source)

module _ {Γ : Context} where
  IsGroupoid : CAT Γ → Set m
  IsGroupoid C = IsEquiv (identityArrow {C = C})

  identity-section-to-groupoid : {C : CAT Γ}
    → Section (identityArrow {C = C}) → IsGroupoid C
  identity-section-to-groupoid {C} given = section-retraction-isEquiv given
    (record { retraction = ev₀ {C = C} ; retraction-law = (identity-source {C = C}) ⁻¹ })

  groupoid-to-identity-section : {C : CAT Γ}
    → IsGroupoid C → Section (identityArrow {C = C})
  groupoid-to-identity-section {C} = equiv-section {f = identityArrow {C = C}}

  groupoid-from-source-equivalence : {C : CAT Γ}
    → IsEquiv (ev₀ {C = C}) → IsGroupoid C
  groupoid-from-source-equivalence {C} given =
    equiv-cancel-left (identityArrow {C = C}) (ev₀ {C = C}) given
      (equiv-transport ((identity-source {C = C}) ⁻¹) (id-isEquiv C))

  empty-isGroupoid : IsGroupoid (Zero {Γ = Γ})
  empty-isGroupoid = groupoid-from-source-equivalence {C = Zero {Γ = Γ}}
    (into-zero-isEquiv (ev₀ {C = Zero {Γ = Γ}}))
```
