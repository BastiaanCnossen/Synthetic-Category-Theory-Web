# Equivalences and dependent products and sums

Both dependent operations send equivalences to equivalences. The proofs
apply their constructed actions to an inverse and its two identifications.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
open import SCT.VolumeI.Chapter05.Section01.Core
import SCT.VolumeI.Chapter05.Section02.DependentProducts as Products
import SCT.VolumeI.Chapter05.Section02.DependentSums as Sums
import SCT.VolumeI.Chapter05.Section02.ProductFunctoriality as ProductAction
import SCT.VolumeI.Chapter05.Section02.SumFunctoriality as SumAction

module SCT.VolumeI.Chapter05.Section02.DependentEquivalences
  {l : Level} {S T : Theory l l l} (W : Weakening S T)
  (P : Products.DependentProducts W) where

private
  module S = View S
  module T = View T
open Products.DependentProducts P
open ProductAction W P
open S using (_∙_; _⁻¹)

Π-map-isEquiv : {B C : T.CAT} {f : T.MAP B C}
  → T.IsEquiv f → S.IsEquiv (Π-map f)
Π-map-isEquiv {B} {C} {f} e = record
  { inverse = Π-map (T.IsEquiv.inverse e)
  ; sectionIso = Π-map-comp f (T.IsEquiv.inverse e) ∙
      (Π-map-cong (T.IsEquiv.sectionIso e) ∙ (Π-map-id B) ⁻¹)
  ; retractionIso = Π-map-comp (T.IsEquiv.inverse e) f ∙
      (Π-map-cong (T.IsEquiv.retractionIso e) ∙ (Π-map-id C) ⁻¹) }

Π-equiv : {B C : T.CAT} → T.Equiv B C → S.Equiv (Π B) (Π C)
Π-equiv e = record { functor = Π-map (T.Equiv.functor e)
  ; isEquiv = Π-map-isEquiv (T.Equiv.isEquiv e) }

module SumResults (Q : Sums.DependentSums W P) where
  open Sums.DependentSums Q
  open SumAction W P Q

  Σ-map-isEquiv : {B C : T.CAT} {f : T.MAP B C}
    → T.IsEquiv f → S.IsEquiv (Σ-map f)
  Σ-map-isEquiv {B} {C} {f} e = record
    { inverse = Σ-map (T.IsEquiv.inverse e)
    ; sectionIso = Σ-map-comp f (T.IsEquiv.inverse e) ∙
        (Σ-map-cong (T.IsEquiv.sectionIso e) ∙ (Σ-map-id B) ⁻¹)
    ; retractionIso = Σ-map-comp (T.IsEquiv.inverse e) f ∙
        (Σ-map-cong (T.IsEquiv.retractionIso e) ∙ (Σ-map-id C) ⁻¹) }

  Σ-equiv : {B C : T.CAT} → T.Equiv B C → S.Equiv (Σ B) (Σ C)
  Σ-equiv e = record { functor = Σ-map (T.Equiv.functor e)
    ; isEquiv = Σ-map-isEquiv (T.Equiv.isEquiv e) }
```
