# Functors into the terminal category and out of the initial category

These are `lem:Functor_Category_Into_Terminal_Category` and
`lem:Functors_Out_Of_Empty_Category`. The latter uses the previously stated
strictness axiom only to identify a product with the initial category.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section06.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section06.Contractible
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section06.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section04.Initial 𝒯 M

fun-terminal-contractible : (C : CAT) → IsContractible (Fun C One)
fun-terminal-contractible C = record
  { inverse = funCurry (terminate (One × C))
  ; sectionIso = funReflect _ _ (terminal-iso _ _)
  ; retractionIso = terminal-iso _ _ }

module FromInitial (I : InitialStructure) (S : StrictInitial I) where
  open Initiality I
  open Strictness I S

  empty-domain-iso : {X D : CAT} (f g : MAP (X × Zero) D) → NatIso f g
  empty-domain-iso {X} f g = FunctorLift.lift (preWhisker-lift
    (IsEquiv.inverse (product-zero-isEquiv X)) (equiv-inverse (product-zero-isEquiv X))
    (initial-iso _ _))

  fun-initial-contractible : (D : CAT) → IsContractible (Fun Zero D)
  fun-initial-contractible D = record
    { inverse = funCurry (initiate D ∘ pr₂)
    ; sectionIso = funReflect _ _ (empty-domain-iso _ _)
    ; retractionIso = terminal-iso _ _ }
```

