# Functors into the terminal category and out of the initial category

These are `lem:Functor_Category_Into_Terminal_Category` and
`lem:Functors_Out_Of_Empty_Category`. The latter uses the previously stated
strictness axiom only to identify a product with the initial category.
Both proofs test postcomposition by termination on mapping animae.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter01.Section07.Contractible
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section05.Initial 𝒯 M

open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingTests 𝒯 M F using (module Test)
open import SCT.VolumeI.Chapter01.Section04.EquivalenceDetection 𝒯 M using (post-tests-all)

maps-to-terminal-contractible : (T : CAT) → IsContractible (Map T One)
maps-to-terminal-contractible T = record
  { inverse = mapCurry one-isAn (terminate (One × T))
  ; sectionIso = mapReflect (map-isAn T One) _ _ (terminal-iso _ _)
  ; retractionIso = terminal-iso _ _ }

-- Any map between contractible categories is an equivalence. In the
-- application this is the actual postcomposition by termination.
contractible-map : {A B : CAT} (f : MAP A B) →
  IsContractible A → IsContractible B → IsEquiv f
contractible-map {B = B} f aContractible bContractible =
  equiv-cancel-left f (terminate B) bContractible
    (equiv-transport (terminal-iso _ _) aContractible)

fun-terminal-test : (T C : CAT) →
  IsEquiv (mapPost {C = T} (terminate (Fun C One)))
fun-terminal-test T C = contractible-map _
  (contractible-source (Test.forward T C One) (Test.forward-isEquiv T C One)
    (maps-to-terminal-contractible (T × C)))
  (maps-to-terminal-contractible T)

fun-terminal-contractible : (C : CAT) → IsContractible (Fun C One)
fun-terminal-contractible C = post-tests-all (terminate (Fun C One))
  (λ T → fun-terminal-test T C)

module FromInitial (I : InitialStructure) (S : StrictInitial I) where
  open Initiality I
  open Strictness I S

  fun-initial-test : (T D : CAT) →
    IsEquiv (mapPost {C = T} (terminate (Fun Zero D)))
  fun-initial-test T D = contractible-map _
    (contractible-source (Test.forward T Zero D) (Test.forward-isEquiv T Zero D)
      (contractible-source (mapPre (IsEquiv.inverse (product-zero-isEquiv T)))
        (mapPre-isEquiv (IsEquiv.inverse (product-zero-isEquiv T))
          (equiv-inverse (product-zero-isEquiv T)))
        (maps-from-zero-contractible D)))
    (maps-to-terminal-contractible T)

  fun-initial-contractible : (D : CAT) → IsContractible (Fun Zero D)
  fun-initial-contractible D = post-tests-all (terminate (Fun Zero D))
    (λ T → fun-initial-test T D)
```
