# When the two-point coproduct is contractible

This proves `lem:2_Contractible_Implies_Everything_Contractible`.
Disjointness makes the initial anima contractible. Strictness then makes
every category contractible.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section05.Setup as Setup
import SCT.VolumeI.Chapter01.Section05.Initial as Initial
import SCT.VolumeI.Chapter01.Section05.Coproducts as Coproducts
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section06.UniversalCoproducts as Universality

module SCT.VolumeI.Chapter01.Section06.ContractibleCoproduct
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (I : Initial.InitialStructure 𝒯 M) (S : Initial.StrictInitial 𝒯 M I)
  (B : Coproducts.CoproductStructure 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (U : Universality.CoproductUniversality 𝒯 M B P) where

open Setup 𝒯 M
open Initial.Initiality 𝒯 M I
open Initial.StrictInitial S
open Coproducts.CoproductStructure B
open import SCT.VolumeI.Chapter01.Section06.DisjointCoproducts 𝒯 M I B P U
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P

two-contractible-implies-all : IsContractible (One ⊔ One) → (C : CAT) → IsContractible C
two-contractible-implies-all e C = equiv-transport (terminal-iso _ _)
  (equiv-compose toZero (initiate One) (into-zero-isEquiv toZero) zeroContractible)
  where
  leftEquivalence : IsEquiv (in₁ {One} {One})
  leftEquivalence = equiv-cancel-left in₁ (terminate (One ⊔ One)) e
    (equiv-transport (terminal-iso _ _) (id-isEquiv One))
  zeroContractible : IsEquiv (initiate One)
  zeroContractible = degenerate-pullback-converse leftEquivalence (disjointCone One One)
    (disjoint-isPullback One One)
  toZero = IsEquiv.inverse zeroContractible ∘ terminate C

all-contractible-implies-two : ((C : CAT) → IsContractible C) → IsContractible (One ⊔ One)
all-contractible-implies-two all = all (One ⊔ One)
```
