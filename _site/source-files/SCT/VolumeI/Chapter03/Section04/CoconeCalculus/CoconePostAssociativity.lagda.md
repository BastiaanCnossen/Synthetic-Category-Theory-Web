# Associativity of postcomposition on cocones

The ordinary associators compare postcomposition by a composite with
successive postcomposition. The coordinate associativity law supplies
the compatibility with the cocone matching.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.CoconePostAssociativity
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.CoconeCalculus.CoconePostcomposition 𝒯 using (coconePost)
open import SCT.VolumeI.Chapter01.Section04.ProductCalculus.ProductSubstitution 𝒯 M using (coordinate-outer-comp)

coconePost-assoc : {A B C D E K : CAT} {u : MAP A B} {v : MAP A C}
  (s : Cocone u v D) (F : MAP D E) (G : MAP E K) →
  CoconeIso (coconePost (G ∘ F) s) (coconePost G (coconePost F s))
coconePost-assoc {u = u} {v} s F G = record
  { leftIso = comp-assoc (Cocone.left s) F G
  ; rightIso = comp-assoc (Cocone.right s) F G
  ; compatible = (coordinate-outer-comp v (Cocone.right s) (Cocone.left s) u (Cocone.match s) F G) ⁻¹ }
```
