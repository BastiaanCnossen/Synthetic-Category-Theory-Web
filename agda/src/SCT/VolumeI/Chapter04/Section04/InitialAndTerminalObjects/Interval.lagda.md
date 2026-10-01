# Universal endpoints and the three contractible hom categories

For `lem:Interval_Has_Terminal_Object`, the required initial and terminal
objects are exactly the existing interval-endpoint axiom. Pulling back
their slice projections gives `cor:Hom_Spaces_[1]`.

For a general category, the same argument is
`rmk:Unique_Morphism_From_Initial_Object`. No converse by testing
absolute objects is used.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints

module SCT.VolumeI.Chapter04.Section04.InitialAndTerminalObjects.Interval
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I) where

open import SCT.VolumeI.Chapter02.Section01.HomAndSlices 𝒯 M ℱ P I public
open import SCT.VolumeI.Chapter02.Section01.DiagramCalculus.SliceFibers 𝒯 M ℱ P I
  using (initial-hom-contractible; terminal-hom-contractible)
open Endpoints.IntervalEndpoints E

zero-initial : IsInitial zero
zero-initial = zero-isInitial

one-terminal : IsTerminal one
one-terminal = one-isTerminal

hom₀₀-contractible : IsContractible (Hom [1] zero zero)
hom₀₀-contractible = initial-hom-contractible zero zero-initial zero

hom₀₁-contractible : IsContractible (Hom [1] zero one)
hom₀₁-contractible = initial-hom-contractible zero zero-initial one

hom₁₁-contractible : IsContractible (Hom [1] one one)
hom₁₁-contractible = terminal-hom-contractible one one-terminal one

arrows-from-initial : {C : CAT} (x : Obj-abs C) → IsInitial x →
  (y : Obj-abs C) → IsContractible (Hom C x y)
arrows-from-initial = initial-hom-contractible

arrows-to-terminal : {C : CAT} (x : Obj-abs C) → IsTerminal x →
  (y : Obj-abs C) → IsContractible (Hom C y x)
arrows-to-terminal = terminal-hom-contractible
```

