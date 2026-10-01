# Transposition as an equivalence of framed expressions

Package the checked transposition operations, comparison laws, and
inverse equations behind an abstract value. Its public fields allow
downstream proofs to use the laws without unfolding the Segal and
pullback constructions inside the operations. The package is constructed
from the existing adjunction data and adds no assumption.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedTransposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeIdentifications as Inverses
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeComparisons as Comparisons

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionEquivalences 𝒯 M ℱ I public
  using (ExpressionEquivalence)

abstract
  transposition : {Γ C D : CAT} {l : MAP C D} {r : MAP D C}
    (adj : Adjunction l r) (x : MAP Γ C) (y : MAP Γ D) →
    ExpressionEquivalence (l ∘ x) y x (r ∘ y)
  transposition adj x y = record
    { forward = A.transpose x y
    ; backward = A.untranspose x y
    ; forward-cong = N.transpose-cong x y
    ; backward-cong = N.untranspose-cong x y
    ; backward-forward = V.untranspose-transpose x y
    ; forward-backward = V.transpose-untranspose x y
    }
    where
    module A = Adjunction adj
    module N = Comparisons.Comparisons 𝒯 M ℱ P I E S adj
    module V = Inverses.InverseLaws 𝒯 M ℱ P I E S Q adj
```
