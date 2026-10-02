# Equivalences of operations on parameterized morphisms

Package two operations together with their inverse comparisons. The
realization theorem turns these data into an equivalence of endpoint
pullbacks. An abstract inhabitant of this record can hide expensive
expression formulas without hiding their laws.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking

module SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperationEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) where

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I public

open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionFamilyEquivalences 𝒯 M ℱ I
  using (FamilyEquivalence; represented)

record ExpressionOperationEquivalence {B C D : CAT}
  (u v : MAP B C) (s t : MAP B D) : Set (c ⊔ m) where
  field
    forward : ExpressionOperation u v s t
    backward : ExpressionOperation s t u v
    backward-forward : {Γ : CAT} (b : MAP Γ B) (f : MorphismExpression (u ∘ b) (v ∘ b)) →
      ExpressionIso (ExpressionOperation.apply backward b (ExpressionOperation.apply forward b f)) f
    forward-backward : {Γ : CAT} (b : MAP Γ B) (g : MorphismExpression (s ∘ b) (t ∘ b)) →
      ExpressionIso (ExpressionOperation.apply forward b (ExpressionOperation.apply backward b g)) g

  open EquivalenceOperations forward backward backward-forward forward-backward public
    using (isEquiv; equivalence)
from-family-equivalence : {B C D : CAT} {u v : MAP B C} {s t : MAP B D} →
  FamilyEquivalence (represented u) (represented v) (represented s) (represented t) →
  ExpressionOperationEquivalence u v s t
from-family-equivalence e = record
  { forward = from-family-operation E.forward
  ; backward = from-family-operation E.backward
  ; backward-forward = E.backward-forward ; forward-backward = E.forward-backward }
  where module E = FamilyEquivalence e
```
