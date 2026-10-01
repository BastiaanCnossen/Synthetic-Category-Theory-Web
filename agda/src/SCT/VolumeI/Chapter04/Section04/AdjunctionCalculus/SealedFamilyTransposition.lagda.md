# The parameterized transposition package

The family operations, their restriction and endpoint-change laws, and
their inverse equations are constructed from the adjunction calculus.
Keeping the assembled value abstract prevents its clients from expanding
the nested Segal and endpoint-pullback constructions during conversion.
The two computation comparisons expose the original formulas explicitly
without making clients unfold the whole equivalence package.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section02.SegalAxiom as Segal
import SCT.VolumeI.Chapter02.Section01.CommutativeSquareAxiom as Squares

module SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.SealedFamilyTransposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.Adjunctions 𝒯 M ℱ P I E S public
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperationEquivalences 𝒯 M ℱ P I public
  using (ExpressionOperationEquivalence)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.EndpointFiberOperations 𝒯 M ℱ P I
  using (ExpressionOperation)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ExpressionIdentifications 𝒯 M ℱ I
  using (expressionIso-id)
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilies as Families
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyRestriction as Restriction
import SCT.VolumeI.Chapter04.Section04.AdjunctionCalculus.TransposeFamilyInverses as Inverses

abstract
  transposition : {B C D : CAT} {l : MAP C D} {r : MAP D C}
    (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) →
    ExpressionOperationEquivalence (l ∘ x) y x (r ∘ y)
  transposition adj x y = record
    { forward = record
        { apply = F.forward ; on-comparison = F.forward-cong
        ; on-restriction = R.forward-restrict ; on-change = F.forward-change }
    ; backward = record
        { apply = F.backward ; on-comparison = F.backward-cong
        ; on-restriction = R.backward-restrict ; on-change = F.backward-change }
    ; backward-forward = V.backward-forward
    ; forward-backward = V.forward-backward
    }
    where
    module F = Families.Families 𝒯 M ℱ P I E S adj x y
      using (forward; forward-cong; forward-change; backward; backward-cong; backward-change)
    module R = Restriction.RestrictionFamilies 𝒯 M ℱ P I E S adj x y
      using (forward-restrict; backward-restrict)
    module V = Inverses.InverseFamilies 𝒯 M ℱ P I E S Q adj x y
      using (backward-forward; forward-backward)

  forward-computation : {B C D Γ : CAT} {l : MAP C D} {r : MAP D C}
    (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) (b : MAP Γ B)
    (f : MorphismExpression ((l ∘ x) ∘ b) (y ∘ b)) →
    ExpressionIso
      (ExpressionOperation.apply (ExpressionOperationEquivalence.forward (transposition adj x y)) b f)
      (Families.Families.forward 𝒯 M ℱ P I E S adj x y b f)
  forward-computation adj x y b f = expressionIso-id _

  backward-computation : {B C D Γ : CAT} {l : MAP C D} {r : MAP D C}
    (adj : Adjunction l r) (x : MAP B C) (y : MAP B D) (b : MAP Γ B)
    (f : MorphismExpression (x ∘ b) ((r ∘ y) ∘ b)) →
    ExpressionIso
      (ExpressionOperation.apply (ExpressionOperationEquivalence.backward (transposition adj x y)) b f)
      (Families.Families.backward 𝒯 M ℱ P I E S adj x y b f)
  backward-computation adj x y b f = expressionIso-id _
```
