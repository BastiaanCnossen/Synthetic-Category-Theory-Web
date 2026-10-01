# Composition of relative adjoint sections

Composing relative adjunctions preserves invertibility of the relevant
unit or counit. Consequently relative left and right adjoint sections
are closed under composition, with the specified base triangles retained.

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

module SCT.VolumeI.Chapter04.Section04.RelativeSectionComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (S : Segal.SegalAxiom 𝒯 M ℱ P I E)
  (Q : Squares.CommutativeSquareAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter04.Section04.RelativeComposition 𝒯 M ℱ P I E S Q public

compose-relative-left-adjoint-section : {C D T B : CAT}
  {p : MAP C B} {q : MAP D B} {t : MAP T B}
  {f : FunctorOver p q} {g : FunctorOver q t} {u : FunctorOver q p} {v : FunctorOver t q} →
  RelativeLeftAdjointSection p q f u → RelativeLeftAdjointSection q t g v →
  RelativeLeftAdjointSection p t (compose-over g f) (compose-over u v)
compose-relative-left-adjoint-section ea eb = record
  { relative-adjunction = Composite.adjunction B.relative-adjunction A.relative-adjunction
  ; unit-invertible = Composite.unit-invertible B.relative-adjunction A.relative-adjunction
      B.unit-invertible A.unit-invertible }
  where
    module A = RelativeLeftAdjointSection ea
    module B = RelativeLeftAdjointSection eb

compose-relative-right-adjoint-section : {C D T B : CAT}
  {p : MAP C B} {q : MAP D B} {t : MAP T B}
  {f : FunctorOver p q} {g : FunctorOver q t} {u : FunctorOver q p} {v : FunctorOver t q} →
  RelativeRightAdjointSection p q f u → RelativeRightAdjointSection q t g v →
  RelativeRightAdjointSection p t (compose-over g f) (compose-over u v)
compose-relative-right-adjoint-section ea eb = record
  { relative-adjunction = Composite.adjunction A.relative-adjunction B.relative-adjunction
  ; counit-invertible = Composite.counit-invertible A.relative-adjunction B.relative-adjunction
      A.counit-invertible B.counit-invertible }
  where
    module A = RelativeRightAdjointSection ea
    module B = RelativeRightAdjointSection eb
```
