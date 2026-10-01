# Insertion and successive changes of parameter

We compare insertion after a composite parameter change with the pasted
insertion squares. Each coordinate retains its chosen projection witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterSecondCoordinate as Second
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ParameterFirstCoordinate as First
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductFirstCoordinate as FirstBase
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionProjectionWitnesses as Witnesses
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionParameterComposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ hiding (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M using (slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-compose)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ParameterSquarePasting 𝒯 using (paste)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate 𝒯 M using (parameter-base)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect; cancel-right)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯 using (section-image; section-pre; section-comp)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (change-middle)
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (left-unitor-comp)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
module PS = Projection 𝒯
  using (Square; compose-base; compose-square; lift-base; lift-compose; lift-square; pre-square; module Pasting)

module At {X Y Z A : CAT} (x : Obj-abs A) (h : MAP X Y) (k : MAP Y Z) where
  H = productMap h (id A)
  K = productMap k (id A)
  KH = productMap (k ∘ h) (id A)
  κ = slice-comparison {C = A} k h
  short = (κ ▷ insert x) ∙ paste (insert-natural k x) (insert-natural h x)
  long = insert-natural (k ∘ h) x

  module FirstProjection where
    bx = pair-β₁ (id X) (const x)
    by = pair-β₁ (id Y) (const x)
    bz = pair-β₁ (id Z) (const x)
    baseH = FirstBase.parameter-base 𝒯 M h A
    baseK = FirstBase.parameter-base 𝒯 M k A
    baseKH = FirstBase.parameter-base 𝒯 M (k ∘ h) A
    overH = First.parameter-over 𝒯 M h k A
    overX = PS.lift-base k (h ∘ pr₁) (insert x) (section-image pr₁ (insert x) bx h)
    overY = section-image pr₁ (insert x) by k
    module Diagram = PS.Pasting (k ∘ h) k (id Z)
      (k ∘ (h ∘ pr₁)) (k ∘ pr₁) pr₁
      (insert x) (insert x) (insert x) h k H K
      (idIso (k ∘ h)) (comp-unitˡ k) overH baseK overX overY bz
      (insert-natural h x) (insert-natural k x)
    final = PS.compose-base pr₁ KH (comp-assoc pr₁ h k ∙ baseKH) (insert x) overX

    abstract
      first-square : PS.Square (k ∘ pr₁)
        (PS.compose-base (k ∘ pr₁) (insert x) overY h (idIso (k ∘ h)))
        (PS.compose-base (k ∘ pr₁) H overH (insert x) overX) (insert-natural h x)
      first-square = (section-pre pr₁ (insert x) by h k) ⁻¹ ∙
        (PS.lift-square k pr₁
          (Witnesses.Parameter.incoming₁ 𝒯 M ℱ h x)
          (Witnesses.Parameter.outgoing₁ 𝒯 M ℱ h x) (insert-natural h x)
          (Witnesses.Parameter.projection₁ 𝒯 M ℱ h x) ∙
        isoComp-cong
          (PS.lift-compose k pr₁ H (insert x) baseH (section-image pr₁ (insert x) bx h))
          (idIso ((k ∘ pr₁) ◁ insert-natural h x)))

      source-unit : (PS.compose-base (id Z) k (comp-unitˡ k) h (idIso (k ∘ h))) =₂
        (comp-unitˡ (k ∘ h))
      source-unit = cancel-right (comp-assoc h k (id Z)) (comp-unitˡ (k ∘ h)) ∙
        (isoComp-cong ((left-unitor-comp h k) ⁻¹) (idIso ((comp-assoc h k (id Z)) ⁻¹)) ∙
          isoComp-unitˡ-at _)

      source-normalization : Diagram.b₀ =₂ Witnesses.Parameter.incoming₁ 𝒯 M ℱ (k ∘ h) x
      source-normalization = isoComp-cong source-unit (idIso _)

      target-normalization : final =₂ Witnesses.Parameter.outgoing₁ 𝒯 M ℱ (k ∘ h) x
      target-normalization = isoComp-unitˡ-at _ ∙
        change-middle pr₁ KH (insert x) baseKH (section-image pr₁ (insert x) bx (k ∘ h))
          (comp-assoc pr₁ h k) overX (idIso (k ∘ h))
          (section-comp pr₁ (insert x) bx h k ∙ isoComp-unitˡ-at _)

      short-square : PS.Square pr₁ Diagram.b₀ final short
      short-square = PS.compose-square pr₁ Diagram.b₀ Diagram.b₅ final
        (κ ▷ insert x) (paste (insert-natural k x) (insert-natural h x))
        (PS.pre-square pr₁ (insert x) _ _ overX κ (First.compositor 𝒯 M h k A))
        (Diagram.paste-square first-square (Witnesses.Parameter.projection₁ 𝒯 M ℱ k x))

      long-square : PS.Square pr₁ Diagram.b₀ final long
      long-square = source-normalization ⁻¹ ∙
        (Witnesses.Parameter.projection₁ 𝒯 M ℱ (k ∘ h) x ∙
          isoComp-cong target-normalization (idIso (pr₁ ◁ long)))

      comparison : (pr₁ ◁ long) =₂ (pr₁ ◁ short)
      comparison = cancel-left-reflect final (short-square ⁻¹ ∙ long-square)

  module SecondProjection where
    bx = pair-β₂ (id X) (const x)
    by = pair-β₂ (id Y) (const x)
    bz = pair-β₂ (id Z) (const x)
    module Diagram = PS.Pasting (const x) (const x) (const x) pr₂ pr₂ pr₂
      (insert x) (insert x) (insert x) h k H K
      (const-pre x h) (const-pre x k) (parameter-base h A) (parameter-base k A)
      bx by bz (insert-natural h x) (insert-natural k x)
    final = PS.compose-base pr₂ KH (parameter-base (k ∘ h) A) (insert x) bx

    abstract
      source-normalization : Diagram.b₀ =₂ Witnesses.Parameter.incoming₂ 𝒯 M ℱ (k ∘ h) x
      source-normalization = isoComp-cong (const-pre-compose x h k) (idIso _)

      short-square : PS.Square pr₂ Diagram.b₀ final short
      short-square = PS.compose-square pr₂ Diagram.b₀ Diagram.b₅ final
        (κ ▷ insert x) (paste (insert-natural k x) (insert-natural h x))
        (PS.pre-square pr₂ (insert x) _ _ bx κ (Second.compositor 𝒯 M h k A))
        (Diagram.paste-square
          (Witnesses.Parameter.normalized-projection₂ 𝒯 M ℱ h x)
          (Witnesses.Parameter.normalized-projection₂ 𝒯 M ℱ k x))

      long-square : PS.Square pr₂ Diagram.b₀ final long
      long-square = source-normalization ⁻¹ ∙
        Witnesses.Parameter.normalized-projection₂ 𝒯 M ℱ (k ∘ h) x

      comparison : (pr₂ ◁ long) =₂ (pr₂ ◁ short)
      comparison = cancel-left-reflect final (short-square ⁻¹ ∙ long-square)

  abstract
    comparison : long =₂ short
    comparison = pair-iso-extensionality FirstProjection.comparison SecondProjection.comparison
```
