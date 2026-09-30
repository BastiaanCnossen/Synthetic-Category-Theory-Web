# Restriction along a functor over the base

Precomposition acts on the defining pullbacks of relative functor
categories. Its two squares retain the supplied triangle and the
precomposition/postcomposition interchange. If the source functor is an
equivalence, so is this restriction functor.

The interchange is chosen by its uncurried image. The final computation
rule exposes that image for subsequent comparisons of whole families.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Composition.Precomposition
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost; mapPost-isEquiv)
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramNames 𝒯 M ℱ
  using (nameFun; name-cong; named-restriction)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Interchange {A B C S : CAT} (e : MAP A B) (f : MAP C S) where
  left = funPost {C = A} f ∘ funPre {D = C} e
  right = funPre {D = S} e ∘ funPost {C = B} f
  R : MAP (Fun B C × A) (Fun B C × B)
  R = productMap (id (Fun B C)) e

  raw : funUncurry left =₁ funUncurry right
  raw = (funPre-uncurry e (funPost f)) ⁻¹ ∙
    (((funPost-β f ▷ R) ⁻¹) ∙
      ((comp-assoc R funEval f) ⁻¹ ∙
        ((f ◁ funPre-β e) ∙ funPost-uncurry f (funPre e))))

  comparison : left =₁ right
  comparison = funIsoReflect left right raw

  comparison-image : funUncurryIso comparison =₂ raw
  comparison-image = funIsoReflect-β left right raw

module Precompose {A B C S : CAT} (r : MAP B S) (f : MAP C S)
  (e : MAP A B) (a′ : MAP A S) (β : (r ∘ e) =₁ a′) where
  cospan : CospanMap (funPost f) (nameFun r) (funPost f) (nameFun a′)
  cospan = record
    { left = funPre e ; right = id One ; base = funPre e
    ; leftSquare = Interchange.comparison e f
    ; rightSquare = (named-restriction e r) ⁻¹ ∙ ((name-cong β) ⁻¹ ∙ comp-unitʳ (nameFun a′)) }

  functor : MAP (FunOver r f) (FunOver a′ f)
  functor = CospanMap.pullbackMap cospan

  maps : MAP (MapOver r f) (MapOver a′ f)
  maps = mapPost functor

  abstract
    functor-isEquiv : IsEquiv e → IsEquiv functor
    functor-isEquiv ee = CospanEquivalence.pullbackMap-isEquiv cospan
      (funPre-isEquiv e ee) (id-isEquiv One) (funPre-isEquiv e ee)

    maps-isEquiv : IsEquiv e → IsEquiv maps
    maps-isEquiv ee = mapPost-isEquiv functor (functor-isEquiv ee)
```
