# The relative exponential law

Uncurrying identifies functors over a map into a functor category with
functors over its uncurried map. We apply the ordinary exponential law
to the defining pullback of relative functor categories. Both squares
are chosen by their uncurried images, so their commutativity data remain
available for the subsequent evaluation comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.ExponentialLaw
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M using (mapPost; mapPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.CospanEquivalences 𝒯 P using (module CospanEquivalence)
open import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.DiagramNames 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P

module Law {K S C B : CAT} (r : MAP C B) (a′ : MAP K (Fun S B)) where
  module E = ExponentialLaw K S C
  module T = ExponentialLaw K S B
  J = funPost {C = K} (funPost {C = S} r)
  R = Associativity.backward (Fun K (Fun S C)) K S
  u = funUncurry a′
  R₁ = Associativity.backward One K S
  Q = productMap (pr₂ {C = One} {D = K}) (id S)

  abstract
    double-post : funUncurry (funUncurry J) =₁ (r ∘ E.doubleEvaluation)
    double-post = funPost-uncurry r (funEval {K} {Fun S C}) ∙
      funUncurry-cong (funPost-β (funPost {C = S} r))

    left-normal : funUncurry (funPost r ∘ E.forward) =₁ (r ∘ E.forwardEvaluation)
    left-normal = (r ◁ E.forward-β) ∙ funPost-uncurry r E.forward

    right-normal : funUncurry (T.forward ∘ J) =₁ (r ∘ E.forwardEvaluation)
    right-normal = comp-assoc R E.doubleEvaluation r ∙
      ((double-post ▷ R) ∙ T.forward-represents J)

  post-raw = right-normal ⁻¹ ∙ left-normal
  post-square : (funPost r ∘ E.forward) =₁ (T.forward ∘ J)
  post-square = funIsoReflect _ _ post-raw

  abstract
    post-square-image : funUncurryIso post-square =₂ post-raw
    post-square-image = funIsoReflect-β _ _ post-raw

    double-name : funUncurry (funUncurry (nameFun a′)) =₁ (u ∘ Q)
    double-name = funUncurry-restrict a′ pr₂ ∙
      funUncurry-cong (funCurry-β (a′ ∘ pr₂))

    remove-One : (Q ∘ R₁) =₁ pr₂ {C = One} {D = K × S}
    remove-One = pair-η pr₂ ∙
      (pair-cong (Associativity.backward-second One K S)
        (Associativity.backward-third One K S ∙ ((comp-unitˡ pr₂) ▷ R₁)) ∙
        pair-pre (pr₂ ∘ pr₁) (id S ∘ pr₂) R₁)

  named-raw : funUncurry (T.forward ∘ nameFun a′) =₁ funUncurry (nameFun u)
  named-raw = (funCurry-β (u ∘ pr₂)) ⁻¹ ∙
    ((u ◁ remove-One) ∙
      (comp-assoc R₁ Q u ∙
        ((double-name ▷ R₁) ∙ T.forward-represents (nameFun a′))))

  named-square : (T.forward ∘ nameFun a′) =₁ nameFun u
  named-square = funIsoReflect _ _ named-raw

  abstract
    named-square-image : funUncurryIso named-square =₂ named-raw
    named-square-image = funIsoReflect-β _ _ named-raw

  cospan : CospanMap (funPost (funPost r)) (nameFun a′) (funPost r) (nameFun u)
  cospan = record
    { left = E.forward ; base = T.forward ; right = id One
    ; leftSquare = post-square
    ; rightSquare = named-square ⁻¹ ∙ comp-unitʳ (nameFun u) }

  functor : MAP (FunOver a′ (funPost r)) (FunOver u r)
  functor = CospanMap.pullbackMap cospan

  maps : MAP (MapOver a′ (funPost r)) (MapOver u r)
  maps = mapPost functor

  abstract
    functor-isEquiv : IsEquiv functor
    functor-isEquiv = CospanEquivalence.pullbackMap-isEquiv cospan
      E.forward-isEquiv (id-isEquiv One) T.forward-isEquiv

    maps-isEquiv : IsEquiv maps
    maps-isEquiv = mapPost-isEquiv functor functor-isEquiv
```
