# Interchanging the diagram variables

Double currying and symmetry of products interchange the two diagram
variables. The comparison with constant diagrams is retained explicitly:
being constant in the first variable becomes postcomposition with the
constant-diagram functor in the second presentation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter03.Section04.CoconeCalculus.DiagramInterchange
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ using (funIsoReflect; funIsoReflect-β)
open import SCT.VolumeI.Chapter01.Section04.Points 𝒯 M using (oneProduct-in)
open import SCT.VolumeI.Chapter01.Section07.ExponentialLaw 𝒯 M ℱ using (module ExponentialLaw)
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ using (module Constant)

module Interchange (T C D : CAT) where
  module First = ExponentialLaw T C D using (forward; forward-isEquiv)
  module Second = ExponentialLaw C T D
    using (forward; backward; forward-backward; backward-forward)
  module Constants = Constant T C D using (comparison)
  middle = funPre {D = D} (swap {C} {T}) ∘ First.forward

  exchange : MAP (Fun T (Fun C D)) (Fun C (Fun T D))
  exchange = Second.backward ∘ middle

  backward-isEquiv : IsEquiv Second.backward
  backward-isEquiv = record
    { inverse = Second.forward ; sectionIso = Second.forward-backward ⁻¹
    ; retractionIso = Second.backward-forward ⁻¹ }

  abstract
    exchange-isEquiv : IsEquiv exchange
    exchange-isEquiv = equiv-compose middle Second.backward
      (equiv-compose First.forward (funPre swap) First.forward-isEquiv
        (funPre-isEquiv swap (swap-isEquiv C T))) backward-isEquiv

    exchange-constant : (exchange ∘ constantDiagram T (Fun C D)) =₁ funPost (constantDiagram T D)
    exchange-constant = comp-unitˡ (funPost (constantDiagram T D)) ∙
      ((Second.backward-forward ▷ funPost (constantDiagram T D)) ∙
        ((comp-assoc (funPost (constantDiagram T D)) Second.forward Second.backward) ⁻¹ ∙
          ((Second.backward ◁ Constants.comparison) ∙
            ((Second.backward ◁ comp-assoc (constantDiagram T (Fun C D)) First.forward (funPre swap)) ∙
              comp-assoc (constantDiagram T (Fun C D)) middle Second.backward))))
```

Naming a postcomposed functor agrees with postcomposition of its name.
This comparison is used when passing between transformations and their
functors into the arrow category. `post-nameFun-image` records the
specified uncurried identification, for later calculations with relative
triangles.

```agda
nameFun-cong : {C D : CAT} {f g : MAP C D} → f =₁ g → nameFun f =₁ nameFun g
nameFun-cong α = funCurry-cong (α ▷ pr₂)

post-nameFun-uncurried : {B C D : CAT} (g : MAP C D) (f : MAP B C) →
  funUncurry (funPost g ∘ nameFun f) =₁ funUncurry (nameFun (g ∘ f))
post-nameFun-uncurried g f =
  (funCurry-β ((g ∘ f) ∘ pr₂)) ⁻¹ ∙
    ((comp-assoc pr₂ f g) ⁻¹ ∙
      ((g ◁ funCurry-β (f ∘ pr₂)) ∙ funPost-uncurry g (nameFun f)))

post-nameFun : {B C D : CAT} (g : MAP C D) (f : MAP B C) →
  (funPost g ∘ nameFun f) =₁ nameFun (g ∘ f)
post-nameFun g f = funIsoReflect _ _ (post-nameFun-uncurried g f)

post-nameFun-image : {B C D : CAT} (g : MAP C D) (f : MAP B C) →
  funUncurryIso (post-nameFun g f) =₂ post-nameFun-uncurried g f
post-nameFun-image g f = funIsoReflect-β _ _ (post-nameFun-uncurried g f)

decodeFun-cong : {C D : CAT} {f g : Obj-abs (Fun C D)} → f =₁ g → decodeFun f =₁ decodeFun g
decodeFun-cong {C} α = funUncurry-cong α ▷ oneProduct-in C

decodeFun-post : {B C D : CAT} (g : MAP C D) (f : Obj-abs (Fun B C)) →
  decodeFun (funPost g ∘ f) =₁ (g ∘ decodeFun f)
decodeFun-post {B} g f = comp-assoc (oneProduct-in B) (funUncurry f) g ∙
  (funPost-uncurry g f ▷ oneProduct-in B)
```
