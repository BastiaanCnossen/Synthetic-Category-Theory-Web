# Computing the specified functor-category reflector

The original functor-category reflection operation is defined through
specialization of the evaluation-induced mapping functor. Naturality of
that specialization comparison computes the image of the same reflector.
This distinguishes it from choosing another lift through uncurrying.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section07.Evaluation as Evaluation
import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.EvaluationNaturality as Naturality
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreNamingNaturality as Naming
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingUnits as PairingUnits
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Inverses
import SCT.VolumeI.Chapter05.Section01.ComparisonCalculus.Calculus as Calculus

module SCT.VolumeI.Chapter05.Section02.MappingCalculus.FunctorReflection
  {l : Level} (𝒯 : Theory l l l) (M : Mapping.MappingAnimae 𝒯)
  (F : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M F
open import SCT.VolumeI.Chapter01.Section04.Substitution.Specialization 𝒯 M
open import SCT.VolumeI.Chapter01.Section04.Substitution.DecodingNaturality 𝒯 M
  using (decodeFamily; decodeFamily-at)
open Calculus 𝒯 using (_then_)
open PairingUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (cancel-right-reflect)
open Inverses vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-inverse)

module At {X C D : CAT} (f g : MAP X (Fun C D)) where
  module E = Evaluation.Evaluation 𝒯 M (funEval {C} {D})
  module A = Naturality.Action 𝒯 M (funEval {C} {D})
  module N = Naturality.Represented 𝒯 M (funEval {C} {D}) X
  open E.At X using (forward; decode-forward; specialize-β)

  family-at : {U V : MAP X (Fun C D)} (α : U =₁ V)
    → A.uncurryFamily α =₂ funUncurry-cong α
  family-at α = (A.uncurryFamily-at α) ⁻¹ then A.uncurryIso-at α

  action₂ : {U V : MAP X (Fun C D)} {α β : U =₁ V}
    → α =₂ β → funUncurry-cong α =₂ funUncurry-cong β
  action₂ {U} {V} {α} {β} p = (A.uncurryIso-at α) ⁻¹ then
    (A.isoMap U V ◁ p) then A.uncurryIso-at β

  specialization-action : (β : f =₁ g)
    → specializeMapIso forward β =₂ decodeMapIso (forward ◁ nameMapIso β)
  specialization-action β =
    comp-assoc β (postWhisker forward ∘ nameMap-isoMap f g)
      (decodeMap-isoMap (forward ∘ nameMap f) (forward ∘ nameMap g)) then
    (decodeMap-isoMap (forward ∘ nameMap f) (forward ∘ nameMap g) ◁
      comp-assoc β (nameMap-isoMap f g) (postWhisker forward))

  decoded-square : (β : f =₁ g)
    → (decode-forward (nameMap g) ∙ decodeMapIso (forward ◁ nameMapIso β)) =₂
      (funUncurry-cong (decodeMapIso (nameMapIso β)) ∙ decode-forward (nameMap f))
  decoded-square β =
    isoComp-cong ((const-One (decode-forward (nameMap g))) ⁻¹)
      (decodeFamily-at (forward ◁ nameMapIso β)) then
    N.decode-forward-inputs (nameMapIso β) then
    isoComp-cong
      (A.uncurryFamily-cong ((decodeFamily-at (nameMapIso β)) ⁻¹) then
        family-at (decodeMapIso (nameMapIso β)))
      (const-One (decode-forward (nameMap f)))

  named-square : (β : f =₁ g)
    → (funUncurry-cong (decode-name g) ∙ funUncurry-cong (decodeMapIso (nameMapIso β))) =₂
      (funUncurry-cong β ∙ funUncurry-cong (decode-name f))
  named-square β = (A.uncurry-cong-comp (decode-name g) (decodeMapIso (nameMapIso β))) ⁻¹ then
    action₂ (Naming.Named.square 𝒯 M f g β) then A.uncurry-cong-comp β (decode-name f)

  specialization-natural : (β : f =₁ g)
    → (specialize-β g ∙ specializeMapIso forward β) =₂
      (funUncurry-cong β ∙ specialize-β f)
  specialization-natural β =
    isoComp-cong (idIso (specialize-β g)) (specialization-action β) then
    paste-squares (decode-forward (nameMap f)) (decode-forward (nameMap g))
      (funUncurry-cong (decode-name f)) (funUncurry-cong (decode-name g))
      (decodeMapIso (forward ◁ nameMapIso β)) (funUncurry-cong (decodeMapIso (nameMapIso β)))
      (funUncurry-cong β) (decoded-square β) (named-square β)

  reflection-β : (α : funUncurry f =₁ funUncurry g)
    → funUncurry-cong (funReflect f g α) =₂ α
  reflection-β α = cancel-right-reflect (specialize-β f)
    ((specialization-natural (funReflect f g α)) ⁻¹ then
      isoComp-cong (idIso (specialize-β g))
        (specializeMap-reflect-β forward (funUniversal C D X) f g
          ((specialize-β g) ⁻¹ ∙ (α ∙ specialize-β f))) then
      cancel-inverse (specialize-β g) (α ∙ specialize-β f))
```
