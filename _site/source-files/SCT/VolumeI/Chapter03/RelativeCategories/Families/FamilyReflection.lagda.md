# Recognizing relative families by evaluation

An identification of evaluated families, compatible with their triangles,
lifts to an identification of their relative cones. Uncurrying reflects
the matching square after cancelling the postcomposition and constant-name
comparisons. Thus the argument applies to the whole parameter category,
not only to its absolute points.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN

module SCT.VolumeI.Chapter03.RelativeCategories.Families.FamilyReflection
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.MappingCompatibility 𝒯 M ℱ using (funPost-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section07.PullbackCalculus.ConeUncurrying 𝒯 M ℱ using (paste-iso-squares)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting 𝒯 P using (pullback-reflect)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (evalMatch)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P using (EvaluatedCone)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameNaturality 𝒯 M ℱ P using (constant-name-natural)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left; move-square)

module Cones {X C D S : CAT} {f : MAP C S} {g : MAP D S}
  (s t : Cone (funPost g) (nameFun f) X) (Φ : FunctorOverIso (EvaluatedCone s) (EvaluatedCone t)) where
  α = funIsoReflect (Cone.left s) (Cone.left t) (FunctorOverIso.underlying Φ)
  β = terminal-iso (Cone.right s) (Cone.right t)
  fs = funPost-uncurry g (Cone.left s)
  ft = funPost-uncurry g (Cone.left t)
  κs = uncurry-constant-name f (Cone.right s)
  κt = uncurry-constant-name f (Cone.right t)
  τs = funUncurryIso (Cone.match s)
  τt = funUncurryIso (Cone.match t)
  first = funUncurryIso (funPost g ◁ α)
  middle = g ◁ funUncurryIso α
  last = funUncurryIso (nameFun f ◁ β)

  abstract
    native-square : (evalMatch t ∙ middle) =₂ (idIso (f ∘ pr₂) ∙ evalMatch s)
    native-square = (isoComp-unitˡ-at (evalMatch s)) ⁻¹ ∙
      (FunctorOverIso.compatible Φ ∙
        isoComp-cong (idIso (evalMatch t))
          (postWhisker g ◁ funIsoReflect-β (Cone.left s) (Cone.left t) (FunctorOverIso.underlying Φ)))

    recover : (r : Cone (funPost g) (nameFun f) X) →
      ((uncurry-constant-name f (Cone.right r)) ⁻¹ ∙ (evalMatch r ∙ funPost-uncurry g (Cone.left r))) =₂
        funUncurryIso (Cone.match r)
    recover r = cancel-left κ τ ∙ isoComp-cong (idIso (κ ⁻¹))
      (isoComp-cong (idIso κ)
        (isoComp-unitʳ-at τ ∙
          (isoComp-cong (idIso τ) (isoComp-inverseˡ-at b) ∙ isoComp-assoc-at τ (b ⁻¹) b)) ∙
        isoComp-assoc-at κ (τ ∙ b ⁻¹) b)
      where
      κ : funUncurry (nameFun f ∘ Cone.right r) =₁ (f ∘ pr₂)
      κ = uncurry-constant-name f (Cone.right r)
      τ : funUncurry (funPost g ∘ Cone.left r) =₁ funUncurry (nameFun f ∘ Cone.right r)
      τ = funUncurryIso (Cone.match r)
      b : funUncurry (funPost g ∘ Cone.left r) =₁ (g ∘ funUncurry (Cone.left r))
      b = funPost-uncurry g (Cone.left r)

    raw-square : (τt ∙ first) =₂ (last ∙ τs)
    raw-square = isoComp-cong (idIso last) (recover s) ∙
      (paste-iso-squares (evalMatch s ∙ fs) (evalMatch t ∙ ft) (κs ⁻¹) (κt ⁻¹)
        first (idIso (f ∘ pr₂)) last
        (paste-iso-squares fs ft (evalMatch s) (evalMatch t) first middle (idIso (f ∘ pr₂))
          (funPost-uncurry-natural g α) native-square)
        (move-square κt last (idIso (f ∘ pr₂)) κs
          ((isoComp-unitˡ-at κs) ⁻¹ ∙ constant-name-natural f β)) ∙
        isoComp-cong ((recover t) ⁻¹) (idIso first))

    matching : (Cone.match t ∙ (funPost g ◁ α)) =₂ ((nameFun f ◁ β) ∙ Cone.match s)
    matching = funReflect-Iso₂ _ _
      ((funUncurryIso-comp (nameFun f ◁ β) (Cone.match s)) ⁻¹ ∙
        (raw-square ∙ funUncurryIso-comp (Cone.match t) (funPost g ◁ α)))

  comparison : ConeIso s t
  comparison = record { leftIso = α ; rightIso = β ; compatible = matching }

abstract
  reflect-family : {X C D S : CAT} (f : MAP C S) (g : MAP D S)
    (F G : MAP X (FunOver f g)) →
    FunctorOverIso (EvaluatedCone (conePre F (pullbackCone (funPost g) (nameFun f))))
      (EvaluatedCone (conePre G (pullbackCone (funPost g) (nameFun f)))) → F =₁ G
  reflect-family f g F G Φ = pullback-reflect F G
    (Cones.comparison (conePre F (pullbackCone (funPost g) (nameFun f)))
      (conePre G (pullbackCone (funPost g) (nameFun f))) Φ)
```
