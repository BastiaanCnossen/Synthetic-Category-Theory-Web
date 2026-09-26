# Evaluating change of the source structure

The equivalence changing the structure functor has the expected effect
on its universal family: postcompose the evaluation triangle with the
specified structure identification. The calculation uses the uncurried
image of the named identification, including its parameter comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.Currying.SourceChangeFamilies
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Identifications 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.StructureChange 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.Families.Families 𝒯 M ℱ P using (family; universal; family-composite)
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.EvaluatedRelativeCones 𝒯 M ℱ P
open import SCT.VolumeI.Chapter03.RelativeCategories.ConeCalculus.ConeUncurrying 𝒯 M ℱ P using (evalMatch)
open import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.Evaluation 𝒯 M ℱ P using (uncurry-constant-name)
open import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.SourceChange 𝒯 M ℱ P using (module Change)
open import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.ConstantNameChange 𝒯 M ℱ P using () renaming (module Change to NamedChange)

module ChangedCone {X C D S : CAT} {f f′ : MAP C S} (α : f =₁ f′) {g : MAP D S}
  (s : Cone (funPost g) (nameFun f) X) where
  ν = NamedChange.named α ▷ Cone.right s
  value : Cone (funPost g) (nameFun f′) X
  value = record { left = Cone.left s ; right = Cone.right s ; match = ν ∙ Cone.match s }
  κ = uncurry-constant-name f (Cone.right s)
  κ′ = uncurry-constant-name f′ (Cone.right s)
  τ = funUncurryIso (Cone.match s)
  b = funPost-uncurry g (Cone.left s)

  abstract
    matching : evalMatch value =₂ ((α ▷ pr₂) ∙ evalMatch s)
    matching = isoComp-assoc-at (α ▷ pr₂) κ (τ ∙ b ⁻¹) ∙
      (isoComp-cong (NamedChange.At.comparison α (Cone.right s)) (idIso (τ ∙ b ⁻¹)) ∙
        ((isoComp-assoc-at κ′ (funUncurryIso ν) (τ ∙ b ⁻¹)) ⁻¹ ∙
          (isoComp-cong (idIso κ′) (isoComp-assoc-at (funUncurryIso ν) τ (b ⁻¹)) ∙
            isoComp-cong (idIso κ′) (isoComp-cong (funUncurryIso-comp ν (Cone.match s)) (idIso (b ⁻¹))))))

    comparison : FunctorOverIso (EvaluatedCone value) (change-source (α ▷ pr₂) (EvaluatedCone s))
    comparison = triangle-identification _ _ _ matching

module Source {C D S : CAT} {f f′ : MAP C S} (α : f =₁ f′) (g : MAP D S) where
  module Changed = Change α g
  abstract
    family-comparison : FunctorOverIso (family f′ g Changed.functor)
      (change-source (α ▷ pr₂) (universal f g))
    family-comparison = compose-iso-over
      (ChangedCone.comparison α (pullbackCone (funPost g) (nameFun f)))
      (evaluated-comparison Changed.comparison)

    substituted-comparison : {X : CAT} (F : MAP X (FunOver f g)) →
      FunctorOverIso (family f′ g (Changed.functor ∘ F))
        (change-source (α ▷ pr₂) (family f g F))
    substituted-comparison F = compose-iso-over
      (change-source-iso (α ▷ pr₂)
        (inverse-iso-over (evaluated-restriction F (pullbackCone (funPost g) (nameFun f)))))
      (compose-iso-over (parameter-change α F (universal f g))
        (compose-iso-over (prewhisker-over (parameter-over-functor f′ F) family-comparison)
          (family-composite f′ g F Changed.functor)))
```
