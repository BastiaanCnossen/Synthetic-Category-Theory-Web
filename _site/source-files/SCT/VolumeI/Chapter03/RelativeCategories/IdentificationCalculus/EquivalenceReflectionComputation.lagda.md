# The prescribed image of the existing equivalence reflector

The earlier `equiv-reflect` uses the section of a chosen inverse.
Its image computation follows without replacing that choice. First
use naturality of the section to compute reflection on an image.
Then lift an arbitrary identification through the equivalence on
identification animae and use congruence of the same reflector.

The statement applies again to an identification anima. Thus it can
also recover the image of a reflected triangle witness.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Squares

module SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.EquivalenceReflectionComputation
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Structural vocabulary terminal products productLaws composition whiskering
  using (postWhisker-id-at; postWhisker-comp-at)
open Squares vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-left)

private
  paste : {X C : CAT} {u₀ u₁ v₀ v₁ w₀ w₁ : MAP X C}
    (α : u₀ =₁ u₁) (β : v₀ =₁ v₁) (γ : w₀ =₁ w₁)
    (a₀ : u₀ =₁ v₀) (a₁ : u₁ =₁ v₁)
    (b₀ : v₀ =₁ w₀) (b₁ : v₁ =₁ w₁) →
    (a₁ ∙ α) =₂ (β ∙ a₀) → (b₁ ∙ β) =₂ (γ ∙ b₀) →
    ((b₁ ∙ a₁) ∙ α) =₂ (γ ∙ (b₀ ∙ a₀))
  paste α β γ a₀ a₁ b₀ b₁ first second = isoComp-assoc-at γ b₀ a₀ ∙
    (isoComp-cong second (idIso a₀) ∙
    ((isoComp-assoc-at b₁ β a₀) ⁻¹ ∙
    (isoComp-cong (idIso b₁) first ∙ isoComp-assoc-at b₁ a₁ α)))

module Reflection {X C D : CAT} {F : MAP C D} (e : IsEquiv F)
  (u v : MAP X C) where
  G = IsEquiv.inverse e
  η = IsEquiv.sectionIso e
  comparison : (w : MAP X C) → w =₁ (G ∘ (F ∘ w))
  comparison w = comp-assoc w F G ∙ ((η ▷ w) ∙ (comp-unitˡ w) ⁻¹)

  opaque
    section-natural : (β : u =₁ v) →
      (((η ▷ v) ∙ (comp-unitˡ v) ⁻¹) ∙ β) =₂
        (((G ∘ F) ◁ β) ∙ ((η ▷ u) ∙ (comp-unitˡ u) ⁻¹))
    section-natural β = paste β (id C ◁ β) ((G ∘ F) ◁ β)
      ((comp-unitˡ u) ⁻¹) ((comp-unitˡ v) ⁻¹) (η ▷ u) (η ▷ v)
      (move-square (comp-unitˡ v) (id C ◁ β) β (comp-unitˡ u) (postWhisker-id-at β))
      (interchange-at η β)

    comparison-natural : (β : u =₁ v) →
      (comparison v ∙ β) =₂ ((G ◁ (F ◁ β)) ∙ comparison u)
    comparison-natural β = paste β ((G ∘ F) ◁ β) (G ◁ (F ◁ β))
      ((η ▷ u) ∙ (comp-unitˡ u) ⁻¹) ((η ▷ v) ∙ (comp-unitˡ v) ⁻¹)
      (comp-assoc u F G) (comp-assoc v F G)
      (section-natural β) (postWhisker-comp-at β F G)

    on-image : (β : u =₁ v) → equiv-reflect e u v (F ◁ β) =₂ β
    on-image β = cancel-left (comparison v) β ∙
      isoComp-cong (idIso ((comparison v) ⁻¹)) ((comparison-natural β) ⁻¹)

    congruence : {α β : (F ∘ u) =₁ (F ∘ v)} → α =₂ β →
      equiv-reflect e u v α =₂ equiv-reflect e u v β
    congruence q = isoComp-cong (idIso ((comparison v) ⁻¹))
      (isoComp-cong (postWhisker G ◁ q) (idIso (comparison u)))

  module At (α : (F ∘ u) =₁ (F ∘ v)) where
    chosen : FunctorLift (postWhisker F) α
    chosen = postWhisker-lift F e α
    β = FunctorLift.lift chosen
    image = FunctorLift.comparison chosen

    opaque
      comparison-to-lift : equiv-reflect e u v α =₂ β
      comparison-to-lift = on-image β ∙ congruence (image ⁻¹)

      computation : (F ◁ equiv-reflect e u v α) =₂ α
      computation = image ∙ (postWhisker F ◁ comparison-to-lift)

  computation : (α : (F ∘ u) =₁ (F ∘ v)) → (F ◁ equiv-reflect e u v α) =₂ α
  computation = At.computation
```
