# Cone transport over a fixed base

When a cospan map fixes the base category, its action on a matching is
the usual quotient of the two leg comparisons. This calculation removes
the identity functor and its unitors while retaining their coherence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FixedBaseConeAction
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction 𝒯 P using (module Action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.Comparisons 𝒯 using (coneIso-compose)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural
  vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module Leg {X Y Z Γ : CAT} (f : MAP X Z) (f′ : MAP Y Z)
  (u : MAP X Y) (α : (f′ ∘ u) =₁ f) (p : MAP Γ X) where
  square = (comp-unitˡ f) ⁻¹ ∙ α
  A = comp-assoc p f (id Z)
  B = comp-assoc p u f′
  forward : (f′ ∘ (u ∘ p)) =₁ (f ∘ p)
  forward = (α ▷ p) ∙ B ⁻¹
  frame : (id Z ∘ (f ∘ p)) =₁ (f′ ∘ (u ∘ p))
  frame = B ∙ ((square ⁻¹ ▷ p) ∙ A ⁻¹)

  abstract
    inverse-frame : frame ⁻¹ =₂ (A ∙ ((square ▷ p) ∙ B ⁻¹))
    inverse-frame = isoComp-assoc-at A (square ▷ p) (B ⁻¹) ∙
      (isoComp-cong
        (isoComp-cong (inverse-inverse A)
          (inverse-inverse (square ▷ p) ∙ (＝-inv ◁ pre-inverse square p)) ∙
          inverse-composite (square ⁻¹ ▷ p) (A ⁻¹))
        (idIso (B ⁻¹)) ∙ inverse-composite B ((square ⁻¹ ▷ p) ∙ A ⁻¹))

    unit-cancel : ((comp-unitˡ (f ∘ p) ∙ A) ∙ (square ▷ p)) =₂ (α ▷ p)
    unit-cancel = (preWhisker p ◁ cancel-inverse (comp-unitˡ f) α) ∙
      ((preWhisker-isoComp-at (comp-unitˡ f) square p) ⁻¹ ∙
        isoComp-cong (left-unitor-comp p f) (idIso (square ▷ p)))

    bridge : (comp-unitˡ (f ∘ p) ∙ frame ⁻¹) =₂ forward
    bridge = isoComp-cong unit-cancel (idIso (B ⁻¹)) ∙
      ((isoComp-assoc-at (comp-unitˡ (f ∘ p) ∙ A) (square ▷ p) (B ⁻¹)) ⁻¹ ∙
      ((isoComp-assoc-at (comp-unitˡ (f ∘ p)) A ((square ▷ p) ∙ B ⁻¹)) ⁻¹ ∙
        isoComp-cong (idIso (comp-unitˡ (f ∘ p))) inverse-frame))

    forward-frame : (forward ∙ frame) =₂ comp-unitˡ (f ∘ p)
    forward-frame = isoComp-unitʳ-at (comp-unitˡ (f ∘ p)) ∙
      (isoComp-cong (idIso (comp-unitˡ (f ∘ p))) (isoComp-inverseˡ-at frame) ∙
      (isoComp-assoc-at (comp-unitˡ (f ∘ p)) (frame ⁻¹) frame ∙
        isoComp-cong (bridge ⁻¹) (idIso frame)))

module Fixed {A B A′ B′ Z : CAT} {f : MAP A Z} {g : MAP B Z}
  {f′ : MAP A′ Z} {g′ : MAP B′ Z}
  (u : MAP A A′) (v : MAP B B′)
  (α : (f′ ∘ u) =₁ f) (β : (g′ ∘ v) =₁ g) where
  cospan : CospanMap f g f′ g′
  cospan = record { left = u ; right = v ; base = id Z
    ; leftSquare = (comp-unitˡ f) ⁻¹ ∙ α
    ; rightSquare = (comp-unitˡ g) ⁻¹ ∙ β }
  module Induced = CospanMap cospan using (mapCone)
  module Act = Action cospan using (comparison; module Normal)

  module At {Γ : CAT} (s : Cone f g Γ) where
    module L = Leg f f′ u α (Cone.left s)
    module R = Leg g g′ v β (Cone.right s)
    τ = Cone.match s
    normal = Act.Normal.read s
    simplified : Cone f′ g′ Γ
    simplified = record { left = u ∘ Cone.left s ; right = v ∘ Cone.right s
      ; match = R.forward ⁻¹ ∙ (τ ∙ L.forward) }

    abstract
      square : (R.forward ∙ Cone.match normal) =₂ (τ ∙ L.forward)
      square = isoComp-cong (idIso τ) L.bridge ∙
        (isoComp-assoc-at τ (comp-unitˡ (f ∘ Cone.left s)) (L.frame ⁻¹) ∙
        (isoComp-cong (postWhisker-id-at τ) (idIso (L.frame ⁻¹)) ∙
        ((isoComp-assoc-at (comp-unitˡ (g ∘ Cone.right s)) (id Z ◁ τ) (L.frame ⁻¹)) ⁻¹ ∙
        (isoComp-cong R.forward-frame (idIso ((id Z ◁ τ) ∙ L.frame ⁻¹)) ∙
          (isoComp-assoc-at R.forward R.frame ((id Z ◁ τ) ∙ L.frame ⁻¹)) ⁻¹))))

      matching : Cone.match normal =₂ Cone.match simplified
      matching = isoComp-cong (idIso (R.forward ⁻¹)) square ∙
        (cancel-left R.forward (Cone.match normal)) ⁻¹

    comparison : ConeIso (Induced.mapCone s) simplified
    comparison = coneIso-compose (cone-match-change _ _ _ _ matching) (Act.comparison s)
```
