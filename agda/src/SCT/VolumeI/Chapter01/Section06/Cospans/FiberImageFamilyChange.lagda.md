# Fiber images and changes of family

Changing the source and target families commutes with a specified fiber
image square when their displayed comparison triangle commutes. The cone
comparison retains that triangle. Lifting the comparison gives the square
of induced fiber functors together with its whole cone computation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.FiberImageFamilyChange
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering using (pre-square-projection)
import SCT.VolumeI.Chapter01.Section06.Cospans.FamilyChange as Changes
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
open Laws.PullbackStructure P

module Along {C D E B Γ : CAT}
  (u : MAP C D) (f : MAP C E) (w : MAP E B) (b : MAP D B)
  (α : (b ∘ u) =₁ (w ∘ f))
  {a a′ : MAP Γ D} {e e′ : MAP Γ B}
  (θ : a =₁ a′) (κ : e =₁ e′)
  (δ : (b ∘ a) =₁ e) (δ′ : (b ∘ a′) =₁ e′)
  (triangle : (δ′ ∙ (b ◁ θ)) =₂ (κ ∙ δ)) where
  private
    module Source = Changes.Change 𝒯 P u θ using (map; value; computation)
    module Target = Changes.Change 𝒯 P w κ using (map; value; restrict; action; computation)
    module Before = Images.Along 𝒯 u a f w b e α δ using (value; left-normal; right-normal)
    module After = Images.Along 𝒯 u a′ f w b e′ α δ′ using (value; left-normal; right-normal; action; restrict)

  module ConeComparison {X : CAT} (q : Cone u a X) where
    before = Target.value (Before.value q)
    after = After.value (Source.value q)
    private
      r = Cone.right q
      σ = Cone.match q
      L = Before.left-normal (Cone.left q)
      R = Before.right-normal r
      R′ = After.right-normal r
      abstract
        right-square : (R′ ∙ (b ◁ (θ ▷ r))) =₂ ((κ ▷ r) ∙ R)
        right-square = pre-square-projection b θ κ δ δ′ r triangle
        matching : Cone.match after =₂ Cone.match before
        matching = isoComp-assoc-at (κ ▷ r) R ((b ◁ σ) ∙ L ⁻¹) ∙
          (isoComp-cong right-square (idIso ((b ◁ σ) ∙ L ⁻¹)) ∙
          ((isoComp-assoc-at R′ (b ◁ (θ ▷ r)) ((b ◁ σ) ∙ L ⁻¹)) ⁻¹ ∙
          (isoComp-cong (idIso R′) (isoComp-assoc-at (b ◁ (θ ▷ r)) (b ◁ σ) (L ⁻¹)) ∙
            isoComp-cong (idIso R′)
              (isoComp-cong (postWhisker-isoComp-at b (θ ▷ r) σ) (idIso (L ⁻¹))))))
    comparison : ConeIso before after
    comparison = cone-match-change _ _ _ _ (matching ⁻¹)

  source-change = Source.map
  target-change = Target.map
  image-before : MAP (Pullback u a) (Pullback w e)
  image-before = pullbackLift (Before.value (pullbackCone u a))
  image-after : MAP (Pullback u a′) (Pullback w e′)
  image-after = pullbackLift (After.value (pullbackCone u a′))
  private
    S = pullbackCone u a
    S′ = pullbackCone u a′
    T = pullbackCone w e
    T′ = pullbackCone w e′
    module Square = ConeComparison S using (before; after; comparison)

  before-computation : ConeIso (conePre (target-change ∘ image-before) T′) Square.before
  before-computation = coneIso-compose
    (Target.action (pullbackLift-β (Before.value S)))
    (coneIso-compose (Target.restrict image-before T)
      (coneIso-compose (coneIso-pre image-before Target.computation)
        (coneIso-inverse (conePre-assoc image-before target-change T′))))

  after-computation : ConeIso (conePre (image-after ∘ source-change) T′) Square.after
  after-computation = coneIso-compose (After.action Source.computation)
    (coneIso-compose (coneIso-inverse (After.restrict source-change S′))
      (coneIso-compose (coneIso-pre source-change (pullbackLift-β (After.value S′)))
        (coneIso-inverse (conePre-assoc source-change image-after T′))))

  prescribed : ConeIso (conePre (target-change ∘ image-before) T′)
    (conePre (image-after ∘ source-change) T′)
  prescribed = coneIso-compose (coneIso-inverse after-computation)
    (coneIso-compose Square.comparison before-computation)
  private
    module Lifted = Lifting.Lift 𝒯 P (target-change ∘ image-before) (image-after ∘ source-change) prescribed
      using (lift; comparison-image; left-image; right-image)
  open Lifted public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```


Changing only the target family has a more direct form. It uses the
composite comparison literally and introduces no source identity map.

```agda
module TargetChange {C D E B Γ : CAT}
  (u : MAP C D) (a : MAP Γ D) (f : MAP C E) (w : MAP E B) (b : MAP D B)
  (α : (b ∘ u) =₁ (w ∘ f)) {e e′ : MAP Γ B}
  (δ : (b ∘ a) =₁ e) (κ : e =₁ e′) where
  private
    module Target = Changes.Change 𝒯 P w κ using (map; value; restrict; action; computation)
    module Before = Images.Along 𝒯 u a f w b e α δ using (value; left-normal; right-normal)
    module After = Images.Along 𝒯 u a f w b e′ α (κ ∙ δ) using (value; right-normal)

  module ConeComparison {X : CAT} (q : Cone u a X) where
    before = Target.value (Before.value q)
    after = After.value q
    private
      r = Cone.right q
      rest = (b ◁ Cone.match q) ∙ (Before.left-normal (Cone.left q)) ⁻¹
      abstract
        matching : Cone.match after =₂ Cone.match before
        matching = isoComp-assoc-at (κ ▷ r) (Before.right-normal r) rest ∙
          isoComp-cong
            (isoComp-assoc-at (κ ▷ r) (δ ▷ r) ((comp-assoc r a b) ⁻¹) ∙
              isoComp-cong (preWhisker-isoComp-at κ δ r) (idIso ((comp-assoc r a b) ⁻¹)))
            (idIso rest)
    comparison : ConeIso before after
    comparison = cone-match-change _ _ _ _ (matching ⁻¹)

  target-change = Target.map
  image-before : MAP (Pullback u a) (Pullback w e)
  image-before = pullbackLift (Before.value (pullbackCone u a))
  image-after : MAP (Pullback u a) (Pullback w e′)
  image-after = pullbackLift (After.value (pullbackCone u a))
  private
    S = pullbackCone u a
    T = pullbackCone w e
    T′ = pullbackCone w e′
    module Square = ConeComparison S using (before; after; comparison)

  before-computation : ConeIso (conePre (target-change ∘ image-before) T′) Square.before
  before-computation = coneIso-compose
    (Target.action (pullbackLift-β (Before.value S)))
    (coneIso-compose (Target.restrict image-before T)
      (coneIso-compose (coneIso-pre image-before Target.computation)
        (coneIso-inverse (conePre-assoc image-before target-change T′))))

  prescribed : ConeIso (conePre (target-change ∘ image-before) T′) (conePre image-after T′)
  prescribed = coneIso-compose (coneIso-inverse (pullbackLift-β (After.value S)))
    (coneIso-compose Square.comparison before-computation)
  private
    module Lifted = Lifting.Lift 𝒯 P (target-change ∘ image-before) image-after prescribed
      using (lift; comparison-image; left-image; right-image)
  open Lifted public using (comparison-image; left-image; right-image) renaming (lift to comparison)
```
