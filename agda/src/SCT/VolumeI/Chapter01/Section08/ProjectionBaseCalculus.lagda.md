# Changing the target of projection witnesses

Iterated postcomposition of a projection witness agrees with direct
postcomposition. The second calculation changes the intermediate target
of a composite witness while retaining its specified comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section02.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.ProjectionBaseCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section03.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section03.ProjectionSquares 𝒯 using (lift-base; compose-base)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; preWhisker-comp-at)

lift-assoc : {R K A B C : CAT} (π : MAP K A) (ρ : MAP R A)
  (H : MAP R K) (b : =₁ (π ∘ H) ρ) (f : MAP A B) (g : MAP B C) →
  =₂ (comp-assoc ρ f g ∙ lift-base (g ∘ f) π H b)
    (lift-base g (f ∘ π) H (lift-base f π H b) ∙ (comp-assoc π f g ▷ H))
lift-assoc π ρ H b f g =
  let O = comp-assoc ρ f g
      I = (g ∘ f) ◁ b
      B = comp-assoc H π (g ∘ f)
      J = g ◁ (f ◁ b)
      A = comp-assoc (π ∘ H) f g
      U = comp-assoc H π f
      V = comp-assoc H (f ∘ π) g
      W = comp-assoc π f g ▷ H
  in invIso (isoComp-assoc-at (g ◁ lift-base f π H b) V W) ∙
    (isoComp-cong (invIso (postWhisker-isoComp-at g (f ◁ b) U)) (idIso (V ∙ W)) ∙
    (invIso (isoComp-assoc-at J (g ◁ U) (V ∙ W)) ∙
    (isoComp-cong (idIso J) (pentagon-whiskered H π f g) ∙
    (isoComp-assoc-at J A B ∙
    (isoComp-cong (postWhisker-comp-at b f g) (idIso B) ∙
      invIso (isoComp-assoc-at O I B))))))

lift-base-outer : {R K A B : CAT} (π : MAP K A) (ρ : MAP R A)
  (H : MAP R K) (b : =₁ (π ∘ H) ρ)
  {f g : MAP A B} (α : =₁ f g) →
  =₂ (lift-base g π H b ∙ ((α ▷ π) ▷ H))
    ((α ▷ ρ) ∙ lift-base f π H b)
lift-base-outer π ρ H b {f} {g} α =
  let F = comp-assoc H π f
      G = comp-assoc H π g
      a = (α ▷ π) ▷ H
  in isoComp-assoc-at (α ▷ ρ) (f ◁ b) F ∙
    (isoComp-cong (invIso (interchange-at α b)) (idIso F) ∙
    (invIso (isoComp-assoc-at (g ◁ b) (α ▷ (π ∘ H)) F) ∙
    (isoComp-cong (idIso (g ◁ b)) (preWhisker-comp-at α π H) ∙
      isoComp-assoc-at (g ◁ b) G a)))

change-middle : {X Y Z C : CAT} (π : MAP Z C) (k : MAP Y Z) (j : MAP X Y)
  {q q′ : MAP Y C} {r r′ : MAP X C}
  (b : =₁ (π ∘ k) q) (d : =₁ (q ∘ j) r)
  (α : =₁ q q′) (d′ : =₁ (q′ ∘ j) r′) (η : =₁ r r′) →
  =₂ (η ∙ d) (d′ ∙ (α ▷ j)) →
  =₂ (compose-base π k (α ∙ b) j d′) (η ∙ compose-base π k b j d)
change-middle π k j b d α d′ η p =
  let I = invIso (comp-assoc j k π)
      T = (b ▷ j) ∙ I
  in isoComp-assoc-at η d T ∙
    (isoComp-cong (invIso p) (idIso T) ∙
    (invIso (isoComp-assoc-at d′ (α ▷ j) T) ∙
      isoComp-cong (idIso d′)
        (isoComp-assoc-at (α ▷ j) (b ▷ j) I ∙
          isoComp-cong (preWhisker-isoComp-at α b j) (idIso I))))
```
