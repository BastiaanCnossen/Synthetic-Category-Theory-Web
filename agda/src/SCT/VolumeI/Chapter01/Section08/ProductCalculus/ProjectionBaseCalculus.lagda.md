# Changing the target of projection witnesses

Iterated postcomposition of a projection witness agrees with direct
postcomposition. The second calculation changes the intermediate target
of a composite witness while retaining its specified comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing as Iterated
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural

module SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (lift-base; compose-base)
open Iterated vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pentagon-whiskered)
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-comp-at; preWhisker-comp-at)

lift-assoc : {R K A B C : CAT} (π : MAP K A) (ρ : MAP R A)
  (H : MAP R K) (b : (π ∘ H) =₁ ρ) (f : MAP A B) (g : MAP B C) →
  (comp-assoc ρ f g ∙ lift-base (g ∘ f) π H b) =₂
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
  in (isoComp-assoc-at (g ◁ lift-base f π H b) V W) ⁻¹ ∙
    (isoComp-cong ((postWhisker-isoComp-at g (f ◁ b) U) ⁻¹) (idIso (V ∙ W)) ∙
    ((isoComp-assoc-at J (g ◁ U) (V ∙ W)) ⁻¹ ∙
    (isoComp-cong (idIso J) (pentagon-whiskered H π f g) ∙
    (isoComp-assoc-at J A B ∙
    (isoComp-cong (postWhisker-comp-at b f g) (idIso B) ∙
      (isoComp-assoc-at O I B) ⁻¹)))))

lift-base-outer : {R K A B : CAT} (π : MAP K A) (ρ : MAP R A)
  (H : MAP R K) (b : (π ∘ H) =₁ ρ)
  {f g : MAP A B} (α : f =₁ g) →
  (lift-base g π H b ∙ ((α ▷ π) ▷ H)) =₂
    ((α ▷ ρ) ∙ lift-base f π H b)
lift-base-outer π ρ H b {f} {g} α =
  let F = comp-assoc H π f
      G = comp-assoc H π g
      a = (α ▷ π) ▷ H
  in isoComp-assoc-at (α ▷ ρ) (f ◁ b) F ∙
    (isoComp-cong ((interchange-at α b) ⁻¹) (idIso F) ∙
    ((isoComp-assoc-at (g ◁ b) (α ▷ (π ∘ H)) F) ⁻¹ ∙
    (isoComp-cong (idIso (g ◁ b)) (preWhisker-comp-at α π H) ∙
      isoComp-assoc-at (g ◁ b) G a)))

change-middle : {X Y Z C : CAT} (π : MAP Z C) (k : MAP Y Z) (j : MAP X Y)
  {q q′ : MAP Y C} {r r′ : MAP X C}
  (b : (π ∘ k) =₁ q) (d : (q ∘ j) =₁ r)
  (α : q =₁ q′) (d′ : (q′ ∘ j) =₁ r′) (η : r =₁ r′) →
  (η ∙ d) =₂ (d′ ∙ (α ▷ j)) →
  (compose-base π k (α ∙ b) j d′) =₂ (η ∙ compose-base π k b j d)
change-middle π k j b d α d′ η p =
  let I = (comp-assoc j k π) ⁻¹
      T = (b ▷ j) ∙ I
  in isoComp-assoc-at η d T ∙
    (isoComp-cong (p ⁻¹) (idIso T) ∙
    ((isoComp-assoc-at d′ (α ▷ j) T) ⁻¹ ∙
      isoComp-cong (idIso d′)
        (isoComp-assoc-at (α ▷ j) (b ▷ j) I ∙
          isoComp-cong (preWhisker-isoComp-at α b j) (idIso I))))
```
