# Coordinates of a cospan image

A compatible projection of the three components of a cospan map gives
an identification of the whole image cone. The proof retains the leg
comparisons and verifies the matching by pasting its left, middle, and
right squares. Restriction of the two original square computations is
handled by the general projected-square calculation.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.ProjectedImages
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯 using (coneIso-compose; coneIso-inverse)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality
  vocabulary terminal products productLaws composition vertical whiskering
  using (move-square; cancel-right; substitution-square-projection)
open import SCT.VolumeI.Chapter01.Section03.ProductCalculus.IteratedPairing
  vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle using (transport-pre)
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedCones as Coordinates
import SCT.VolumeI.Chapter01.Section06.Coordinates.ProjectedSquareRestriction as Squares
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Images

private
  abstract
    remove-frame : {X Y : CAT} {a b x y x′ y′ : MAP X Y}
      (L : a =₁ x) (R : b =₁ y) (q : a =₁ b) (q′ : x′ =₁ y′)
      (l : x =₁ x′) (r : y =₁ y′) →
      (q′ ∙ (l ∙ L)) =₂ ((r ∙ R) ∙ q) →
      (q′ ∙ l) =₂ (r ∙ (R ∙ (q ∙ L ⁻¹)))
    remove-frame L R q q′ l r square =
      isoComp-assoc-at r R (q ∙ L ⁻¹) ∙
      (isoComp-assoc-at (r ∙ R) q (L ⁻¹) ∙
      (isoComp-cong square (idIso (L ⁻¹)) ∙
      (isoComp-cong (isoComp-assoc-at q′ l L) (idIso (L ⁻¹)) ∙
        (cancel-right L (q′ ∙ l)) ⁻¹)))

module Coordinate {C D E A B Z A₀ B₀ Z₀ : CAT}
  {f : MAP C E} {g : MAP D E} {F : MAP A Z} {G : MAP B Z}
  {f₀ : MAP A₀ Z₀} {g₀ : MAP B₀ Z₀}
  (H : CospanMap f g F G) (H₀ : CospanMap f g f₀ g₀)
  (qA : MAP A A₀) (qB : MAP B B₀) (π : MAP Z Z₀)
  (ζ : (π ∘ F) =₁ (f₀ ∘ qA)) (η : (π ∘ G) =₁ (g₀ ∘ qB))
  (β : (qA ∘ CospanMap.left H) =₁ CospanMap.left H₀)
  (γ : (qB ∘ CospanMap.right H) =₁ CospanMap.right H₀)
  (κ : (π ∘ CospanMap.base H) =₁ CospanMap.base H₀) where
  private
    module H = CospanMap H
    module H₀ = CospanMap H₀
    module Read = Coordinates.Coordinate 𝒯 F G f₀ g₀ qA qB π ζ η
      using (read; read-iso; left-normal; right-normal)
    module Image = Images.Action 𝒯 P H using (normalized; left-change; right-change; module Normalization)
    module Component = Images.Action 𝒯 P H₀ using (normalized; left-change; right-change; module Normalization)
  module Left = Squares.At 𝒯 F H.base f qA π f₀ H₀.base ζ κ
    H.left H₀.left β H.leftSquare H₀.leftSquare using (coordinate; module Restrict)
  module Right = Squares.At 𝒯 G H.base g qB π g₀ H₀.base η κ
    H.right H₀.right γ H.rightSquare H₀.rightSquare using (coordinate; module Restrict)

  module At (left-computation : Left.coordinate =₂ H₀.leftSquare)
    (right-computation : Right.coordinate =₂ H₀.rightSquare)
    {T : CAT} (s : Cone f g T) where
    left-leg = transport-pre qA H.left β (Cone.left s)
    right-leg = transport-pre qB H.right γ (Cone.right s)
    private
      L = Read.left-normal (H.left ∘ Cone.left s)
      R = Read.right-normal (H.right ∘ Cone.right s)
      l = f₀ ◁ left-leg
      r = g₀ ◁ right-leg
      αL = Image.left-change s
      αR = Image.right-change s
      αL₀ = Component.left-change s
      αR₀ = Component.right-change s
      u = transport-pre π H.base κ (f ∘ Cone.left s)
      v = transport-pre π H.base κ (g ∘ Cone.right s)
      middle = π ◁ (H.base ◁ Cone.match s)
      middle₀ = H₀.base ◁ Cone.match s
      raw = (π ◁ αR) ⁻¹ ∙ (middle ∙ (π ◁ αL))
      final = Cone.match (Component.normalized s)

    private
      abstract
        projected-matching : (π ◁ Cone.match (Image.normalized s)) =₂ raw
        projected-matching = isoComp-cong (post-inverse π αR)
            (postWhisker-isoComp-at π (H.base ◁ Cone.match s) αL) ∙
          postWhisker-isoComp-at π (αR ⁻¹) ((H.base ◁ Cone.match s) ∙ αL)

        raw-square : (final ∙ (l ∙ L)) =₂ ((r ∙ R) ∙ raw)
        raw-square = paste-squares
          (middle ∙ (π ◁ αL)) (middle₀ ∙ αL₀) ((π ◁ αR) ⁻¹) (αR₀ ⁻¹)
          (l ∙ L) v (r ∙ R)
          (paste-squares (π ◁ αL) αL₀ middle middle₀ (l ∙ L) u v
            (Left.Restrict.comparison left-computation (Cone.left s))
            ((substitution-square-projection π H.base H₀.base κ (Cone.match s)) ⁻¹))
          (move-square αR₀ (r ∙ R) v (π ◁ αR)
            (Right.Restrict.comparison right-computation (Cone.right s)))

    normalized-comparison : ConeIso (Read.read (Image.normalized s)) (Component.normalized s)
    normalized-comparison = record
      { leftIso = left-leg ; rightIso = right-leg
      ; compatible =
          isoComp-cong (idIso r)
            (isoComp-cong (idIso R) (isoComp-cong (projected-matching ⁻¹) (idIso (L ⁻¹)))) ∙
          remove-frame L R raw final l r raw-square }

    comparison : ConeIso (Read.read (H.mapCone s)) (H₀.mapCone s)
    comparison = coneIso-compose (Component.Normalization.comparison s)
      (coneIso-compose normalized-comparison
        (Read.read-iso (coneIso-inverse (Image.Normalization.comparison s))))
```
