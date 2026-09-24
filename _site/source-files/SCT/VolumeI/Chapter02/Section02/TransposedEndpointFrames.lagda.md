# The endpoints of a transposed corner

A corner specified by two frames remains specified by those frames after
transposition and currying. The common comparison at the shared endpoint
cancels. This identifies the chosen matching, including its dependence on
the endpoint lifts.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter01.Section03.PairingNaturality as PN

module SCT.VolumeI.Chapter02.Section02.TransposedEndpointFrames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section07.Setup 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section07.IsomorphismLifting 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section06.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Cocones 𝒯
open import SCT.VolumeI.Chapter01.Section08.Transposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.TransposedSquareEvaluation 𝒯 M ℱ
  using (transposeIso-inverse)
open import SCT.VolumeI.Chapter01.Section08.CoconeTransposition 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section08.FunRestrictionCones 𝒯 M ℱ
open import SCT.VolumeI.Chapter02.Section01.FramedCocones 𝒯 using (framed-cocone)
import SCT.VolumeI.Chapter02.Section02.TransposedCornerComparisons as Corners
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left)

module FrameCalculus where
  abstract
    quotient-pre : {X C : CAT} {x y z x′ y′ : MAP X C}
      (a : x =₁ z) (b : y =₁ z) (l : x′ =₁ x) (r : y′ =₁ y) →
      ((b ∙ r) ⁻¹ ∙ (a ∙ l)) =₂ (r ⁻¹ ∙ ((b ⁻¹ ∙ a) ∙ l))
    quotient-pre a b l r =
      isoComp-cong (idIso (r ⁻¹)) ((isoComp-assoc-at (b ⁻¹) a l) ⁻¹) ∙
      (isoComp-assoc-at (r ⁻¹) (b ⁻¹) (a ∙ l) ∙
        isoComp-cong (inverse-composite b r) (idIso (a ∙ l)))

    quotient-common : {X C : CAT} {x y z w : MAP X C}
      (a : x =₁ z) (b : y =₁ z) (c : z =₁ w) →
      ((c ∙ b) ⁻¹ ∙ (c ∙ a)) =₂ (b ⁻¹ ∙ a)
    quotient-common a b c = isoComp-cong (idIso (b ⁻¹)) (cancel-left c a) ∙
      (isoComp-assoc-at (b ⁻¹) (c ⁻¹) (c ∙ a) ∙
        isoComp-cong (inverse-composite c b) (idIso (c ∙ a)))

open FrameCalculus

module FramedCorner {Γ A B C : CAT}
  (f : MAP A (Fun Γ C)) (g : MAP B (Fun Γ C))
  (u : Obj-abs A) (v : Obj-abs B) (z : Obj-abs (Fun Γ C))
  (α : (f ∘ u) =₁ z) (β : (g ∘ v) =₁ z) where
  module Left = Corners.Edge 𝒯 M ℱ P f u z α
  module Right = Corners.Edge 𝒯 M ℱ P g v z β
  transposed = transposeCocone (framed-cocone f g α β)
  module Curried = CurryRestriction transposed
  left-frame = Left.comparison
  right-frame = Right.comparison
  αᵗ = transposeIso α
  βᵗ = transposeIso β
  l = transpose-pre u f
  r = transpose-pre v g
  cf = funCurry-β (transpose f) ▷ productMap (id Γ) u
  cg = funCurry-β (transpose g) ▷ productMap (id Γ) v
  cz = funCurry-β (transpose z)
  qf = Curried.leftChange
  qg = Curried.rightChange
  first-frame = αᵗ ∙ l ⁻¹
  second-frame = βᵗ ∙ r ⁻¹
  first-lift = first-frame ∙ cf
  second-lift = second-frame ∙ cg
  first-raw = first-lift ∙ qf
  second-raw = second-lift ∙ qg

  abstract
    transposed-matching : (Cocone.match transposed) =₂ (second-frame ⁻¹ ∙ first-frame)
    transposed-matching = (quotient-pre αᵗ βᵗ (l ⁻¹) (r ⁻¹)) ⁻¹ ∙
      (isoComp-cong ((inverse-inverse r) ⁻¹) (idIso ((βᵗ ⁻¹ ∙ αᵗ) ∙ l ⁻¹)) ∙
        isoComp-cong (idIso r)
          (isoComp-cong
            (isoComp-cong (transposeIso-inverse β) (idIso αᵗ) ∙ transposeIso-comp (β ⁻¹) α)
            (idIso (l ⁻¹))))

    retargeted-matching : Curried.desired =₂ (second-lift ⁻¹ ∙ first-lift)
    retargeted-matching = (quotient-pre first-frame second-frame cf cg) ⁻¹ ∙
      isoComp-cong (pre-inverse (funCurry-β (transpose g)) (productMap (id Γ) v))
        (isoComp-cong transposed-matching
          (inverse-inverse cf ∙
            (＝-inv ◁ pre-inverse (funCurry-β (transpose f)) (productMap (id Γ) u))))

    raw-matching : Curried.rawMatch =₂ (second-raw ⁻¹ ∙ first-raw)
    raw-matching = (quotient-pre first-lift second-lift qf qg) ⁻¹ ∙
      isoComp-cong (idIso (qg ⁻¹)) (isoComp-cong retargeted-matching (idIso qf))

    left-raw : (cz ⁻¹ ∙ first-raw) =₂ Left.raw
    left-raw = isoComp-cong (idIso (cz ⁻¹))
      (isoComp-cong (idIso αᵗ) (isoComp-assoc-at (l ⁻¹) cf qf) ∙
        (isoComp-assoc-at αᵗ (l ⁻¹ ∙ cf) qf ∙
          isoComp-cong (isoComp-assoc-at αᵗ (l ⁻¹) cf) (idIso qf)))

    right-raw : (cz ⁻¹ ∙ second-raw) =₂ Right.raw
    right-raw = isoComp-cong (idIso (cz ⁻¹))
      (isoComp-cong (idIso βᵗ) (isoComp-assoc-at (r ⁻¹) cg qg) ∙
        (isoComp-assoc-at βᵗ (r ⁻¹ ∙ cg) qg ∙
          isoComp-cong (isoComp-assoc-at βᵗ (r ⁻¹) cg) (idIso qg)))

    raw-frames : Curried.rawMatch =₂ (Right.raw ⁻¹ ∙ Left.raw)
    raw-frames = isoComp-cong (＝-inv ◁ right-raw) left-raw ∙
      ((quotient-common first-raw second-raw (cz ⁻¹)) ⁻¹ ∙ raw-matching)

    matching : (Cone.match Curried.value) =₂ (right-frame ⁻¹ ∙ left-frame)
    matching = funReflect-Iso₂ _ _
      ((funUncurryIso-comp (right-frame ⁻¹) left-frame) ⁻¹ ∙
        (isoComp-cong ((funUncurryIso-inverse right-frame) ⁻¹)
          (idIso (funUncurryIso left-frame)) ∙
        (isoComp-cong (＝-inv ◁ (Right.comparison-β ⁻¹)) (Left.comparison-β ⁻¹) ∙
          (raw-frames ∙ funIsoReflect-β _ _ Curried.rawMatch))))
```
