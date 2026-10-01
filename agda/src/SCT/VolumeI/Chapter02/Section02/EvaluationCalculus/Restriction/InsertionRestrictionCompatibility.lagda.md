# Insertion commutes with restricting the diagram shape

The two paths below start at `L_Y ∘ (insert x ∘ h)`. One restricts the
inserted vertex before changing parameter; the other moves the parameter
past the restriction and then inserts the restricted vertex. We compare
these paths with both product projections retained.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projection
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductFirstCoordinate as First
import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProductSecondCoordinate as Second
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionProjectionWitnesses as Witnesses
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions as Restriction
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionRestrictionCompatibility
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯
  using (section-image; section-lift-compose; section-square)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M
  using (constant-image; constant-image-pre)
open Restriction 𝒯 M ℱ using (insertion)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-left-reflect)
open import SCT.VolumeI.Chapter01.Section08.ProductCalculus.ProjectionBaseCalculus 𝒯 using (change-middle)
open Pairing vocabulary terminal products productLaws composition vertical whiskering using (pair-iso-extensionality)
module PS = Projection 𝒯
  using (Square; associator-square; compose-base; compose-square; inverse-square; lift-base; lift-compose; lift-square; post-square; pre-square)

module RestrictionFirst {A B : CAT} (X : CAT) (r : MAP A B) (x : Obj-abs A) where
  i = insert {X = X} x
  L = productMap (id X) r
  β = pair-β₁ (id X) (const x)
  bL = pair-β₁ (id X ∘ pr₁) (r ∘ pr₂)
  tail = (comp-assoc i L pr₁) ⁻¹
  source = PS.compose-base pr₁ L (First.restriction-base 𝒯 M X r) i β

  abstract
    square : PS.Square pr₁ source (pair-β₁ (id X) (const (r ∘ x))) (insertion X r x)
    square = normalize ∙ Restriction.At.projection₁ 𝒯 M ℱ X r x
      where
      normalize : (Restriction.At.first 𝒯 M ℱ X r x ∙ ((bL ▷ i) ∙ tail)) =₂ source
      normalize = isoComp-cong (idIso β)
          (isoComp-cong ((preWhisker-isoComp-at (comp-unitˡ pr₁) bL i) ⁻¹) (idIso tail)) ∙
        (isoComp-cong (idIso β) ((isoComp-assoc-at (comp-unitˡ pr₁ ▷ i) (bL ▷ i) tail) ⁻¹) ∙
        (isoComp-assoc-at β (comp-unitˡ pr₁ ▷ i) ((bL ▷ i) ∙ tail) ∙
          isoComp-cong (Restriction.At.first-normalization 𝒯 M ℱ X r x) (idIso ((bL ▷ i) ∙ tail))))

module At {X Y A B : CAT} (h : MAP X Y) (r : MAP A B) (x : Obj-abs A) where
  HA = productMap h (id A)
  HB = productMap h (id B)
  LX = productMap (id X) r
  LY = productMap (id Y) r
  ix = insert {X = X} x
  iy = insert {X = Y} x
  jx = insert {X = X} (r ∘ x)
  jy = insert {X = Y} (r ∘ x)
  χX = insertion X r x
  χY = insertion Y r x
  separation = productMap-separate h r
  left = insert-natural h (r ∘ x) ∙ ((χY ▷ h) ∙ (comp-assoc h iy LY) ⁻¹)
  right = (HB ◁ χX) ∙ (comp-assoc ix LX HB ∙
    ((separation ▷ ix) ∙ ((comp-assoc ix HA LY) ⁻¹ ∙ (LY ◁ insert-natural h x))))

  module FirstProjection where
    bLX = First.restriction-base 𝒯 M X r
    bLY = First.restriction-base 𝒯 M Y r
    bHA = First.parameter-base 𝒯 M h A
    bHB = First.parameter-base 𝒯 M h B
    bLXh = First.restriction-over 𝒯 M h r
    bix = pair-β₁ (id X) (const x)
    biy = pair-β₁ (id Y) (const x)
    bjx = pair-β₁ (id X) (const (r ∘ x))
    bjy = pair-β₁ (id Y) (const (r ∘ x))
    sx = section-image pr₁ ix bix h
    tx = section-image pr₁ jx bjx h
    incoming = Witnesses.Parameter.incoming₁ 𝒯 M ℱ h x
    outgoing = Witnesses.Parameter.outgoing₁ 𝒯 M ℱ h x
    final = Witnesses.Parameter.outgoing₁ 𝒯 M ℱ h (r ∘ x)
    b₀ = PS.compose-base pr₁ LY bLY (iy ∘ h) incoming
    b₁ = PS.compose-base pr₁ LY bLY (HA ∘ ix) outgoing
    b₂ = PS.compose-base pr₁ (LY ∘ HA) (PS.compose-base pr₁ LY bLY HA bHA) ix sx
    b₃ = PS.compose-base pr₁ (HB ∘ LX) (PS.compose-base pr₁ HB bHB LX bLXh) ix sx
    b₄ = PS.compose-base pr₁ HB bHB (LX ∘ ix) (PS.compose-base (h ∘ pr₁) LX bLXh ix sx)

    abstract
      restricted-section : PS.Square (h ∘ pr₁)
        (PS.compose-base (h ∘ pr₁) LX bLXh ix sx) tx χX
      restricted-section = (section-lift-compose pr₁ pr₁ LX ix bLX bix h) ⁻¹ ∙
        section-square pr₁ (RestrictionFirst.source X r x) bjx χX h (RestrictionFirst.square X r x)

      right-square : PS.Square pr₁ b₀ final right
      right-square = PS.compose-square pr₁ b₀ b₄ final (HB ◁ χX) _
        (PS.post-square pr₁ HB bHB _ tx χX restricted-section)
        (PS.compose-square pr₁ b₀ b₃ b₄ (comp-assoc ix LX HB) _
          (PS.associator-square pr₁ HB LX ix bHB bLXh sx)
          (PS.compose-square pr₁ b₀ b₂ b₃ (separation ▷ ix) _
            (PS.pre-square pr₁ ix _ _ sx separation (First.separation 𝒯 M h r))
            (PS.compose-square pr₁ b₀ b₁ b₂ ((comp-assoc ix HA LY) ⁻¹) _
              (PS.inverse-square pr₁ b₂ b₁ (comp-assoc ix HA LY)
                (PS.associator-square pr₁ LY HA ix bLY bHA sx))
              (PS.post-square pr₁ LY bLY incoming outgoing (insert-natural h x)
                (Witnesses.Parameter.projection₁ 𝒯 M ℱ h x)))))

      left-square : PS.Square pr₁ b₀ final left
      left-square = PS.compose-square pr₁ b₀
        (Witnesses.Parameter.incoming₁ 𝒯 M ℱ h (r ∘ x)) final (insert-natural h (r ∘ x)) _
        (Witnesses.Parameter.projection₁ 𝒯 M ℱ h (r ∘ x))
        (PS.compose-square pr₁ b₀
          (PS.compose-base pr₁ (LY ∘ iy) (RestrictionFirst.source Y r x) h (comp-unitˡ h))
          (Witnesses.Parameter.incoming₁ 𝒯 M ℱ h (r ∘ x)) (χY ▷ h) _
          (PS.pre-square pr₁ h (RestrictionFirst.source Y r x) bjy (comp-unitˡ h) χY
            (RestrictionFirst.square Y r x))
          (PS.inverse-square pr₁ _ b₀ (comp-assoc h iy LY)
            (PS.associator-square pr₁ LY iy h bLY biy (comp-unitˡ h))))

      comparison : (pr₁ ◁ left) =₂ (pr₁ ◁ right)
      comparison = cancel-left-reflect final (right-square ⁻¹ ∙ left-square)

  module SecondProjection where
    bLX = Second.restriction-base 𝒯 M X r
    bLY = Second.restriction-base 𝒯 M Y r
    bHA = Second.parameter-base 𝒯 M h A
    bHB = Second.parameter-base 𝒯 M h B
    bHAr = PS.lift-base r pr₂ HA bHA
    bix = pair-β₂ (id X) (const x)
    biy = pair-β₂ (id Y) (const x)
    bjx = pair-β₂ (id X) (const (r ∘ x))
    bjy = pair-β₂ (id Y) (const (r ∘ x))
    cx = constant-image X r x
    cy = constant-image Y r x
    objectX = cx ∙ PS.lift-base r pr₂ ix bix
    objectY = cy ∙ PS.lift-base r pr₂ iy biy
    incoming = Witnesses.Parameter.incoming₂ 𝒯 M ℱ h x
    outgoing = Witnesses.Parameter.normalized-outgoing₂ 𝒯 M ℱ h x
    objectInput = PS.compose-base (r ∘ pr₂) iy objectY h (const-pre (r ∘ x) h)
    objectOutput = PS.compose-base (r ∘ pr₂) HA bHAr ix objectX
    restrictionX = PS.compose-base pr₂ LX bLX ix objectX
    restrictionY = PS.compose-base pr₂ LY bLY iy objectY
    final = Witnesses.Parameter.normalized-outgoing₂ 𝒯 M ℱ h (r ∘ x)
    b₀ = PS.compose-base pr₂ LY bLY (iy ∘ h) objectInput
    b₁ = PS.compose-base pr₂ LY bLY (HA ∘ ix) objectOutput
    b₂ = PS.compose-base pr₂ (LY ∘ HA) (PS.compose-base pr₂ LY bLY HA bHAr) ix objectX
    b₃ = PS.compose-base pr₂ (HB ∘ LX) (PS.compose-base pr₂ HB bHB LX bLX) ix objectX
    b₄ = PS.compose-base pr₂ HB bHB (LX ∘ ix) restrictionX

    abstract
      source-normalization : objectInput =₂ (cx ∙ PS.lift-base r pr₂ (iy ∘ h) incoming)
      source-normalization = isoComp-cong (idIso cx)
          (PS.lift-compose r pr₂ iy h biy (const-pre x h)) ∙
        change-middle (r ∘ pr₂) iy h (PS.lift-base r pr₂ iy biy)
          (PS.lift-base r (const x) h (const-pre x h)) cy (const-pre (r ∘ x) h) cx
          ((constant-image-pre h r x) ⁻¹)

      target-normalization : objectOutput =₂ (cx ∙ PS.lift-base r pr₂ (HA ∘ ix) outgoing)
      target-normalization = isoComp-cong (idIso cx) (PS.lift-compose r pr₂ HA ix bHA bix) ∙
        isoComp-assoc-at cx (PS.lift-base r pr₂ ix bix)
          ((bHAr ▷ ix) ∙ (comp-assoc ix HA (r ∘ pr₂)) ⁻¹)

      insertion-square : PS.Square (r ∘ pr₂) objectInput objectOutput (insert-natural h x)
      insertion-square = source-normalization ⁻¹ ∙
        (isoComp-cong (idIso cx)
          (PS.lift-square r pr₂ incoming outgoing (insert-natural h x)
            (Witnesses.Parameter.normalized-projection₂ 𝒯 M ℱ h x)) ∙
        (isoComp-assoc-at cx (PS.lift-base r pr₂ (HA ∘ ix) outgoing)
          ((r ∘ pr₂) ◁ insert-natural h x) ∙
          isoComp-cong target-normalization (idIso ((r ∘ pr₂) ◁ insert-natural h x))))

      right-square : PS.Square pr₂ b₀ final right
      right-square = PS.compose-square pr₂ b₀ b₄ final (HB ◁ χX) _
        (PS.post-square pr₂ HB bHB restrictionX bjx χX (Restriction.At.projection₂ 𝒯 M ℱ X r x))
        (PS.compose-square pr₂ b₀ b₃ b₄ (comp-assoc ix LX HB) _
          (PS.associator-square pr₂ HB LX ix bHB bLX objectX)
          (PS.compose-square pr₂ b₀ b₂ b₃ (separation ▷ ix) _
            (PS.pre-square pr₂ ix _ _ objectX separation (Second.separation 𝒯 M h r))
            (PS.compose-square pr₂ b₀ b₁ b₂ ((comp-assoc ix HA LY) ⁻¹) _
              (PS.inverse-square pr₂ b₂ b₁ (comp-assoc ix HA LY)
                (PS.associator-square pr₂ LY HA ix bLY bHAr objectX))
              (PS.post-square pr₂ LY bLY objectInput objectOutput (insert-natural h x) insertion-square))))

      left-square : PS.Square pr₂ b₀ final left
      left-square = PS.compose-square pr₂ b₀
        (Witnesses.Parameter.incoming₂ 𝒯 M ℱ h (r ∘ x)) final (insert-natural h (r ∘ x)) _
        (Witnesses.Parameter.normalized-projection₂ 𝒯 M ℱ h (r ∘ x))
        (PS.compose-square pr₂ b₀
          (PS.compose-base pr₂ (LY ∘ iy) restrictionY h (const-pre (r ∘ x) h))
          (Witnesses.Parameter.incoming₂ 𝒯 M ℱ h (r ∘ x)) (χY ▷ h) _
          (PS.pre-square pr₂ h restrictionY bjy (const-pre (r ∘ x) h) χY
            (Restriction.At.projection₂ 𝒯 M ℱ Y r x))
          (PS.inverse-square pr₂ _ b₀ (comp-assoc h iy LY)
            (PS.associator-square pr₂ LY iy h bLY objectY (const-pre (r ∘ x) h))))

      comparison : (pr₂ ◁ left) =₂ (pr₂ ◁ right)
      comparison = cancel-left-reflect final (right-square ⁻¹ ∙ left-square)

  abstract
    comparison : left =₂ right
    comparison = pair-iso-extensionality FirstProjection.comparison SecondProjection.comparison
```
