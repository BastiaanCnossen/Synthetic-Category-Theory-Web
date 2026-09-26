# The diagonal formulation of representability

The representability assumption is the manuscript's fiber square. Here we
derive the diagonal square using pullback symmetry and the lifting criterion.
Its matching has normalized coordinates `(identity, identification)`. Both
coordinate equations and compatibility with restriction are proved, so this
is a statement about the specified square, not just its four corners.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.RepresentabilityDiagonal
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.Representability 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
  using (coneSwap; cone-match-change)
open import SCT.VolumeI.Chapter01.Section06.PullbackCriterion 𝒯 P using (cone-isPullback-from-lifting)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.PointDiagonalCoordinates 𝒯 using (module Coordinates)
open import SCT.VolumeI.Chapter01.Section06.Coordinates.PointDiagonalRestriction 𝒯 using (module Restriction)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ComparisonSquares 𝒯 using (decode-encode)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)

opaque
  normalized-inverse : {T X Y : CAT} (π : MAP X Y)
    {u v : MAP T X} {x y : MAP T Y}
    (L : (π ∘ u) =₁ x) (R : (π ∘ v) =₁ y) (q : u =₁ v) →
    (L ∙ ((π ◁ q ⁻¹) ∙ R ⁻¹)) =₂ ((R ∙ ((π ◁ q) ∙ L ⁻¹)) ⁻¹)
  normalized-inverse π {u = u} {v} L R q = calculation ⁻¹ ∙
    isoComp-cong (idIso L) (isoComp-cong (post-inverse π q) (idIso (R ⁻¹)))
    where
    z : (π ∘ u) =₁ (π ∘ v)
    z = π ◁ q
    calculation : ((R ∙ (z ∙ L ⁻¹)) ⁻¹) =₂ (L ∙ (z ⁻¹ ∙ R ⁻¹))
    calculation = isoComp-assoc-at L (z ⁻¹) (R ⁻¹) ∙
      (isoComp-cong
        (isoComp-cong (inverse-inverse L) (idIso (z ⁻¹)) ∙ inverse-composite z (L ⁻¹))
        (idIso (R ⁻¹)) ∙ inverse-composite R (z ∙ L ⁻¹))

module Diagonal (R : Representability) {E : CAT} (a b : Obj-abs E) where
  open Representability R
  open Coordinates a b

  ε = identification a b
  p = terminate (a ＝ b)
  v = const {P = a ＝ b} a

  first = (right₁ v) ⁻¹ ∙ (idIso v ∙ left₁ p)
  second = (right₂ v) ⁻¹ ∙ (ε ⁻¹ ∙ left₂ p)

  reversed-square : Cone F Δ (a ＝ b)
  reversed-square = record { left = p ; right = v ; match = pair-iso first second }

  opaque
    reversed-first : (edge₁ reversed-square) =₂ (idIso v)
    reversed-first = decode-encode (left₁ p) (right₁ v) (idIso v) ∙
      isoComp-cong (idIso (right₁ v))
        (isoComp-cong (pair-iso-β₁ first second) (idIso ((left₁ p) ⁻¹)))

    reversed-second : (edge₂ reversed-square) =₂ (ε ⁻¹)
    reversed-second = decode-encode (left₂ p) (right₂ v) (ε ⁻¹) ∙
      isoComp-cong (idIso (right₂ v))
        (isoComp-cong (pair-iso-β₂ first second) (idIso ((left₂ p) ⁻¹)))

    recovered-matching : (Cone.match (from reversed-square)) =₂ ((ε ⁻¹) ⁻¹)
    recovered-matching = isoComp-unitʳ-at ((ε ⁻¹) ⁻¹) ∙
      isoComp-cong (＝-inv ◁ reversed-second) reversed-first

    recovered-isPullback : IsPullback (from reversed-square)
    recovered-isPullback = pullback-cone-invariant
      (coneIso-inverse (cone-match-change p p _ _ recovered-matching))
      (pullback-swap (identification-square a b ε) (identification-isPullback a b))

  module Original = UniversalCone (from reversed-square) recovered-isPullback
  target = pullbackCone F Δ
  inverse = Original.factor (from target)

  opaque
    factorization : ConeIso (conePre inverse reversed-square) target
    factorization = from-reflect
      (coneIso-compose (Original.factor-β (from target))
        (Restriction.comparison a b reversed-square inverse))

    reflect-comparisons : (h k : MAP (a ＝ b) (a ＝ b))
      → ConeIso (conePre h reversed-square) (conePre k reversed-square) → h =₁ k
    reflect-comparisons h k Φ = Original.reflect h k
      (coneIso-compose (Restriction.comparison a b reversed-square k)
        (coneIso-compose (from-iso Φ)
          (coneIso-inverse (Restriction.comparison a b reversed-square h))))

    reversed-isPullback : IsPullback reversed-square
    reversed-isPullback = cone-isPullback-from-lifting reversed-square inverse
      factorization reflect-comparisons

  diagonal-square : Cone Δ F (a ＝ b)
  diagonal-square = coneSwap reversed-square

  opaque
    diagonal-first :
      (left₁ p ∙ ((pr₁ ◁ Cone.match diagonal-square) ∙ (right₁ v) ⁻¹)) =₂ (idIso v)
    diagonal-first = inverse-identity v ∙
      ((＝-inv ◁ reversed-first) ∙ normalized-inverse pr₁ (left₁ p) (right₁ v) (Cone.match reversed-square))

    diagonal-second :
      (left₂ p ∙ ((pr₂ ◁ Cone.match diagonal-square) ∙ (right₂ v) ⁻¹)) =₂ ε
    diagonal-second = inverse-inverse ε ∙
      ((＝-inv ◁ reversed-second) ∙ normalized-inverse pr₂ (left₂ p) (right₂ v) (Cone.match reversed-square))

    diagonal-isPullback : IsPullback diagonal-square
    diagonal-isPullback = pullback-swap reversed-square reversed-isPullback
```
