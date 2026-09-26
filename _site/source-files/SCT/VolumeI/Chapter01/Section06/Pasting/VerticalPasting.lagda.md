# Vertical pasting with the specified matching

Transpose the ordinary pasting lemma and normalize its matching. This
version retains the usual composite naturality square, including its
associators, and is useful for endpoint evaluation squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Pasting.VerticalPasting
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (IsPullback; pullback-cone-invariant)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma 𝒯 P using (module Pasting)

module Vertical {X Y Z A B C : CAT} (f : MAP A B) (g : MAP B C)
  (r : MAP Z C) (t : Cone r g Y) (s : Cone (Cone.right t) f X)
  (et : IsPullback t) where
  q = Cone.right t
  F = Cone.left s
  p = Cone.right s
  G = Cone.left t
  α = Cone.match s
  β = Cone.match t
  assocBase = comp-assoc p f g
  n = Cone.match (conePre F t)
  j = Cone.match (conePre F (coneSwap t))
  u = g ◁ α
  v = g ◁ (α ⁻¹)
  module Paste = Pasting f g r (coneSwap t) (pullback-swap t et)
  raw = coneSwap (Paste.Paste.flatten (coneSwap s))

  square : Cone r (g ∘ f) X
  square = record { left = G ∘ F ; right = p ; match = assocBase ⁻¹ ∙ (u ∙ n) }

  private
    assocRight = comp-assoc F q g
    assocLeft = comp-assoc F G r
    b = β ▷ F

    abstract
      restriction-inverse : j =₂ (n ⁻¹)
      restriction-inverse = expanded ⁻¹ ∙ isoComp-cong (idIso assocLeft)
        (isoComp-cong (pre-inverse β F) (idIso (assocRight ⁻¹)))
        where
        expanded : (n ⁻¹) =₂ (assocLeft ∙ ((b ⁻¹) ∙ (assocRight ⁻¹)))
        expanded = isoComp-assoc-at assocLeft (b ⁻¹) (assocRight ⁻¹) ∙
          isoComp-cong (isoComp-cong (inverse-inverse assocLeft) (idIso (b ⁻¹))) (idIso (assocRight ⁻¹)) ∙
          isoComp-cong (inverse-composite b (assocLeft ⁻¹)) (idIso (assocRight ⁻¹)) ∙
          inverse-composite assocRight (b ∙ assocLeft ⁻¹)

    abstract
      normalization : Cone.match raw =₂ Cone.match square
      normalization = isoComp-assoc-at (assocBase ⁻¹) u n ∙
        isoComp-cong
          (isoComp-cong (idIso (assocBase ⁻¹))
            (inverse-inverse u ∙ (＝-inv ◁ post-inverse g α)))
          (inverse-inverse n ∙ (＝-inv ◁ restriction-inverse)) ∙
        isoComp-cong (inverse-composite v assocBase) (idIso (j ⁻¹)) ∙
        inverse-composite j (v ∙ assocBase)

  comparison : ConeIso raw square
  comparison = cone-match-change _ _ _ _ normalization

  abstract
    square-isPullback : IsPullback s → IsPullback square
    square-isPullback es = pullback-cone-invariant comparison
      (pullback-swap (Paste.Paste.flatten (coneSwap s))
        (Paste.paste-isPullback (coneSwap s) (pullback-swap s es)))

    cancel-isPullback : IsPullback square → IsPullback s
    cancel-isPullback e = pullback-cone-invariant (coneSwap-swap s)
      (pullback-swap (coneSwap s)
        (Paste.cancel-isPullback (coneSwap s)
          (pullback-cone-invariant (coneSwap-swap (Paste.Paste.flatten (coneSwap s)))
            (pullback-swap raw (pullback-cone-invariant (coneIso-inverse comparison) e)))))
```
