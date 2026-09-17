# The pentagon for retained-route associators

All five parenthesizations receive fixed comparisons with the corresponding
parenthesized composites of retained functors. Each edge is checked against
the primitive associator before the common vertex comparisons are cancelled.

The theorem uses `compose-assoc pAn` at one common anima parameter. Comparing
this family with `internalAssoc`, which is obtained by restricting the
universal three-variable comparison, additionally requires compatibility
with change of parameter. This file does not identify those two choices
without that comparison.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Section01.Everything using (Theory)
import SCT.VolumeI.Chapter01.Section03.Setup as Setup
import SCT.VolumeI.Chapter01.Section03.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section03.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section03.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section03.CompositionPentagon as CompositionPentagon
import SCT.VolumeI.Chapter01.Section03.CoherenceTransport as CoherenceTransport
import SCT.VolumeI.Chapter01.Section02.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section03.InternalPentagon
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open CompositionPentagon 𝒯 M
open CoherenceTransport 𝒯
open Structural vocabulary terminal products productLaws composition whiskering
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idOuter; hcomp-idInner; pentagon-whiskered)

extend-square : {X Y : CAT} {a b a′ b′ a″ b″ : MAP X Y}
  (α : =₁ a b) (β : =₁ a′ b′) (γ : =₁ a″ b″)
  (p : =₁ a a′) (q : =₁ b b′) (p′ : =₁ a′ a″) (q′ : =₁ b′ b″)
  → =₂ (q ∙ α) (β ∙ p) → =₂ (q′ ∙ β) (γ ∙ p′)
  → =₂ ((q′ ∙ q) ∙ α) (γ ∙ (p′ ∙ p))
extend-square α β γ p q p′ q′ first second =
  isoComp-assoc-at γ p′ p ∙
  (isoComp-cong second (idIso p) ∙
  (invIso (isoComp-assoc-at q′ β p) ∙
  (isoComp-cong (idIso q′) first ∙ isoComp-assoc-at q′ q α)))

module Edges (P : CAT) (pAn : isAn P) where
  open RetainedEvaluation P
  open RetainedSquares P
  open RetainedNaturality P

  left-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₁ (retained (composeTerm (composeTerm h g) f))
        ((retained h ∘ retained g) ∘ retained f)
  left-comparison h g f = (retained-compose h g ▷ retained f) ∙ retained-compose (composeTerm h g) f

  right-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → =₁ (retained (composeTerm h (composeTerm g f)))
        (retained h ∘ (retained g ∘ retained f))
  right-comparison h g f = (retained h ◁ retained-compose g f) ∙ retained-compose h (composeTerm g f)

  abstract
    associator-square : {A B C D : CAT}
      (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
      → =₂ (right-comparison h g f ∙ retainedIso (compose-assoc pAn h g f))
          (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f)
    associator-square h g f =
      cancel-two-front (retained h ◁ retained-compose g f) (retained-compose h (composeTerm g f))
        (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f) ∙
        isoComp-cong (idIso (right-comparison h g f)) (compose-assoc-retained-β pAn h g f)

    prewhiskered-edge : {A B C : CAT}
      {g g′ : MAP P (Map B C)} (f : MAP P (Map A B))
      (α : =₁ g g′) {u v : MAP (P × B) (P × C)}
      (p : =₁ (retained g) u) (q : =₁ (retained g′) v) (β : =₁ u v)
      → =₂ (q ∙ retainedIso α) (β ∙ p)
      → =₂
          (((q ▷ retained f) ∙ retained-compose g′ f) ∙
            retainedIso (composeTerm-cong α (idIso f)))
          ((β ▷ retained f) ∙ ((p ▷ retained f) ∙ retained-compose g f))
    prewhiskered-edge {g = g} {g′} f α p q β square =
      let F = retained f
          c = retained-compose g f
          c′ = retained-compose g′ f
          image = composeTerm-cong α (idIso f)
          natural = isoComp-cong
            (hcomp-idInner (retainedIso α) F ∙ hcomp-cong (idIso (retainedIso α)) (retainedIso-id f))
            (idIso c) ∙ retained-compose-natural α (idIso f)
          pre-square = preWhisker-isoComp-at β p F ∙
            ((preWhisker F ◁ square) ∙ invIso (preWhisker-isoComp-at q (retainedIso α) F))
      in isoComp-assoc-at (β ▷ F) (p ▷ F) c ∙
        (isoComp-cong pre-square (idIso c) ∙
        (invIso (isoComp-assoc-at (q ▷ F) (retainedIso α ▷ F) c) ∙
        (isoComp-cong (idIso (q ▷ F)) natural ∙
          isoComp-assoc-at (q ▷ F) c′ (retainedIso image))))

    postwhiskered-edge : {A B C : CAT}
      (g : MAP P (Map B C)) {f f′ : MAP P (Map A B)}
      (α : =₁ f f′) {u v : MAP (P × A) (P × B)}
      (p : =₁ (retained f) u) (q : =₁ (retained f′) v) (β : =₁ u v)
      → =₂ (q ∙ retainedIso α) (β ∙ p)
      → =₂
          (((retained g ◁ q) ∙ retained-compose g f′) ∙
            retainedIso (composeTerm-cong (idIso g) α))
          ((retained g ◁ β) ∙ ((retained g ◁ p) ∙ retained-compose g f))
    postwhiskered-edge g {f} {f′} α p q β square =
      let G = retained g
          c = retained-compose g f
          c′ = retained-compose g f′
          image = composeTerm-cong (idIso g) α
          natural = isoComp-cong
            (hcomp-idOuter G (retainedIso α) ∙ hcomp-cong (retainedIso-id g) (idIso (retainedIso α)))
            (idIso c) ∙ retained-compose-natural (idIso g) α
          post-square = postWhisker-isoComp-at G β p ∙
            ((postWhisker G ◁ square) ∙ invIso (postWhisker-isoComp-at G q (retainedIso α)))
      in isoComp-assoc-at (G ◁ β) (G ◁ p) c ∙
        (isoComp-cong post-square (idIso c) ∙
        (invIso (isoComp-assoc-at (G ◁ q) (G ◁ retainedIso α) c) ∙
        (isoComp-cong (idIso (G ◁ q)) natural ∙
          isoComp-assoc-at (G ◁ q) c′ (retainedIso image))))
```

```agda
module PentagonCalculation {P A B C D E : CAT} (pAn : isAn P)
  (k : MAP P (Map D E)) (h : MAP P (Map C D))
  (g : MAP P (Map B C)) (f : MAP P (Map A B)) where
  open RetainedEvaluation P
  open RetainedSquares P
  open Edges P pAn

  K = retained k
  H = retained h
  G = retained g
  F = retained f
  kh = composeTerm k h
  hg = composeTerm h g
  gf = composeTerm g f
  ckh = retained-compose k h
  chg = retained-compose h g
  cgf = retained-compose g f

  α = compose-assoc pAn kh g f
  β = compose-assoc pAn k h gf
  γ = composeTerm-cong (compose-assoc pAn k h g) (idIso f)
  δ = compose-assoc pAn k hg f
  ε = composeTerm-cong (idIso k) (compose-assoc pAn h g f)

  p₀ : =₁ (retained (composeTerm (composeTerm kh g) f)) (((K ∘ H) ∘ G) ∘ F)
  p₀ = ((ckh ▷ G) ▷ F) ∙ left-comparison kh g f

  p₁ : =₁ (retained (composeTerm kh gf)) ((K ∘ H) ∘ (G ∘ F))
  p₁ = (ckh ▷ (G ∘ F)) ∙ right-comparison kh g f

  p₂ : =₁ (retained (composeTerm (composeTerm k hg) f)) ((K ∘ (H ∘ G)) ∘ F)
  p₂ = ((K ◁ chg) ▷ F) ∙ left-comparison k hg f

  p₃ : =₁ (retained (composeTerm k (composeTerm hg f))) (K ∘ ((H ∘ G) ∘ F))
  p₃ = (K ◁ (chg ▷ F)) ∙ right-comparison k hg f

  p₄ : =₁ (retained (composeTerm k (composeTerm h gf))) (K ∘ (H ∘ (G ∘ F)))
  p₄ = (K ◁ (H ◁ cgf)) ∙ right-comparison k h gf

  α′ = comp-assoc F G (K ∘ H)
  β′ = comp-assoc (G ∘ F) H K
  γ′ = comp-assoc G H K ▷ F
  δ′ = comp-assoc F (H ∘ G) K
  ε′ = K ◁ comp-assoc F G H

  abstract
    first-short-square : =₂ (p₁ ∙ retainedIso α) (α′ ∙ p₀)
    first-short-square = extend-square (retainedIso α) (comp-assoc F G (retained kh)) α′
      (left-comparison kh g f) (right-comparison kh g f)
      ((ckh ▷ G) ▷ F) (ckh ▷ (G ∘ F))
      (associator-square kh g f) (invIso (preWhisker-comp-at ckh G F))

    middle-long-square : =₂ (p₃ ∙ retainedIso δ) (δ′ ∙ p₂)
    middle-long-square = extend-square (retainedIso δ) (comp-assoc F (retained hg) K) δ′
      (left-comparison k hg f) (right-comparison k hg f)
      ((K ◁ chg) ▷ F) (K ◁ (chg ▷ F))
      (associator-square k hg f) (invIso (whisker-mixed-at chg F K))

    second-short-square : =₂ (p₄ ∙ retainedIso β) (β′ ∙ p₁)
    second-short-square =
      let alternative = ((K ∘ H) ◁ cgf) ∙ left-comparison k h gf
          comparison : =₂ p₁ alternative
          comparison = isoComp-assoc-at ((K ∘ H) ◁ cgf) (ckh ▷ retained gf) (retained-compose kh gf) ∙
            (isoComp-cong (interchange-at ckh cgf) (idIso (retained-compose kh gf)) ∙
              invIso (isoComp-assoc-at (ckh ▷ (G ∘ F)) (retained kh ◁ cgf) (retained-compose kh gf)))
          square = extend-square (retainedIso β) (comp-assoc (retained gf) H K) β′
            (left-comparison k h gf) (right-comparison k h gf)
            ((K ∘ H) ◁ cgf) (K ◁ (H ◁ cgf))
            (associator-square k h gf) (invIso (postWhisker-comp-at cgf H K))
      in isoComp-cong (idIso β′) (invIso comparison) ∙ square

    first-long-square : =₂ (p₂ ∙ retainedIso γ) (γ′ ∙ p₀)
    first-long-square =
      let a = left-comparison k h g
          b = right-comparison k h g
          cs = retained-compose (composeTerm kh g) f
          ct = retained-compose (composeTerm k hg) f
          source-normal : =₂ ((a ▷ F) ∙ cs) p₀
          source-normal = isoComp-assoc-at ((ckh ▷ G) ▷ F) (retained-compose kh g ▷ F) cs ∙
            isoComp-cong (preWhisker-isoComp-at (ckh ▷ G) (retained-compose kh g) F) (idIso cs)
          target-normal : =₂ ((b ▷ F) ∙ ct) p₂
          target-normal = isoComp-assoc-at ((K ◁ chg) ▷ F) (retained-compose k hg ▷ F) ct ∙
            isoComp-cong (preWhisker-isoComp-at (K ◁ chg) (retained-compose k hg) F) (idIso ct)
      in isoComp-cong (idIso γ′) source-normal ∙
        (prewhiskered-edge f (compose-assoc pAn k h g) a b (comp-assoc G H K)
          (associator-square k h g) ∙
          isoComp-cong (invIso target-normal) (idIso (retainedIso γ)))

    last-long-square : =₂ (p₄ ∙ retainedIso ε) (ε′ ∙ p₃)
    last-long-square =
      let a = left-comparison h g f
          b = right-comparison h g f
          cs = retained-compose k (composeTerm hg f)
          ct = retained-compose k (composeTerm h gf)
          source-normal : =₂ ((K ◁ a) ∙ cs) p₃
          source-normal = isoComp-assoc-at (K ◁ (chg ▷ F)) (K ◁ retained-compose hg f) cs ∙
            isoComp-cong (postWhisker-isoComp-at K (chg ▷ F) (retained-compose hg f)) (idIso cs)
          target-normal : =₂ ((K ◁ b) ∙ ct) p₄
          target-normal = isoComp-assoc-at (K ◁ (H ◁ cgf)) (K ◁ retained-compose h gf) ct ∙
            isoComp-cong (postWhisker-isoComp-at K (H ◁ cgf) (retained-compose h gf)) (idIso ct)
      in isoComp-cong (idIso ε′) source-normal ∙
        (postwhiskered-edge k (compose-assoc pAn h g f) a b (comp-assoc F G H)
          (associator-square h g f) ∙
          isoComp-cong (invIso target-normal) (idIso (retainedIso ε)))

  abstract
    pentagon : =₂ (β ∙ α) ((ε ∙ δ) ∙ γ)
    pentagon =
      let a = square-to-changeEndpoints p₀ p₁ (retainedIso α) α′ first-short-square
          b = square-to-changeEndpoints p₁ p₄ (retainedIso β) β′ second-short-square
          c = square-to-changeEndpoints p₀ p₂ (retainedIso γ) γ′ first-long-square
          d = square-to-changeEndpoints p₂ p₃ (retainedIso δ) δ′ middle-long-square
          e = square-to-changeEndpoints p₃ p₄ (retainedIso ε) ε′ last-long-square
          short-image = isoComp-cong b a ∙
            invIso (changeEndpoints-comp p₀ p₁ p₄ (retainedIso β) (retainedIso α))
          long-image = isoComp-cong (isoComp-cong e d) c ∙
            invIso (changeEndpoints-comp₃ p₀ p₂ p₃ p₄ (retainedIso ε) (retainedIso δ) (retainedIso γ))
          primitive-law = invIso (isoComp-assoc-at ε′ δ′ γ′) ∙ pentagon-whiskered F G H K
          retained-pentagon = changeEndpoints-reflect p₀ p₄
            (retainedIso β ∙ retainedIso α) ((retainedIso ε ∙ retainedIso δ) ∙ retainedIso γ)
            (invIso long-image ∙ (primitive-law ∙ short-image))
          long-expand = isoComp-cong (retainedIso-comp ε δ) (idIso (retainedIso γ)) ∙
            retainedIso-comp (ε ∙ δ) γ
      in retainedIso-reflect pAn (β ∙ α) ((ε ∙ δ) ∙ γ)
        (invIso long-expand ∙ (retained-pentagon ∙ retainedIso-comp β α))

compose-pentagon : {P A B C D E : CAT} (pAn : isAn P)
  (k : MAP P (Map D E)) (h : MAP P (Map C D))
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  → =₂
      (compose-assoc pAn k h (composeTerm g f) ∙ compose-assoc pAn (composeTerm k h) g f)
      ((composeTerm-cong (idIso k) (compose-assoc pAn h g f) ∙
        compose-assoc pAn k (composeTerm h g) f) ∙
        composeTerm-cong (compose-assoc pAn k h g) (idIso f))
compose-pentagon pAn k h g f = PentagonCalculation.pentagon pAn k h g f
```
