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
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.Setup as Setup
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as MappingAnimae
import SCT.VolumeI.Chapter01.Section04.Composition as MapComposition
import SCT.VolumeI.Chapter01.Section04.InternalCoherence as InternalCoherence
import SCT.VolumeI.Chapter01.Section04.RetainedComparisonLaws as RetainedComparisonLaws
import SCT.VolumeI.Chapter01.Section04.CoherenceTransport as CoherenceTransport
import SCT.VolumeI.Chapter01.Section03.Structural as Structural
import SCT.VolumeI.Chapter01.Section03.IteratedPairing as IteratedPairing

module SCT.VolumeI.Chapter01.Section04.InternalPentagon
  {c m a : Level} (𝒯 : Theory c m a)
  (M : MappingAnimae.MappingAnimae 𝒯) where

open Setup 𝒯
open MappingAnimae.MappingAnimae M
open MapComposition 𝒯 M
open InternalCoherence 𝒯 M
open RetainedComparisonLaws 𝒯 M
open CoherenceTransport 𝒯
open Structural vocabulary terminal products productLaws composition whiskering
open IteratedPairing vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (hcomp-idOuter; hcomp-idInner; pentagon-whiskered)

extend-square : {X Y : CAT} {a b a′ b′ a″ b″ : MAP X Y}
  (α : a =₁ b) (β : a′ =₁ b′) (γ : a″ =₁ b″)
  (p : a =₁ a′) (q : b =₁ b′) (p′ : a′ =₁ a″) (q′ : b′ =₁ b″)
  → (q ∙ α) =₂ (β ∙ p) → (q′ ∙ β) =₂ (γ ∙ p′)
  → ((q′ ∙ q) ∙ α) =₂ (γ ∙ (p′ ∙ p))
extend-square α β γ p q p′ q′ first second =
  isoComp-assoc-at γ p′ p ∙
  (isoComp-cong second (idIso p) ∙
  ((isoComp-assoc-at q′ β p) ⁻¹ ∙
  (isoComp-cong (idIso q′) first ∙ isoComp-assoc-at q′ q α)))

module Edges (P : CAT) (pAn : isAn P) where
  open RetainedEvaluation P
  open RetainedSquares P
  open RetainedNaturality P

  left-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → (retained (composeTerm (composeTerm h g) f)) =₁
        ((retained h ∘ retained g) ∘ retained f)
  left-comparison h g f = (retained-compose h g ▷ retained f) ∙ retained-compose (composeTerm h g) f

  right-comparison : {A B C D : CAT}
    (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
    → (retained (composeTerm h (composeTerm g f))) =₁
        (retained h ∘ (retained g ∘ retained f))
  right-comparison h g f = (retained h ◁ retained-compose g f) ∙ retained-compose h (composeTerm g f)

  abstract
    associator-square : {A B C D : CAT}
      (h : MAP P (Map C D)) (g : MAP P (Map B C)) (f : MAP P (Map A B))
      → (right-comparison h g f ∙ retainedIso (compose-assoc pAn h g f)) =₂
          (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f)
    associator-square h g f =
      cancel-two-front (retained h ◁ retained-compose g f) (retained-compose h (composeTerm g f))
        (comp-assoc (retained f) (retained g) (retained h) ∙ left-comparison h g f) ∙
        isoComp-cong (idIso (right-comparison h g f)) (compose-assoc-retained-β pAn h g f)

    prewhiskered-edge : {A B C : CAT}
      {g g′ : MAP P (Map B C)} (f : MAP P (Map A B))
      (α : g =₁ g′) {u v : MAP (P × B) (P × C)}
      (p : (retained g) =₁ u) (q : (retained g′) =₁ v) (β : u =₁ v)
      → (q ∙ retainedIso α) =₂ (β ∙ p)
      →
          (((q ▷ retained f) ∙ retained-compose g′ f) ∙
            retainedIso (composeTerm-cong α (idIso f))) =₂
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
            ((preWhisker F ◁ square) ∙ (preWhisker-isoComp-at q (retainedIso α) F) ⁻¹)
      in isoComp-assoc-at (β ▷ F) (p ▷ F) c ∙
        (isoComp-cong pre-square (idIso c) ∙
        ((isoComp-assoc-at (q ▷ F) (retainedIso α ▷ F) c) ⁻¹ ∙
        (isoComp-cong (idIso (q ▷ F)) natural ∙
          isoComp-assoc-at (q ▷ F) c′ (retainedIso image))))

    postwhiskered-edge : {A B C : CAT}
      (g : MAP P (Map B C)) {f f′ : MAP P (Map A B)}
      (α : f =₁ f′) {u v : MAP (P × A) (P × B)}
      (p : (retained f) =₁ u) (q : (retained f′) =₁ v) (β : u =₁ v)
      → (q ∙ retainedIso α) =₂ (β ∙ p)
      →
          (((retained g ◁ q) ∙ retained-compose g f′) ∙
            retainedIso (composeTerm-cong (idIso g) α)) =₂
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
            ((postWhisker G ◁ square) ∙ (postWhisker-isoComp-at G q (retainedIso α)) ⁻¹)
      in isoComp-assoc-at (G ◁ β) (G ◁ p) c ∙
        (isoComp-cong post-square (idIso c) ∙
        ((isoComp-assoc-at (G ◁ q) (G ◁ retainedIso α) c) ⁻¹ ∙
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

  p₀ : (retained (composeTerm (composeTerm kh g) f)) =₁ (((K ∘ H) ∘ G) ∘ F)
  p₀ = ((ckh ▷ G) ▷ F) ∙ left-comparison kh g f

  p₁ : (retained (composeTerm kh gf)) =₁ ((K ∘ H) ∘ (G ∘ F))
  p₁ = (ckh ▷ (G ∘ F)) ∙ right-comparison kh g f

  p₂ : (retained (composeTerm (composeTerm k hg) f)) =₁ ((K ∘ (H ∘ G)) ∘ F)
  p₂ = ((K ◁ chg) ▷ F) ∙ left-comparison k hg f

  p₃ : (retained (composeTerm k (composeTerm hg f))) =₁ (K ∘ ((H ∘ G) ∘ F))
  p₃ = (K ◁ (chg ▷ F)) ∙ right-comparison k hg f

  p₄ : (retained (composeTerm k (composeTerm h gf))) =₁ (K ∘ (H ∘ (G ∘ F)))
  p₄ = (K ◁ (H ◁ cgf)) ∙ right-comparison k h gf

  α′ = comp-assoc F G (K ∘ H)
  β′ = comp-assoc (G ∘ F) H K
  γ′ = comp-assoc G H K ▷ F
  δ′ = comp-assoc F (H ∘ G) K
  ε′ = K ◁ comp-assoc F G H

  abstract
    first-short-square : (p₁ ∙ retainedIso α) =₂ (α′ ∙ p₀)
    first-short-square = extend-square (retainedIso α) (comp-assoc F G (retained kh)) α′
      (left-comparison kh g f) (right-comparison kh g f)
      ((ckh ▷ G) ▷ F) (ckh ▷ (G ∘ F))
      (associator-square kh g f) ((preWhisker-comp-at ckh G F) ⁻¹)

    middle-long-square : (p₃ ∙ retainedIso δ) =₂ (δ′ ∙ p₂)
    middle-long-square = extend-square (retainedIso δ) (comp-assoc F (retained hg) K) δ′
      (left-comparison k hg f) (right-comparison k hg f)
      ((K ◁ chg) ▷ F) (K ◁ (chg ▷ F))
      (associator-square k hg f) ((whisker-mixed-at chg F K) ⁻¹)

    second-short-square : (p₄ ∙ retainedIso β) =₂ (β′ ∙ p₁)
    second-short-square =
      let alternative = ((K ∘ H) ◁ cgf) ∙ left-comparison k h gf
          comparison : p₁ =₂ alternative
          comparison = isoComp-assoc-at ((K ∘ H) ◁ cgf) (ckh ▷ retained gf) (retained-compose kh gf) ∙
            (isoComp-cong (interchange-at ckh cgf) (idIso (retained-compose kh gf)) ∙
              (isoComp-assoc-at (ckh ▷ (G ∘ F)) (retained kh ◁ cgf) (retained-compose kh gf)) ⁻¹)
          square = extend-square (retainedIso β) (comp-assoc (retained gf) H K) β′
            (left-comparison k h gf) (right-comparison k h gf)
            ((K ∘ H) ◁ cgf) (K ◁ (H ◁ cgf))
            (associator-square k h gf) ((postWhisker-comp-at cgf H K) ⁻¹)
      in isoComp-cong (idIso β′) (comparison ⁻¹) ∙ square

    first-long-square : (p₂ ∙ retainedIso γ) =₂ (γ′ ∙ p₀)
    first-long-square =
      let a = left-comparison k h g
          b = right-comparison k h g
          cs = retained-compose (composeTerm kh g) f
          ct = retained-compose (composeTerm k hg) f
          source-normal : ((a ▷ F) ∙ cs) =₂ p₀
          source-normal = isoComp-assoc-at ((ckh ▷ G) ▷ F) (retained-compose kh g ▷ F) cs ∙
            isoComp-cong (preWhisker-isoComp-at (ckh ▷ G) (retained-compose kh g) F) (idIso cs)
          target-normal : ((b ▷ F) ∙ ct) =₂ p₂
          target-normal = isoComp-assoc-at ((K ◁ chg) ▷ F) (retained-compose k hg ▷ F) ct ∙
            isoComp-cong (preWhisker-isoComp-at (K ◁ chg) (retained-compose k hg) F) (idIso ct)
      in isoComp-cong (idIso γ′) source-normal ∙
        (prewhiskered-edge f (compose-assoc pAn k h g) a b (comp-assoc G H K)
          (associator-square k h g) ∙
          isoComp-cong (target-normal ⁻¹) (idIso (retainedIso γ)))

    last-long-square : (p₄ ∙ retainedIso ε) =₂ (ε′ ∙ p₃)
    last-long-square =
      let a = left-comparison h g f
          b = right-comparison h g f
          cs = retained-compose k (composeTerm hg f)
          ct = retained-compose k (composeTerm h gf)
          source-normal : ((K ◁ a) ∙ cs) =₂ p₃
          source-normal = isoComp-assoc-at (K ◁ (chg ▷ F)) (K ◁ retained-compose hg f) cs ∙
            isoComp-cong (postWhisker-isoComp-at K (chg ▷ F) (retained-compose hg f)) (idIso cs)
          target-normal : ((K ◁ b) ∙ ct) =₂ p₄
          target-normal = isoComp-assoc-at (K ◁ (H ◁ cgf)) (K ◁ retained-compose h gf) ct ∙
            isoComp-cong (postWhisker-isoComp-at K (H ◁ cgf) (retained-compose h gf)) (idIso ct)
      in isoComp-cong (idIso ε′) source-normal ∙
        (postwhiskered-edge k (compose-assoc pAn h g f) a b (comp-assoc F G H)
          (associator-square h g f) ∙
          isoComp-cong (target-normal ⁻¹) (idIso (retainedIso ε)))

  abstract
    pentagon : (β ∙ α) =₂ ((ε ∙ δ) ∙ γ)
    pentagon =
      let a = square-to-changeEndpoints p₀ p₁ (retainedIso α) α′ first-short-square
          b = square-to-changeEndpoints p₁ p₄ (retainedIso β) β′ second-short-square
          c = square-to-changeEndpoints p₀ p₂ (retainedIso γ) γ′ first-long-square
          d = square-to-changeEndpoints p₂ p₃ (retainedIso δ) δ′ middle-long-square
          e = square-to-changeEndpoints p₃ p₄ (retainedIso ε) ε′ last-long-square
          short-image = isoComp-cong b a ∙
            (changeEndpoints-comp p₀ p₁ p₄ (retainedIso β) (retainedIso α)) ⁻¹
          long-image = isoComp-cong (isoComp-cong e d) c ∙
            (changeEndpoints-comp₃ p₀ p₂ p₃ p₄ (retainedIso ε) (retainedIso δ) (retainedIso γ)) ⁻¹
          primitive-law = (isoComp-assoc-at ε′ δ′ γ′) ⁻¹ ∙ pentagon-whiskered F G H K
          retained-pentagon = changeEndpoints-reflect p₀ p₄
            (retainedIso β ∙ retainedIso α) ((retainedIso ε ∙ retainedIso δ) ∙ retainedIso γ)
            (long-image ⁻¹ ∙ (primitive-law ∙ short-image))
          long-expand = isoComp-cong (retainedIso-comp ε δ) (idIso (retainedIso γ)) ∙
            retainedIso-comp (ε ∙ δ) γ
      in retainedIso-reflect pAn (β ∙ α) ((ε ∙ δ) ∙ γ)
        (long-expand ⁻¹ ∙ (retained-pentagon ∙ retainedIso-comp β α))

compose-pentagon : {P A B C D E : CAT} (pAn : isAn P)
  (k : MAP P (Map D E)) (h : MAP P (Map C D))
  (g : MAP P (Map B C)) (f : MAP P (Map A B))
  →
      (compose-assoc pAn k h (composeTerm g f) ∙ compose-assoc pAn (composeTerm k h) g f) =₂
      ((composeTerm-cong (idIso k) (compose-assoc pAn h g f) ∙
        compose-assoc pAn k (composeTerm h g) f) ∙
        composeTerm-cong (compose-assoc pAn k h g) (idIso f))
compose-pentagon pAn k h g f = PentagonCalculation.pentagon pAn k h g f
```
