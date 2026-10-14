# Coherence of mapping-term composition

At an anima term source, relative evaluation recovers the unit and
associativity laws. The triangle compares their complete underlying images
through three fixed vertex identifications, then reflects primitive
coherence. The constant comparisons at `One` are normalized explicitly.
This does not yet identify the recovered laws with the default universal
choices, or assert their coherence at an arbitrary term source.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼; pair-pre; project-pair₁)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (triangle-with-identity; hcomp-id-inner-One; hcomp-id-outer-One;
    preWhisker-comp-One; postWhisker-comp-One; whisker-mixed-One; pentagon-whiskered)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module Coordinates; module UnitNormalization; module PairInput; at-pair-restrict)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-frame-square; post-changed-restriction)
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase using (module OverFirstFactor; product-over; change-parameter; second-projection; reflect-second)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Composition
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase
open import SCT.VolumeI.Chapter01.Section04.EvaluationCoherence
open import SCT.VolumeI.Chapter01.Section04.UncurryingRestriction
open import SCT.VolumeI.Chapter01.Section04.EvaluationRestriction public
  using (evaluation-restrict; evaluation-restrict-over; evaluation-restrict-natural;
    evaluation⁼-reflect-change; evaluation-recover-after-change)
open import SCT.VolumeI.Chapter01.Section04.CompositionLaws

module _ {Γ : Context} {X : CAT Γ} where
  open Terms.Equalities X using (_＝_)
  module _ {P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    evaluation⁼-cong : {x y : Term (Map C D)} {α β : x ＝ y}
      → α =₁ β → evaluation⁼ α =₁ evaluation⁼ β
    evaluation⁼-cong p = pair⁼-cong (id₌ _) (uncurry⁼-functor _ _ ◁ p)

    evaluation⁼-identity : (x : Term (Map C D))
      → evaluation⁼ (const {P = X} (id₌ x)) =₁ const (id₌ (FunctorOverBase.functor (evaluation-over x)))
    evaluation⁼-identity x =
      const-cong (pair⁼-id-One pr₁ (uncurry x)) ∙
        (pair⁼-constant (id₌ pr₁) (id₌ (uncurry x)) ∙
          pair⁼-cong (id₌ _) (uncurry⁼-identity x))

    evaluation⁼-composition : {x y z : Term (Map C D)} (β : y ＝ z) (α : x ＝ y)
      → evaluation⁼ (β ∙ α) =₁ (evaluation⁼ β ∙ evaluation⁼ α)
    evaluation⁼-composition β α = OverFirstFactor.pair-pr₁-cong-comp P (uncurry⁼ β) (uncurry⁼ α) ∙
      pair⁼-cong (id₌ _) (uncurry⁼-composition β α)

module _ {Γ : Context} {P : CAT Γ} where
  open Terms.InContext P using (Term)
  private
    evaluated : {C D : CAT Γ} → Term (Map C D) → MAP (P × C) (P × D)
    evaluated x = FunctorOverBase.functor (evaluation-over x)

    evaluated-compose : {A B C : CAT Γ} (y : Term (Map B C)) (x : Term (Map A B))
      → evaluated (compose y x) =₁ (evaluated y ∘ evaluated x)
    evaluated-compose y x = IdentificationOver.identification (evaluation-compose y x)

    evaluated-identity : (C : CAT Γ) → evaluated (identity-map C) =₁ id (P × C)
    evaluated-identity C = IdentificationOver.identification (evaluation-identity P C)

    evaluation⁼-identity-One : {C D : CAT Γ} (x : Term (Map C D))
      → evaluation⁼ (id₌ x) =₂ id₌ (evaluated x)
    evaluation⁼-identity-One x = const-One (id₌ (evaluated x)) ∙
      (evaluation⁼-identity x ∙ evaluation⁼-cong ((const-One (id₌ x)) ⁻¹))

    evaluated-compose-natural : {A B C : CAT Γ}
      {y y′ : Term (Map B C)} {x x′ : Term (Map A B)} (α : y =₁ y′) (β : x =₁ x′)
      → SquareCell₌ (evaluation⁼ (compose⁼ α β)) (evaluation⁼ α ⋆ evaluation⁼ β)
          (evaluated-compose y x) (evaluated-compose y′ x′)
    evaluated-compose-natural {y = y} {y′ = y′} {x = x} {x′ = x′} α β =
      replace-sides₌ (const-One (evaluated-compose y x)) (const-One (evaluated-compose y′ x′))
        (evaluation-compose-natural α β)

  private
    module TriangleCalculation {A B C : CAT Γ} (pAn : isAn P)
      (y : Term (Map B C)) (x : Term (Map A B)) where

      G : MAP (P × B) (P × C)
      G = evaluated y
      F : MAP (P × A) (P × B)
      F = evaluated x
      I : MAP P (Map B B)
      I = identity-map {P = P} B
      J : MAP (P × B) (P × B)
      J = evaluated I
      ε : J =₁ id (P × B)
      ε = evaluated-identity B

      left : (compose (compose y I) x) =₁ (compose y x)
      left = compose⁼ (Recovered.unitʳ pAn y) (id₌ x)

      middle : (compose (compose y I) x) =₁ (compose y (compose I x))
      middle = Recovered.assoc pAn y I x

      right : (compose y (compose I x)) =₁ (compose y x)
      right = compose⁼ (id₌ y) (Recovered.unitˡ pAn x)

      source-normalization : evaluated (compose (compose y I) x) =₁ ((G ∘ J) ∘ F)
      source-normalization = (evaluated-compose y I ▷ F) ∙ evaluated-compose (compose y I) x
      middle-normalization : evaluated (compose y (compose I x)) =₁ (G ∘ (J ∘ F))
      middle-normalization = (G ◁ evaluated-compose I x) ∙ evaluated-compose y (compose I x)
      target-normalization : evaluated (compose y x) =₁ (G ∘ F)
      target-normalization = evaluated-compose y x

      external-left : ((G ∘ J) ∘ F) =₁ (G ∘ F)
      external-left = (comp-unitʳ G ▷ F) ∙ ((G ◁ ε) ▷ F)
      external-middle : ((G ∘ J) ∘ F) =₁ (G ∘ (J ∘ F))
      external-middle = comp-assoc F J G
      external-right : (G ∘ (J ∘ F)) =₁ (G ∘ F)
      external-right = G ◁ (comp-unitˡ F ∙ (ε ▷ F))

      LeftNaturality : Set m
      LeftNaturality = (target-normalization ∙ evaluation⁼ left) =₂
        ((evaluation⁼ (Recovered.unitʳ pAn y) ⋆ evaluation⁼ (id₌ x)) ∙
          evaluated-compose (compose y I) x)

      RightNaturality : Set m
      RightNaturality = (target-normalization ∙ evaluation⁼ right) =₂
        ((evaluation⁼ (id₌ y) ⋆ evaluation⁼ (Recovered.unitˡ pAn x)) ∙
          evaluated-compose y (compose I x))

      left-edge-transport : LeftNaturality
        → (changeEndpoints source-normalization target-normalization (evaluation⁼ left)) =₂ external-left
      left-edge-transport natural =
        let c = evaluated-compose y I
            d = evaluated-compose (compose y I) x
            β = G ◁ ε
            outer = comp-unitʳ G
            normalized = preWhisker-comp₌ outer (β ∙ c) F ∙
              (preWhisker F ◁ Recovered.unitʳ-image pAn y)
            expanded = comp₌-cong (id₌ (outer ▷ F)) (preWhisker-comp₌ β c F) ∙ normalized
            rebracket = comp₌-assoc external-left (c ▷ F) d ∙
              comp₌-cong ((comp₌-assoc (outer ▷ F) (β ▷ F) (c ▷ F)) ⁻¹) (id₌ d)
            square = rebracket ∙
              (comp₌-cong expanded (id₌ d) ∙
              (comp₌-cong
                (hcomp-id-inner-One (evaluation⁼ (Recovered.unitʳ pAn y)) F ∙
                  hcomp-cong (id₌ (evaluation⁼ (Recovered.unitʳ pAn y))) (evaluation⁼-identity-One x))
                (id₌ d) ∙ natural))
        in square-to-changeEndpoints source-normalization target-normalization (evaluation⁼ left) external-left square

      middle-edge-transport :
        (changeEndpoints source-normalization middle-normalization (evaluation⁼ middle)) =₂ external-middle
      middle-edge-transport = inverse-route-transport source-normalization
        (G ◁ evaluated-compose I x) (evaluated-compose y (compose I x))
        (evaluation⁼ middle) external-middle (Recovered.assoc-image pAn y I x)

      right-edge-transport : RightNaturality
        → (changeEndpoints middle-normalization target-normalization (evaluation⁼ right)) =₂ external-right
      right-edge-transport natural =
        let c = evaluated-compose I x
            d = evaluated-compose y (compose I x)
            β = ε ▷ F
            outer = comp-unitˡ F
            normalized = postWhisker-comp₌ G outer (β ∙ c) ∙
              (postWhisker G ◁ Recovered.unitˡ-image pAn x)
            expanded = comp₌-cong (id₌ (G ◁ outer)) (postWhisker-comp₌ G β c) ∙ normalized
            rebracket = comp₌-assoc external-right (G ◁ c) d ∙
              (comp₌-cong
                (comp₌-cong ((postWhisker-comp₌ G outer β) ⁻¹) (id₌ (G ◁ c)) ∙
                  (comp₌-assoc (G ◁ outer) (G ◁ β) (G ◁ c)) ⁻¹) (id₌ d))
            square = rebracket ∙
              (comp₌-cong expanded (id₌ d) ∙
              (comp₌-cong
                (hcomp-id-outer-One G (evaluation⁼ (Recovered.unitˡ pAn x)) ∙
                  hcomp-cong (evaluation⁼-identity-One y) (id₌ (evaluation⁼ (Recovered.unitˡ pAn x))))
                (id₌ d) ∙ natural))
        in square-to-changeEndpoints middle-normalization target-normalization (evaluation⁼ right) external-right square

      triangle : LeftNaturality → RightNaturality → left =₂ (right ∙ middle)
      triangle natural-left natural-right = evaluation⁼-reflect pAn left (right ∙ middle)
        ((evaluation⁼-composition right middle) ⁻¹ ∙
          changeEndpoints-reflect source-normalization target-normalization
            {α = evaluation⁼ left} {β = evaluation⁼ right ∙ evaluation⁼ middle}
            (changeEndpoints-comp source-normalization middle-normalization target-normalization
              (evaluation⁼ right) (evaluation⁼ middle) ∙
            ((comp₌-cong (right-edge-transport natural-right) middle-edge-transport) ⁻¹ ∙
            (triangle-with-identity G F J ε ∙ left-edge-transport natural-left))))

  recoveredCompositionTriangle : {A B C : CAT Γ} (pAn : isAn P)
    (x : Term (Map A B)) (y : Term (Map B C))
    → TriangleDiagram {X = One {Γ}}
        (compose (compose y (identity-map B)) x)
        (compose y (compose (identity-map B) x)) (compose y x)
  recoveredCompositionTriangle pAn x y = triangle-diagram
    (compose⁼ (Recovered.unitʳ pAn y) (id₌ x))
    (Recovered.assoc pAn y (identity-map _) x)
    (compose⁼ (id₌ y) (Recovered.unitˡ pAn x))

  recovered-triangle : {A B C : CAT Γ} (pAn : isAn P)
    (x : Term (Map A B)) (y : Term (Map B C))
    → TriangleCommutes (recoveredCompositionTriangle pAn x y)
  recovered-triangle pAn x y = TriangleCalculation.triangle pAn y x
    (evaluated-compose-natural (Recovered.unitʳ pAn y) (id₌ x))
    (evaluated-compose-natural (id₌ y) (Recovered.unitˡ pAn x))
```

For the pentagon, fix the evaluation frame at each of the five binary
composites. Each recovered edge has a square to the corresponding functor
edge in those frames. The two action edges retain their identity inputs;
their images are normalized explicitly. Interchange compares the two
frames at the intermediate vertex on the short route. Transporting all
five squares gives the primitive pentagon, with its left-associated long
route, and relative evaluation reflects the resulting equation.

```agda
  private
    module RecoveredPentagonCalculation {A B C D E : CAT Γ} (pAn : isAn P)
      (w : Term (Map D E)) (z : Term (Map C D))
      (y : Term (Map B C)) (x : Term (Map A B)) where

      left-evaluation : {U V W Z : CAT Γ}
        (z′ : Term (Map W Z)) (y′ : Term (Map V W)) (x′ : Term (Map U V))
        → evaluated (compose (compose z′ y′) x′) =₁ ((evaluated z′ ∘ evaluated y′) ∘ evaluated x′)
      left-evaluation z′ y′ x′ =
        (evaluated-compose z′ y′ ▷ evaluated x′) ∙ evaluated-compose (compose z′ y′) x′

      right-evaluation : {U V W Z : CAT Γ}
        (z′ : Term (Map W Z)) (y′ : Term (Map V W)) (x′ : Term (Map U V))
        → evaluated (compose z′ (compose y′ x′)) =₁ (evaluated z′ ∘ (evaluated y′ ∘ evaluated x′))
      right-evaluation z′ y′ x′ =
        (evaluated z′ ◁ evaluated-compose y′ x′) ∙ evaluated-compose z′ (compose y′ x′)

      associator-square : {U V W Z : CAT Γ}
        (z′ : Term (Map W Z)) (y′ : Term (Map V W)) (x′ : Term (Map U V))
        → SquareCell₌ (evaluation⁼ (Recovered.assoc pAn z′ y′ x′))
            (comp-assoc (evaluated x′) (evaluated y′) (evaluated z′))
            (left-evaluation z′ y′ x′) (right-evaluation z′ y′ x′)
      associator-square z′ y′ x′ = inverse-route-square (left-evaluation z′ y′ x′)
        (evaluated z′ ◁ evaluated-compose y′ x′) (evaluated-compose z′ (compose y′ x′))
        (evaluation⁼ (Recovered.assoc pAn z′ y′ x′))
        (comp-assoc (evaluated x′) (evaluated y′) (evaluated z′))
        (Recovered.assoc-image pAn z′ y′ x′)

      K : MAP (P × D) (P × E)
      K = evaluated w
      H : MAP (P × C) (P × D)
      H = evaluated z
      G : MAP (P × B) (P × C)
      G = evaluated y
      F : MAP (P × A) (P × B)
      F = evaluated x
      wz : Term (Map C E)
      wz = compose w z
      zy : Term (Map B D)
      zy = compose z y
      yx : Term (Map A C)
      yx = compose y x
      cwz : evaluated wz =₁ (K ∘ H)
      cwz = evaluated-compose w z
      czy : evaluated zy =₁ (H ∘ G)
      czy = evaluated-compose z y
      cyx : evaluated yx =₁ (G ∘ F)
      cyx = evaluated-compose y x

      α : compose (compose wz y) x =₁ compose wz yx
      α = Recovered.assoc pAn wz y x
      β : compose wz yx =₁ compose w (compose z yx)
      β = Recovered.assoc pAn w z yx
      γ : compose (compose wz y) x =₁ compose (compose w zy) x
      γ = compose⁼ (Recovered.assoc pAn w z y) (id₌ x)
      δ : compose (compose w zy) x =₁ compose w (compose zy x)
      δ = Recovered.assoc pAn w zy x
      ε : compose w (compose zy x) =₁ compose w (compose z yx)
      ε = compose⁼ (id₌ w) (Recovered.assoc pAn z y x)

      p₀ : (evaluated (compose (compose wz y) x)) =₁ (((K ∘ H) ∘ G) ∘ F)
      p₀ = ((cwz ▷ G) ▷ F) ∙ left-evaluation wz y x

      p₁ : (evaluated (compose wz yx)) =₁ ((K ∘ H) ∘ (G ∘ F))
      p₁ = (cwz ▷ (G ∘ F)) ∙ right-evaluation wz y x

      p₂ : (evaluated (compose (compose w zy) x)) =₁ ((K ∘ (H ∘ G)) ∘ F)
      p₂ = ((K ◁ czy) ▷ F) ∙ left-evaluation w zy x

      p₃ : (evaluated (compose w (compose zy x))) =₁ (K ∘ ((H ∘ G) ∘ F))
      p₃ = (K ◁ (czy ▷ F)) ∙ right-evaluation w zy x

      p₄ : (evaluated (compose w (compose z yx))) =₁ (K ∘ (H ∘ (G ∘ F)))
      p₄ = (K ◁ (H ◁ cyx)) ∙ right-evaluation w z yx

      α′ : (((K ∘ H) ∘ G) ∘ F) =₁ ((K ∘ H) ∘ (G ∘ F))
      α′ = comp-assoc F G (K ∘ H)
      β′ : ((K ∘ H) ∘ (G ∘ F)) =₁ (K ∘ (H ∘ (G ∘ F)))
      β′ = comp-assoc (G ∘ F) H K
      γ′ : (((K ∘ H) ∘ G) ∘ F) =₁ ((K ∘ (H ∘ G)) ∘ F)
      γ′ = comp-assoc G H K ▷ F
      δ′ : ((K ∘ (H ∘ G)) ∘ F) =₁ (K ∘ ((H ∘ G) ∘ F))
      δ′ = comp-assoc F (H ∘ G) K
      ε′ : (K ∘ ((H ∘ G) ∘ F)) =₁ (K ∘ (H ∘ (G ∘ F)))
      ε′ = K ◁ comp-assoc F G H

      opaque
        first-short-square : (p₁ ∙ evaluation⁼ α) =₂ (α′ ∙ p₀)
        first-short-square = paste-square₌
          {t = evaluation⁼ α} {m = comp-assoc F G (evaluated wz)} {b = α′}
          {l₁ = left-evaluation wz y x} {r₁ = right-evaluation wz y x}
          {l₂ = (cwz ▷ G) ▷ F} {r₂ = cwz ▷ (G ∘ F)}
          (associator-square wz y x) ((preWhisker-comp-One cwz G F) ⁻¹)

        middle-long-square : (p₃ ∙ evaluation⁼ δ) =₂ (δ′ ∙ p₂)
        middle-long-square = paste-square₌
          {t = evaluation⁼ δ} {m = comp-assoc F (evaluated zy) K} {b = δ′}
          {l₁ = left-evaluation w zy x} {r₁ = right-evaluation w zy x}
          {l₂ = (K ◁ czy) ▷ F} {r₂ = K ◁ (czy ▷ F)}
          (associator-square w zy x) ((whisker-mixed-One czy F K) ⁻¹)

        second-short-square : (p₄ ∙ evaluation⁼ β) =₂ (β′ ∙ p₁)
        second-short-square =
          let alternative = ((K ∘ H) ◁ cyx) ∙ left-evaluation w z yx
              comparison : p₁ =₂ alternative
              comparison = comp₌-assoc ((K ∘ H) ◁ cyx) (cwz ▷ evaluated yx) (evaluated-compose wz yx) ∙
                (comp₌-cong (interchange cwz cyx) (id₌ (evaluated-compose wz yx)) ∙
                  (comp₌-assoc (cwz ▷ (G ∘ F)) (evaluated wz ◁ cyx) (evaluated-compose wz yx)) ⁻¹)
              square = paste-square₌
                {t = evaluation⁼ β} {m = comp-assoc (evaluated yx) H K} {b = β′}
                {l₁ = left-evaluation w z yx} {r₁ = right-evaluation w z yx}
                {l₂ = (K ∘ H) ◁ cyx} {r₂ = K ◁ (H ◁ cyx)}
                (associator-square w z yx) ((postWhisker-comp-One cyx H K) ⁻¹)
          in comp₌-cong (id₌ β′) (comparison ⁻¹) ∙ square

        first-long-square : (p₂ ∙ evaluation⁼ γ) =₂ (γ′ ∙ p₀)
        first-long-square =
          let a = left-evaluation w z y
              b = right-evaluation w z y
              cs = evaluated-compose (compose wz y) x
              ct = evaluated-compose (compose w zy) x
              source-normal : ((a ▷ F) ∙ cs) =₂ p₀
              source-normal = prewhiskered-composite F (cwz ▷ G) (evaluated-compose wz y) cs
              target-normal : ((b ▷ F) ∙ ct) =₂ p₂
              target-normal = prewhiskered-composite F (K ◁ czy) (evaluated-compose w zy) ct
              image = evaluation⁼ (Recovered.assoc pAn w z y)
              normalize : (image ⋆ evaluation⁼ (id₌ x)) =₂ (image ▷ F)
              normalize = hcomp-id-inner-One image F ∙
                hcomp-cong (id₌ image) (evaluation⁼-identity-One x)
              natural = replace-edges₌ (id₌ (evaluation⁼ γ)) normalize
                (evaluated-compose-natural (Recovered.assoc pAn w z y) (id₌ x))
              square = paste-square₌ natural
                (pre-square₌ F (associator-square w z y))
          in replace-sides₌ source-normal target-normal square

        last-long-square : (p₄ ∙ evaluation⁼ ε) =₂ (ε′ ∙ p₃)
        last-long-square =
          let a = left-evaluation z y x
              b = right-evaluation z y x
              cs = evaluated-compose w (compose zy x)
              ct = evaluated-compose w (compose z yx)
              source-normal : ((K ◁ a) ∙ cs) =₂ p₃
              source-normal = postwhiskered-composite K (czy ▷ F) (evaluated-compose zy x) cs
              target-normal : ((K ◁ b) ∙ ct) =₂ p₄
              target-normal = postwhiskered-composite K (H ◁ cyx) (evaluated-compose z yx) ct
              image = evaluation⁼ (Recovered.assoc pAn z y x)
              normalize : (evaluation⁼ (id₌ w) ⋆ image) =₂ (K ◁ image)
              normalize = hcomp-id-outer-One K image ∙
                hcomp-cong (evaluation⁼-identity-One w) (id₌ image)
              natural = replace-edges₌ (id₌ (evaluation⁼ ε)) normalize
                (evaluated-compose-natural (id₌ w) (Recovered.assoc pAn z y x))
              square = paste-square₌ natural
                (post-square₌ K (associator-square z y x))
          in replace-sides₌ source-normal target-normal square


      opaque
        pentagon : (β ∙ α) =₂ ((ε ∙ δ) ∙ γ)
        pentagon =
          let a = square-to-changeEndpoints p₀ p₁ (evaluation⁼ α) α′ first-short-square
              b = square-to-changeEndpoints p₁ p₄ (evaluation⁼ β) β′ second-short-square
              c = square-to-changeEndpoints p₀ p₂ (evaluation⁼ γ) γ′ first-long-square
              d = square-to-changeEndpoints p₂ p₃ (evaluation⁼ δ) δ′ middle-long-square
              e = square-to-changeEndpoints p₃ p₄ (evaluation⁼ ε) ε′ last-long-square
              short-image = comp₌-cong b a ∙
                (changeEndpoints-comp p₀ p₁ p₄ (evaluation⁼ β) (evaluation⁼ α)) ⁻¹
              long-image = comp₌-cong (comp₌-cong e d) c ∙
                (changeEndpoints-comp₃ p₀ p₂ p₃ p₄ (evaluation⁼ ε) (evaluation⁼ δ) (evaluation⁼ γ)) ⁻¹
              primitive-law = pentagon-whiskered F G H K
              image-pentagon = changeEndpoints-reflect p₀ p₄
                {α = evaluation⁼ β ∙ evaluation⁼ α}
                {β = (evaluation⁼ ε ∙ evaluation⁼ δ) ∙ evaluation⁼ γ}
                (long-image ⁻¹ ∙ (primitive-law ∙ short-image))
              long-expand = comp₌-cong (evaluation⁼-composition ε δ) (id₌ (evaluation⁼ γ)) ∙
                evaluation⁼-composition (ε ∙ δ) γ
          in evaluation⁼-reflect pAn (β ∙ α) ((ε ∙ δ) ∙ γ)
            (long-expand ⁻¹ ∙ (image-pentagon ∙ evaluation⁼-composition β α))

  recoveredCompositionPentagon : {A B C D E : CAT Γ} (pAn : isAn P)
    (x : Term (Map A B)) (y : Term (Map B C)) (z : Term (Map C D)) (w : Term (Map D E))
    → PentagonDiagram {X = One {Γ}}
        (compose (compose (compose w z) y) x)
        (compose (compose w z) (compose y x))
        (compose w (compose z (compose y x)))
        (compose (compose w (compose z y)) x)
        (compose w (compose (compose z y) x))
  recoveredCompositionPentagon pAn x y z w = pentagon-diagram
    (Recovered.assoc pAn (compose w z) y x)
    (Recovered.assoc pAn w z (compose y x))
    (compose⁼ (Recovered.assoc pAn w z y) (id₌ x))
    (Recovered.assoc pAn w (compose z y) x)
    (compose⁼ (id₌ w) (Recovered.assoc pAn z y x))

  recovered-pentagon : {A B C D E : CAT Γ} (pAn : isAn P)
    (x : Term (Map A B)) (y : Term (Map B C)) (z : Term (Map C D)) (w : Term (Map D E))
    → PentagonCommutes (recoveredCompositionPentagon pAn x y z w)
  recovered-pentagon pAn x y z w = RecoveredPentagonCalculation.pentagon pAn w z y x
```

The left-unit restriction calculation fixes the outer term to the
representing identity and the inner term to the identity of the mapping
anima. The local application normalization below is used for their selected
composite, with the actual product change and projection comparisons.

```agda
private
  module LeftUnitRestriction {Γ : Context} {Q C D : CAT Γ}
    (x : MAP Q (Map C D)) where
    M = Map C D
    open Terms.InContext M using (Term)

    outer : Term (Map D D)
    outer = identity-map D

    inner : Term (Map C D)
    inner = id M

    composite : Term (Map C D)
    composite = compose outer inner

    as-application-restriction : {A B : CAT Γ} (t : Term (Map A B))
      → uncurry-as-apply (t ∘ x) =₂
          (apply-map⁼ (Coordinates.first A t x) (second-projection x) ∙
            (apply-map-pre (t ∘ pr₁) pr₂ (productMap x (id A)) ∙
              ((uncurry-as-apply t ▷ productMap x (id A)) ∙ uncurry-restrict t x)))
    as-application-restriction {A = A} t =
      let module U = UnitNormalization {C = A} t x
          corner = comp-assoc (pr₁ {C = Q} {D = A}) x t
          first = apply-map⁼ corner (id₌ pr₂)
          second = apply-map⁼ (Coordinates.first A t x) U.second
          tail = apply-map-pre (t ∘ pr₁) pr₂ U.s ∙
            ((uncurry-as-apply t ▷ U.s) ∙ uncurry-restrict t x)
          frame = post-frame-square mapEval U.s U.before U.after U.finish
            (pair⁼ U.first U.second) (pair-pre (t ∘ pr₁) pr₂ U.s) U.change U.unit-square
          join = Binary.binary-cong₂ mapEval (comp-inv-left corner U.first) (comp₌-unitˡ-One U.second) ∙
            (Binary.binary-cong-comp mapEval corner (Coordinates.first A t x) (id₌ pr₂) U.second) ⁻¹
          normalize = comp₌-cong join (id₌ tail) ∙ (comp₌-assoc first second tail) ⁻¹
      in cancel-left first (normalize ⁻¹ ∙ frame)

    at-restriction : {R T Z A B : CAT Γ}
      (f : MAP Z (Map A B)) (p : MAP T Z) (z : MAP T A) (r : MAP R T)
      → (apply-map⁼ (comp-assoc r p f) (id₌ (z ∘ r)) ∙
          (apply-map-pre (f ∘ p) z r ∙ (uncurry-at f p z ▷ r))) =₂
          (uncurry-at f (p ∘ r) (z ∘ r) ∙
            ((uncurry f ◁ pair-pre p z r) ∙ comp-assoc r (pair p z) (uncurry f)))
    at-restriction {A = A} f p z r =
      (post-changed-restriction mapEval (productMap f (id A))
        (pair p z) r (pair (p ∘ r) (z ∘ r)) (pair-pre p z r)
        (PairInput.at-pair f p z) (pair-pre (f ∘ p) z r)
        (PairInput.at-pair f (p ∘ r) (z ∘ r))
        (pair⁼ (comp-assoc r p f) (id₌ (z ∘ r)))
        (at-pair-restrict f p z r)) ⁻¹

    module CompositionBeta where
      s = productMap x (id C)
      module Inputs = TripleRestriction
        (outer ∘ pr₁ {C = M} {D = C}) (inner ∘ pr₁) pr₂ s
      U = uncurry (mapComp {C = C} {D = D} {E = D})
      V = doubleEvaluation {C = C} {D = D} {E = D}
      b = mapComp-β {C = C} {D = D} {E = D}

      source-change = (U ◁ Inputs.triple-change) ∙ comp-assoc s Inputs.triple U
      target-change = (V ◁ Inputs.triple-change) ∙ comp-assoc s Inputs.triple V

      square : SquareCell₌ ((b ▷ Inputs.triple) ▷ s) (b ▷ Inputs.triple′)
        source-change target-change
      square = replace-sides₌
        (comp₌-cong (id₌ (U ◁ Inputs.triple-change)) (const-One (comp-assoc s Inputs.triple U)))
        (comp₌-cong (id₌ (V ◁ Inputs.triple-change)) (const-One (comp-assoc s Inputs.triple V)))
        (identification-restriction b Inputs.triple s Inputs.triple′ Inputs.triple-change)
```
