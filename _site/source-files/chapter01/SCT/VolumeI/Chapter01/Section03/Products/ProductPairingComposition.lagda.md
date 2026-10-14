# Composition of product functors at a pair

Applying two product functors successively to a pair agrees with applying
their selected composite. Both coordinate associators are retained. This
is the common calculation needed when parameter change meets shape change.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductPairingComposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; preWhisker-comp₌; comp-inv-left)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-comp; pair⁼-cong)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; post-square-cell; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)

private
  module Coordinate {Γ : Context} {T V W X Y Z : CAT Γ}
    (π : MAP V X) (ψ : MAP W Y) (f : MAP X Y) (F : MAP Y Z)
    (u : MAP V W) (t : MAP T V) (s : MAP T W) (δ : (u ∘ t) =₁ s)
    (p : MAP T X) (b : (π ∘ t) =₁ p)
    (β : (ψ ∘ u) =₁ (f ∘ π)) (β′ : (ψ ∘ s) =₁ (f ∘ p)) where
    first = post-square-cell F π f ψ u β
    second = post-triangle (F ∘ f) π t b
    direct = post-triangle F ψ s β′
    incoming = post-triangle f π t b
    law : SquareCell₌ (ψ ◁ δ) incoming (restrict-triangle ψ u β t) β′ →
      (direct ∙ (((F ∘ ψ) ◁ δ) ∙ comp-assoc t u (F ∘ ψ))) =₂
      (comp-assoc p f F ∙ (second ∙ (first ▷ t)))
    law image = normalize ⁻¹ ∙
      post-triangle-change F ψ u t s δ β β′ incoming image
      where
      corner = comp-assoc π f F
      original = post-triangle F ψ u β
      mid = comp-assoc t (f ∘ π) F
      simplify = (preWhisker t ◁ comp-inv-left corner original) ∙
        (preWhisker-comp₌ corner first t) ⁻¹
      normalize = comp₌-cong (id₌ (F ◁ incoming)) (comp₌-cong (id₌ mid) simplify) ∙
        (comp₌-cong (id₌ (F ◁ incoming)) (comp₌-assoc mid (corner ▷ t) (first ▷ t)) ∙
        (comp₌-assoc (F ◁ incoming) (mid ∙ (corner ▷ t)) (first ▷ t) ∙
        (comp₌-cong (post-triangle-comp F f π t b) (id₌ (first ▷ t)) ∙
          (comp₌-assoc (comp-assoc p f F) second (first ▷ t)) ⁻¹)))

module AtPair {Γ : Context} {T A B C X Y Z : CAT Γ}
  (f : MAP A B) (F : MAP B C) (g : MAP X Y) (G : MAP Y Z)
  (p : MAP T A) (q : MAP T X) where
  private
    u = productMap f g
    t = pair p q
    s = pair (f ∘ p) (g ∘ q)
    δ = productMap-pair f g p q
    first-coordinate = post-triangle f pr₁ t (pair-β₁ p q)
    second-coordinate = post-triangle g pr₂ t (pair-β₂ p q)
    module First = Coordinate pr₁ pr₁ f F u t s δ p (pair-β₁ p q)
      (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) (pair-β₁ (f ∘ p) (g ∘ q))
    module Second = Coordinate pr₂ pr₂ g G u t s δ q (pair-β₂ p q)
      (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) (pair-β₂ (f ∘ p) (g ∘ q))
    ρ : RestrictionDiagram {E = One} {Q = T} (A × X) (B × Y)
    ρ = restriction-diagram u t s δ
    first-evaluation : Evaluation ρ (F ∘ pr₁) ((F ∘ f) ∘ pr₁)
      ((F ∘ f) ∘ p) (F ∘ (f ∘ p))
    first-evaluation = evaluation First.direct First.first First.second (comp-assoc p f F)
    second-evaluation : Evaluation ρ (G ∘ pr₂) ((G ∘ g) ∘ pr₂)
      ((G ∘ g) ∘ q) (G ∘ (g ∘ q))
    second-evaluation = evaluation Second.direct Second.first Second.second (comp-assoc q g G)
  composition :
    (productMap-pair F G (f ∘ p) (g ∘ q) ∙
      ((productMap F G ◁ productMap-pair f g p q) ∙
        comp-assoc (pair p q) (productMap f g) (productMap F G))) =₂
    (pair⁼ (comp-assoc p f F) (comp-assoc q g G) ∙
      (productMap-pair (F ∘ f) (G ∘ g) p q ∙ (productMap-comp f F g G ▷ pair p q)))
  composition = pair-compatible-One ρ first-evaluation second-evaluation
    (First.law (pair-evaluation-over₁-One (f ∘ pr₁) (g ∘ pr₂) t first-coordinate second-coordinate))
    (Second.law (pair-evaluation-over₂-One (f ∘ pr₁) (g ∘ pr₂) t first-coordinate second-coordinate))
```

## Composition with specified coordinate frames

The same calculation permits arbitrary identifications of the intermediate
and final coordinates. This is the form used by insertion comparisons: it
keeps their unitors and constant-input associators explicitly.

```agda
open import SCT.VolumeI.Chapter01.Section02.Specialization using (postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair-inner-One)

module FramedComposition {Γ : Context} {T A B C X Y Z : CAT Γ}
  (f : MAP A B) (F : MAP B C) (g : MAP X Y) (G : MAP Y Z)
  (p : MAP T A) (q : MAP T X) (p′ : MAP T B) (q′ : MAP T Y)
  (p″ : MAP T C) (q″ : MAP T Z)
  (α : (f ∘ p) =₁ p′) (β : (g ∘ q) =₁ q′)
  (γ : (F ∘ p′) =₁ p″) (δ : (G ∘ q′) =₁ q″) where
  private
    input-frame = pair⁼ α β
    output-frame = pair⁼ γ δ
    input-evaluation = productMap-pair f g p q
    output-evaluation = productMap-pair F G p′ q′
    intermediate-evaluation = productMap-pair F G (f ∘ p) (g ∘ q)
    outer = productMap F G
    associator = comp-assoc (pair p q) (productMap f g) outer
    changed-frame = pair⁼ (F ◁ α) (G ◁ β)
    tail = (outer ◁ input-evaluation) ∙ associator
    combined-frame = pair⁼ (γ ∙ (F ◁ α)) (δ ∙ (G ◁ β))
    coordinate-associators = pair⁼ (comp-assoc p f F) (comp-assoc q g G)
    composite-evaluation = productMap-pair (F ∘ f) (G ∘ g) p q
    restricted-compositor = productMap-comp f F g G ▷ pair p q

  first : (productMap f g ∘ pair p q) =₁ pair p′ q′
  first = input-frame ∙ input-evaluation
  second : (outer ∘ pair p′ q′) =₁ pair p″ q″
  second = output-frame ∙ output-evaluation
  coordinate₁ : ((F ∘ f) ∘ p) =₁ p″
  coordinate₁ = (γ ∙ (F ◁ α)) ∙ comp-assoc p f F
  coordinate₂ : ((G ∘ g) ∘ q) =₁ q″
  coordinate₂ = (δ ∙ (G ◁ β)) ∙ comp-assoc q g G

  composition : (second ∙ ((outer ◁ first) ∙ associator)) =₂
    (pair⁼ coordinate₁ coordinate₂ ∙ (composite-evaluation ∙ restricted-compositor))
  composition = finish ∙ (raw-composition ∙ (normalize-frame ∙ expand))
    where
    expand =
      comp₌-cong (id₌ output-frame)
        ((comp₌-assoc output-evaluation (outer ◁ input-frame) tail) ⁻¹) ∙
      (comp₌-assoc output-frame output-evaluation ((outer ◁ input-frame) ∙ tail) ∙
      (comp₌-cong (id₌ second)
        (comp₌-assoc (outer ◁ input-frame) (outer ◁ input-evaluation) associator) ∙
      comp₌-cong (id₌ second)
        (comp₌-cong (postWhisker-comp₌ outer input-frame input-evaluation) (id₌ associator))))
    normalize-frame =
      comp₌-cong ((pair⁼-comp γ (F ◁ α) δ (G ◁ β)) ⁻¹)
        (id₌ (intermediate-evaluation ∙ tail)) ∙
      ((comp₌-assoc output-frame changed-frame (intermediate-evaluation ∙ tail)) ⁻¹ ∙
      (comp₌-cong (id₌ output-frame)
        (comp₌-assoc changed-frame intermediate-evaluation tail) ∙
      comp₌-cong (id₌ output-frame)
        (comp₌-cong (productMap-pair-inner-One F G α β) (id₌ tail))))
    raw-composition = comp₌-cong (id₌ combined-frame) (AtPair.composition f F g G p q)
    finish = comp₌-cong
      ((pair⁼-comp (γ ∙ (F ◁ α)) (comp-assoc p f F)
        (δ ∙ (G ◁ β)) (comp-assoc q g G)) ⁻¹)
      (id₌ (composite-evaluation ∙ restricted-compositor)) ∙
      (comp₌-assoc combined-frame coordinate-associators
        (composite-evaluation ∙ restricted-compositor)) ⁻¹
```


The composite product functor may itself be normalized by specified
identifications in its two coordinates. It suffices to verify the two
coordinate equations; the full paired comparison, including the selected
product compositor, follows.

```agda
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair-outer-One)

module NormalizedComposition {Γ : Context} {T A B C X Y Z : CAT Γ}
  (f : MAP A B) (F : MAP B C) (g : MAP X Y) (G : MAP Y Z)
  (p : MAP T A) (q : MAP T X) (p′ : MAP T B) (q′ : MAP T Y)
  (p″ : MAP T C) (q″ : MAP T Z)
  (α : (f ∘ p) =₁ p′) (β : (g ∘ q) =₁ q′)
  (γ : (F ∘ p′) =₁ p″) (δ : (G ∘ q′) =₁ q″)
  (H : MAP A C) (K : MAP X Z) (σ : (F ∘ f) =₁ H) (τ : (G ∘ g) =₁ K)
  (ε : (H ∘ p) =₁ p″) (ζ : (K ∘ q) =₁ q″) where
  private
    module Framed = FramedComposition f F g G p q p′ q′ p″ q″ α β γ δ
    source-pair = pair p q
    raw = productMap-pair (F ∘ f) (G ∘ g) p q
    normalized = productMap-pair H K p q
    final-frame = pair⁼ ε ζ
    coordinate-change = pair⁼ (σ ▷ p) (τ ▷ q)
    functor-change = productMap-cong σ τ
    raw-compositor = productMap-comp f F g G
    restricted = raw-compositor ▷ source-pair
  compositor : (productMap F G ∘ productMap f g) =₁ productMap H K
  compositor = functor-change ∙ raw-compositor
  direct : (productMap H K ∘ source-pair) =₁ pair p″ q″
  direct = final-frame ∙ normalized

  composition :
    Framed.coordinate₁ =₂ (ε ∙ (σ ▷ p)) →
    Framed.coordinate₂ =₂ (ζ ∙ (τ ▷ q)) →
    (Framed.second ∙ ((productMap F G ◁ Framed.first) ∙
      comp-assoc source-pair (productMap f g) (productMap F G))) =₂
    (direct ∙ (compositor ▷ source-pair))
  composition first-coordinate second-coordinate = normalize ∙
    (comp₌-cong (pair⁼-cong first-coordinate second-coordinate)
      (id₌ (raw ∙ restricted)) ∙ Framed.composition)
    where
    normalize =
      comp₌-cong (id₌ direct) ((preWhisker-comp₌ functor-change raw-compositor source-pair) ⁻¹) ∙
      ((comp₌-assoc final-frame normalized ((functor-change ▷ source-pair) ∙ restricted)) ⁻¹ ∙
      (comp₌-cong (id₌ final-frame)
        (comp₌-assoc normalized (functor-change ▷ source-pair) restricted) ∙
      (comp₌-cong (id₌ final-frame)
        (comp₌-cong ((productMap-pair-outer-One σ τ p q) ⁻¹) (id₌ restricted)) ∙
      (comp₌-cong (id₌ final-frame) ((comp₌-assoc coordinate-change raw restricted) ⁻¹) ∙
      (comp₌-assoc final-frame coordinate-change (raw ∙ restricted) ∙
      comp₌-cong (pair⁼-comp ε (σ ▷ p) ζ (τ ▷ q)) (id₌ (raw ∙ restricted)))))))
```
