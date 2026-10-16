# Substitution in the first product factor

`productMap σ (id C)` changes the parameter of a product `P × C`. This module
computes the composition identification `productMap-first-comp f σ` of two such
functors through its coordinates, which are postcomposed square cells, and
proves its compatibility with pair inputs, restriction, a binary functor, a
further substitution (associativity) and units. The identity coordinate
keeps the specified unitor `comp-unitˡ (id C)`; it is normalized only where a
statement requires it.

Each comparison of two identifications into a product is the compatibility
of a paired evaluation along a restriction diagram: the coordinate
evaluations are compatible, so their pairing is (PairingSquares). The
diagrams are the restriction of a pair, the substitution applied to a pair,
and two successive substitutions. The unit normalization is the naturality
of a paired evaluation in its inputs, and the binary case postcomposes the
pairing (BinaryFunctors).

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Terms using (Equal)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; preWhisker-id₌;
    module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id; productMap-comp; module Associativity)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (left-unitor-comp; identity-unitors; postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; post-triangle-comp; module FrameChange)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (restriction-diagram; evaluation)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
```

## Composition coordinates

The coordinates of `productMap-first-comp f σ` are the postcomposed square
cells `first` and `second` of the two projections; the identity coordinate
carries the left unitor of `id C`.

```agda
module _ {Γ : Context} where
  module Coordinates {Y X Z : CAT Γ} (C : CAT Γ) (f : MAP X Z) (σ : MAP Y X) where
    substitution : MAP (Y × C) (X × C)
    substitution = productMap σ (id C)

    first : ((f ∘ pr₁) ∘ substitution) =₁ ((f ∘ σ) ∘ pr₁)
    first = post-square-cell f pr₁ σ pr₁ substitution (pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂))

    second-before-unit : ((id C ∘ pr₂) ∘ substitution) =₁ ((id C ∘ id C) ∘ pr₂)
    second-before-unit =
      post-square-cell (id C) pr₂ (id C) pr₂ substitution (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂))

    second : ((id C ∘ pr₂) ∘ substitution) =₁ (id C ∘ pr₂)
    second = (comp-unitˡ (id C) ▷ pr₂) ∙ second-before-unit

    normalized : (productMap f (id C) ∘ substitution) =₁ productMap (f ∘ σ) (id C)
    normalized = pair⁼ first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution

    normalization : productMap-first-comp {C = C} f σ =₂ normalized
    normalization =
      let firstUnit = id₌ (f ∘ σ) ▷ pr₁
          secondUnit = comp-unitˡ (id C) ▷ pr₂
          firstNormalization = comp₌-unitˡ-One first ∙
            comp₌-cong (preWhisker-id₌ (f ∘ σ) pr₁) (id₌ first)
          pairedNormalization = pair⁼-cong firstNormalization (id₌ second) ∙
            (pair⁼-comp firstUnit first secondUnit second-before-unit) ⁻¹
      in comp₌-cong pairedNormalization
          (id₌ (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution)) ∙
        (comp₌-assoc (pair⁼ firstUnit secondUnit)
          (pair⁼ first second-before-unit) (pair-pre (f ∘ pr₁) (id C ∘ pr₂) substitution)) ⁻¹

    projection₁ : SquareCell₌ (pr₁ ◁ productMap-first-comp {C = C} f σ) first
      (project-pair₁ (f ∘ pr₁) (id C ∘ pr₂) substitution)
      (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂))
    projection₁ = pair-evaluation-over₁-One (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
      comp₌-cong (id₌ (pair-β₁ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
        (postWhisker pr₁ ◁ normalization)

    projection₂ : SquareCell₌ (pr₂ ◁ productMap-first-comp {C = C} f σ) second
      (project-pair₂ (f ∘ pr₁) (id C ∘ pr₂) substitution)
      (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂))
    projection₂ = pair-evaluation-over₂-One (f ∘ pr₁) (id C ∘ pr₂) substitution first second ∙
      comp₌-cong (id₌ (pair-β₂ ((f ∘ σ) ∘ pr₁) (id C ∘ pr₂)))
        (postWhisker pr₂ ◁ normalization)
```

## The identity coordinate

The second coordinate is the second projection law followed by the left
unitor of `pr₂`. It is compatible with a further substitution `τ`.

```agda
  module _ {Y X : CAT Γ} where
    open Terms.InContext X using (Term)

    second-normalization : {Z : CAT Γ} (C : CAT Γ) (f : MAP X Z) (σ : MAP Y X)
      → Coordinates.second C f σ =₂
          (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂) ∙ (comp-unitˡ pr₂ ▷ productMap σ (id C)))
    second-normalization C f σ = post-square-cell-id pr₂ (id C) pr₂ (productMap σ (id C))
      (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂))

  module _ {W Y X : CAT Γ} where
    open Terms.InContext X using (Term)

    second-coordinate-assoc : {Z : CAT Γ} (C : CAT Γ)
      (f : MAP X Z) (σ : MAP Y X) (τ : MAP W Y)
      → (Coordinates.second C f (σ ∘ τ) ∙
            (((id C ∘ pr₂) ◁ productMap-first-comp {C = C} σ τ) ∙
              comp-assoc (productMap τ (id C)) (productMap σ (id C)) (id C ∘ pr₂))) =₂
          ((id₌ (id C) ▷ pr₂) ∙
            (Coordinates.second C (f ∘ σ) τ ∙
              (Coordinates.second C f σ ▷ productMap τ (id C))))
    second-coordinate-assoc C f σ τ =
      let s = productMap σ (id C)
          t = productMap τ (id C)
          st = productMap (σ ∘ τ) (id C)
          change = productMap-first-comp {C = C} σ τ
          b = pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)
          bst = pair-β₂ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
          S = Coordinates.second C f σ
          T = Coordinates.second C (f ∘ σ) τ
          normalized = T ∙ (S ▷ t)
          composition = FrameChange.compatible s t st change (id C ∘ pr₂) pr₂
            (id C ∘ pr₂) (id C ∘ pr₂) (comp-unitˡ pr₂) b bst S T
            (Coordinates.second C f (σ ∘ τ))
            (second-normalization C f σ)
            (second-normalization C f (σ ∘ τ))
            (Coordinates.projection₂ C σ τ)
          insertIdentity = (comp₌-unitˡ-One normalized ∙
            comp₌-cong (preWhisker-id₌ (id C) pr₂) (id₌ normalized)) ⁻¹
      in insertIdentity ∙ composition
```

## Pair inputs and restriction

Applied to a pair `pair p x`, `productMap f (id C)` gives `pair (f ∘ p) x`,
with the unitor of `x` in the second coordinate. This comparison is
compatible with restricting the pair.

```agda
  module _ {T : CAT Γ} where
    open Terms.InContext T using (Term)

    module PairInput {X Y C : CAT Γ} (f : MAP X Y) (p : Term X) (x : Term C) where

      first : ((f ∘ pr₁) ∘ pair p x) =₁ (f ∘ p)
      first = post-triangle f pr₁ (pair p x) (pair-β₁ p x)

      second : ((id C ∘ pr₂) ∘ pair p x) =₁ x
      second = comp-unitˡ x ∙ post-triangle (id C) pr₂ (pair p x) (pair-β₂ p x)

      at-pair : (productMap f (id C) ∘ pair p x) =₁ pair (f ∘ p) x
      at-pair = pair⁼ (id₌ (f ∘ p)) (comp-unitˡ x) ∙ productMap-pair f (id C) p x

      normalized : (productMap f (id C) ∘ pair p x) =₁ pair (f ∘ p) x
      normalized = pair⁼ first second ∙ pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x)

      normalization : at-pair =₂ normalized
      normalization =
        comp₌-cong
          (pair⁼-cong (comp₌-unitˡ-One first) (id₌ second) ∙
            (pair⁼-comp (id₌ (f ∘ p)) first (comp-unitˡ x)
              (post-triangle (id C) pr₂ (pair p x) (pair-β₂ p x))) ⁻¹) (id₌ _) ∙
        (comp₌-assoc (pair⁼ (id₌ (f ∘ p)) (comp-unitˡ x))
          (pair⁼ first (post-triangle (id C) pr₂ (pair p x) (pair-β₂ p x)))
          (pair-pre (f ∘ pr₁) (id C ∘ pr₂) (pair p x))) ⁻¹

  module _ {R T X : CAT Γ} where
    open Terms.InContext T using (Term)

    pair-input-first-restrict : {Y C : CAT Γ}
      (f : MAP X Y) (p : Term X) (x : Term C) (r : MAP R T)
      → (PairInput.first f (p ∘ r) (x ∘ r) ∙
            (((f ∘ pr₁) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (f ∘ pr₁))) =₂
          (comp-assoc r p f ∙ (PairInput.first f p x ▷ r))
    pair-input-first-restrict f p x r =
      comp₌-unitˡ-One _ ∙
      (comp₌-cong (postWhisker-id₌ f (p ∘ r)) (id₌ _) ∙
        post-triangle-change f pr₁ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
          (pair-β₁ p x) (pair-β₁ (p ∘ r) (x ∘ r)) (id₌ (p ∘ r))
          ((comp₌-unitˡ-One _) ⁻¹ ∙ pair-pre-triangle₁ p x r))

    pair-input-second-restrict : {Y C : CAT Γ}
      (f : MAP X Y) (p : Term X) (x : Term C) (r : MAP R T)
      → (PairInput.second f (p ∘ r) (x ∘ r) ∙
            (((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂))) =₂
          (PairInput.second f p x ▷ r)
    pair-input-second-restrict {C = C} f p x r =
      let before = post-triangle (id C) pr₂ (pair p x) (pair-β₂ p x)
          after = post-triangle (id C) pr₂ (pair (p ∘ r) (x ∘ r)) (pair-β₂ (p ∘ r) (x ∘ r))
          change = ((id C ∘ pr₂) ◁ pair-pre p x r) ∙ comp-assoc r (pair p x) (id C ∘ pr₂)
          coordinate = comp₌-unitˡ-One _ ∙
            (comp₌-cong (postWhisker-id₌ (id C) (x ∘ r)) (id₌ _) ∙
              post-triangle-change (id C) pr₂ (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
                (pair-β₂ p x) (pair-β₂ (p ∘ r) (x ∘ r)) (id₌ (x ∘ r))
                ((comp₌-unitˡ-One _) ⁻¹ ∙ pair-pre-triangle₂ p x r))
      in (preWhisker-comp₌ (comp-unitˡ x) before r) ⁻¹ ∙
        (comp₌-cong (left-unitor-comp r x) (id₌ (before ▷ r)) ∙
        ((comp₌-assoc (comp-unitˡ (x ∘ r)) (comp-assoc r x (id C)) (before ▷ r)) ⁻¹ ∙
        (comp₌-cong (id₌ (comp-unitˡ (x ∘ r))) coordinate ∙
          comp₌-assoc (comp-unitˡ (x ∘ r)) after change)))

    at-pair-restrict : {Y C : CAT Γ}
      (f : MAP X Y) (p : Term X) (x : Term C) (r : MAP R T)
      → (PairInput.at-pair f (p ∘ r) (x ∘ r) ∙
            ((productMap f (id C) ◁ pair-pre p x r) ∙
              comp-assoc r (pair p x) (productMap f (id C)))) =₂
          (pair⁼ (comp-assoc r p f) (id₌ (x ∘ r)) ∙
            (pair-pre (f ∘ p) x r ∙ (PairInput.at-pair f p x ▷ r)))
    at-pair-restrict {C = C} f p x r =
      let u = PairInput.first f p x
          v = PairInput.second f p x
          w = id₌ ((f ∘ p) ∘ r)
          z = id₌ (x ∘ r)
          a = PairInput.first f (p ∘ r) (x ∘ r)
          d = PairInput.second f (p ∘ r) (x ∘ r)
          η = comp-assoc r p f
          θ = id₌ (x ∘ r)
          base = pair-pre (f ∘ p) x r
          restriction = restriction-diagram (pair p x) r (pair (p ∘ r) (x ∘ r)) (pair-pre p x r)
          assembled = pair-compatible-One restriction (evaluation a u w η) (evaluation d v z θ)
            (comp₌-cong (id₌ η) ((comp₌-unitˡ-One (u ▷ r)) ⁻¹) ∙ pair-input-first-restrict f p x r)
            ((comp₌-unitˡ-One _) ⁻¹ ∙
              ((comp₌-unitˡ-One (v ▷ r)) ⁻¹ ∙ pair-input-second-restrict f p x r))
          long-normal = comp₌-cong (id₌ (pair⁼ η θ))
            (comp₌-cong (comp₌-unitˡ-One base ∙
                comp₌-cong (pair⁼-id-One ((f ∘ p) ∘ r) (x ∘ r)) (id₌ base))
              (preWhisker r ◁ (PairInput.normalization f p x) ⁻¹))
      in long-normal ∙
        (assembled ∙ comp₌-cong (PairInput.normalization f (p ∘ r) (x ∘ r)) (id₌ _))
```

## Normalizing the identity coordinate

Replacing `id C ∘ pr₂` by `pr₂` on both sides of `productMap-first-comp f σ`
gives the paired evaluation of the first coordinate and the second
projection law.

```agda
  module UnitNormalization {P Q X C : CAT Γ} (f : MAP P X) (σ : MAP Q P) where

    s : MAP (Q × C) (P × C)
    s = productMap σ (id C)

    change : (productMap f (id C) ∘ s) =₁ productMap (f ∘ σ) (id C)
    change = productMap-first-comp f σ

    before : productMap f (id C) =₁ pair (f ∘ pr₁) pr₂
    before = pair⁼ (id₌ (f ∘ pr₁)) (comp-unitˡ pr₂)

    after : productMap (f ∘ σ) (id C) =₁ pair ((f ∘ σ) ∘ pr₁) pr₂
    after = pair⁼ (id₌ ((f ∘ σ) ∘ pr₁)) (comp-unitˡ pr₂)

    first : ((f ∘ pr₁) ∘ s) =₁ (f ∘ (σ ∘ pr₁))
    first = (f ◁ pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)) ∙ comp-assoc s pr₁ f

    second : (pr₂ ∘ s) =₁ pr₂
    second = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)

    finish : pair ((f ∘ σ) ∘ pr₁) pr₂ =₁ pair (f ∘ (σ ∘ pr₁)) (pr₂ {C = Q} {D = C})
    finish = pair⁼ (comp-assoc pr₁ σ f) (id₌ pr₂)

    changed : (pair (f ∘ pr₁) pr₂ ∘ s) =₁ pair (f ∘ (σ ∘ pr₁)) pr₂
    changed = pair⁼ first second ∙ pair-pre (f ∘ pr₁) pr₂ s

    unit-square : ((finish ∙ after) ∙ change) =₂ (changed ∙ (before ▷ s))
    unit-square =
      let A = comp-assoc pr₁ σ f
          e = Coordinates.first C f σ
          d = Coordinates.second C f σ
          unitBefore = comp-unitˡ pr₂
          unitAfter = comp-unitˡ pr₂
          firstNormalize = (comp₌-cong (id₌ first) (preWhisker-id₌ (f ∘ pr₁) s)) ⁻¹ ∙
            ((comp₌-unitʳ-One first) ⁻¹ ∙
              (comp-inv-left A first ∙ comp₌-cong (id₌ A) (comp₌-unitˡ-One e)))
          secondNormalize = (comp₌-assoc unitAfter
              (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂)) (unitBefore ▷ s)) ⁻¹ ∙
            (comp₌-cong (id₌ unitAfter) (second-normalization C f σ) ∙
              comp₌-unitˡ-One (unitAfter ∙ d))
          firstSquare = (comp₌-assoc A (id₌ ((f ∘ σ) ∘ pr₁)) e) ⁻¹ ∙ firstNormalize ⁻¹
          secondSquare = (comp₌-assoc (id₌ pr₂) unitAfter d) ⁻¹ ∙ secondNormalize ⁻¹
          natural = pair-evaluation-natural-inputs-One (id₌ (f ∘ pr₁)) unitBefore s
            e first d second (A ∙ id₌ ((f ∘ σ) ∘ pr₁)) (id₌ pr₂ ∙ unitAfter)
            firstSquare secondSquare
      in natural ⁻¹ ∙
        comp₌-cong ((pair⁼-comp A (id₌ ((f ∘ σ) ∘ pr₁)) (id₌ pr₂) unitAfter) ⁻¹)
          (Coordinates.normalization C f σ)
```

## Changing both the first functor and the pair input

```agda
  module _ {T X : CAT Γ} where
    open Terms.InContext T using (Term)

    pair-input-second-normalization : {Y C : CAT Γ}
      (f : MAP X Y) (p : Term X) (x : Term C)
      → PairInput.second f p x =₂ (pair-β₂ p x ∙ (comp-unitˡ pr₂ ▷ pair p x))
    pair-input-second-normalization {C = C} f p x =
      comp₌-cong (id₌ (pair-β₂ p x)) (left-unitor-comp (pair p x) pr₂) ∙
        (comp₌-assoc (pair-β₂ p x) (comp-unitˡ (pr₂ ∘ pair p x)) (comp-assoc (pair p x) pr₂ (id C)) ∙
        (comp₌-cong (postWhisker-id-One (pair-β₂ p x)) (id₌ (comp-assoc (pair p x) pr₂ (id C))) ∙
          (comp₌-assoc (comp-unitˡ x) (id C ◁ pair-β₂ p x) (comp-assoc (pair p x) pr₂ (id C))) ⁻¹))

    at-pair-projection₁ : {Y C : CAT Γ} (f : MAP X Y) (p : Term X) (x : Term C)
      → SquareCell₌ (pr₁ ◁ PairInput.at-pair f p x) (PairInput.first f p x)
          (project-pair₁ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)) (pair-β₁ (f ∘ p) x)
    at-pair-projection₁ {C = C} f p x =
      pair-evaluation-over₁-One (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
        (PairInput.first f p x) (PairInput.second f p x) ∙
          comp₌-cong (id₌ (pair-β₁ (f ∘ p) x)) (postWhisker pr₁ ◁ PairInput.normalization f p x)

    at-pair-projection₂ : {Y C : CAT Γ} (f : MAP X Y) (p : Term X) (x : Term C)
      → SquareCell₌ (pr₂ ◁ PairInput.at-pair f p x) (PairInput.second f p x)
          (project-pair₂ (f ∘ pr₁) (id C ∘ pr₂) (pair p x)) (pair-β₂ (f ∘ p) x)
    at-pair-projection₂ {C = C} f p x =
      pair-evaluation-over₂-One (f ∘ pr₁) (id C ∘ pr₂) (pair p x)
        (PairInput.first f p x) (PairInput.second f p x) ∙
          comp₌-cong (id₌ (pair-β₂ (f ∘ p) x)) (postWhisker pr₂ ◁ PairInput.normalization f p x)

  module _ {T : CAT Γ} where
    open Terms.InContext T using (Term)

    pair-input-first-change : {Q P Y C : CAT Γ}
      (f : MAP P Y) (σ : MAP Q P) (p : Term Q) (x : Term C)
      → (PairInput.first f (σ ∘ p) x ∙
            (((f ∘ pr₁) ◁ PairInput.at-pair σ p x) ∙
              comp-assoc (pair p x) (productMap σ (id C)) (f ∘ pr₁))) =₂
          (comp-assoc p σ f ∙
            (PairInput.first (f ∘ σ) p x ∙ (Coordinates.first C f σ ▷ pair p x)))
    pair-input-first-change {C = C} f σ p x =
      let h = productMap σ (id C)
          t = pair p x
          n = PairInput.at-pair σ p x
          b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
          c = PairInput.first σ p x
          original = post-triangle f pr₁ h b
          u = Coordinates.first C f σ
          w = PairInput.first (f ∘ σ) p x
          A = comp-assoc p σ f
          corner = comp-assoc pr₁ σ f
          mid = comp-assoc t (σ ∘ pr₁) f
          simplify = (preWhisker t ◁ comp-inv-left corner original) ∙
            (preWhisker-comp₌ corner u t) ⁻¹
          normalizeLong = comp₌-cong (id₌ (f ◁ c)) (comp₌-cong (id₌ mid) simplify) ∙
            (comp₌-cong (id₌ (f ◁ c)) (comp₌-assoc mid (corner ▷ t) (u ▷ t)) ∙
            (comp₌-assoc (f ◁ c) (mid ∙ (corner ▷ t)) (u ▷ t) ∙
            (comp₌-cong (post-triangle-comp f σ pr₁ t (pair-β₁ p x)) (id₌ (u ▷ t)) ∙
              (comp₌-assoc A w (u ▷ t)) ⁻¹)))
      in normalizeLong ⁻¹ ∙
        post-triangle-change f pr₁ h t (pair (σ ∘ p) x) n b (pair-β₁ (σ ∘ p) x) c
          (at-pair-projection₁ σ p x)

    pair-input-second-change : {Q P Y C : CAT Γ}
      (f : MAP P Y) (σ : MAP Q P) (p : Term Q) (x : Term C)
      → (PairInput.second f (σ ∘ p) x ∙
            (((id C ∘ pr₂) ◁ PairInput.at-pair σ p x) ∙
              comp-assoc (pair p x) (productMap σ (id C)) (id C ∘ pr₂))) =₂
          (id₌ x ∙
            (PairInput.second (f ∘ σ) p x ∙ (Coordinates.second C f σ ▷ pair p x)))
    pair-input-second-change {C = C} f σ p x =
      let h = productMap σ (id C)
          t = pair p x
          n = PairInput.at-pair σ p x
          S = Coordinates.second C f σ
          T = PairInput.second (f ∘ σ) p x
          normalized = T ∙ (S ▷ t)
          composition = FrameChange.compatible h t (pair (σ ∘ p) x) n (id C ∘ pr₂) pr₂
            (id C ∘ pr₂) x (comp-unitˡ pr₂) (pair-β₂ (σ ∘ pr₁) (id C ∘ pr₂))
            (pair-β₂ (σ ∘ p) x) S T (PairInput.second f (σ ∘ p) x)
            (second-normalization C f σ) (pair-input-second-normalization f (σ ∘ p) x)
            (at-pair-projection₂ σ p x)
      in (comp₌-unitˡ-One normalized) ⁻¹ ∙ composition

    at-pair-input-change : {Q P Y C : CAT Γ}
      (f : MAP P Y) (σ : MAP Q P) (p : Term Q) (x : Term C)
      → (PairInput.at-pair f (σ ∘ p) x ∙
            ((productMap f (id C) ◁ PairInput.at-pair σ p x) ∙
              comp-assoc (pair p x) (productMap σ (id C)) (productMap f (id C)))) =₂
          (pair⁼ (comp-assoc p σ f) (id₌ x) ∙
            (PairInput.at-pair (f ∘ σ) p x ∙ (productMap-first-comp {C = C} f σ ▷ pair p x)))
    at-pair-input-change {C = C} f σ p x =
      let u = Coordinates.first C f σ
          v = Coordinates.second C f σ
          w = PairInput.first (f ∘ σ) p x
          z = PairInput.second (f ∘ σ) p x
          a = PairInput.first f (σ ∘ p) x
          d = PairInput.second f (σ ∘ p) x
          η = comp-assoc p σ f
          θ = id₌ x
          substitution = restriction-diagram (productMap σ (id C)) (pair p x) (pair (σ ∘ p) x)
            (PairInput.at-pair σ p x)
          assembled = pair-compatible-One substitution (evaluation a u w η) (evaluation d v z θ)
            (pair-input-first-change f σ p x) (pair-input-second-change f σ p x)
          normalizeShort = comp₌-cong (PairInput.normalization f (σ ∘ p) x) (id₌ _)
          normalizeLong = comp₌-cong (id₌ (pair⁼ η θ))
            (comp₌-cong (PairInput.normalization (f ∘ σ) p x)
              (preWhisker (pair p x) ◁ Coordinates.normalization C f σ))
      in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)
```

## The first coordinate of a binary functor

For a binary functor `F`, restricting `binary-apply F g f` along the
first projection is compatible with the substitution `productMap σ (id C)`.

```agda
module _ {Γ : Context} where
  module BinaryFirstCoordinate {P Q A B Z : CAT Γ} (C : CAT Γ)
    (F : MAP (A × B) Z) (g : MAP P A) (f : MAP P B) (σ : MAP Q P) where

    s : MAP (Q × C) (P × C)
    s = productMap σ (id C)
    δ : (pr₁ ∘ s) =₁ (σ ∘ pr₁)
    δ = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
    first-associator : ((g ∘ σ) ∘ pr₁) =₁ (g ∘ (σ ∘ pr₁))
    first-associator = comp-assoc (pr₁ {C = Q} {D = C}) σ g
    second-associator : ((f ∘ σ) ∘ pr₁) =₁ (f ∘ (σ ∘ pr₁))
    second-associator = comp-assoc (pr₁ {C = Q} {D = C}) σ f
    output-associator :
      ((binary-apply F g f ∘ σ) ∘ pr₁) =₁ (binary-apply F g f ∘ (σ ∘ pr₁))
    output-associator = comp-assoc (pr₁ {C = Q} {D = C}) σ (binary-apply F g f)
    first-coordinate : ((g ∘ pr₁) ∘ s) =₁ ((g ∘ σ) ∘ pr₁)
    first-coordinate = Coordinates.first C g σ
    second-coordinate : ((f ∘ pr₁) ∘ s) =₁ ((f ∘ σ) ∘ pr₁)
    second-coordinate = Coordinates.first C f σ
    output-coordinate :
      ((binary-apply F g f ∘ pr₁) ∘ s) =₁ ((binary-apply F g f ∘ σ) ∘ pr₁)
    output-coordinate = Coordinates.first C (binary-apply F g f) σ
    original-route :
      (binary-apply F g f ∘ pr₁) =₁ binary-apply F (g ∘ pr₁) (f ∘ pr₁)
    original-route = binary-cong F (id₌ (g ∘ pr₁ {C = P} {D = C})) (id₌ (f ∘ pr₁ {C = P} {D = C})) ∙
      binary-pre F g f (pr₁ {C = P} {D = C})
    changed-route : (binary-apply F g f ∘ (σ ∘ pr₁)) =₁
      binary-apply F ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁)
    changed-route = binary-cong F (first-associator ⁻¹) (second-associator ⁻¹) ∙
      binary-pre F g f (σ ∘ pr₁ {C = Q} {D = C})
    tail : ((binary-apply F g f ∘ pr₁) ∘ s) =₁ (binary-apply F g f ∘ (σ ∘ pr₁))
    tail = (binary-apply F g f ◁ δ) ∙ comp-assoc s pr₁ (binary-apply F g f)
    iterated-route : ((binary-apply F g f ∘ σ) ∘ pr₁) =₁
      binary-apply F ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁)
    iterated-route = binary-pre F (g ∘ σ) (f ∘ σ) (pr₁ {C = Q} {D = C}) ∙
      (binary-pre F g f σ ▷ pr₁ {C = Q} {D = C})

    abstract
      old-normalization : original-route =₂ binary-pre F g f pr₁
      old-normalization = comp₌-unitˡ-One (binary-pre F g f pr₁) ∙
        comp₌-cong (binary-cong-id-One F (g ∘ pr₁) (f ∘ pr₁)) (id₌ (binary-pre F g f pr₁))

    abstract
      new-normalization : changed-route =₂ (iterated-route ∙ output-associator ⁻¹)
      new-normalization =
        let inverseAction = binary-cong F (first-associator ⁻¹) (second-associator ⁻¹)
            forwardAction = binary-cong F first-associator second-associator
            cancelAction = binary-cong-id-One F ((g ∘ σ) ∘ pr₁) ((f ∘ σ) ∘ pr₁) ∙
              (binary-cong₂ F (comp₌-inverseˡ-One first-associator)
                (comp₌-inverseˡ-One second-associator) ∙
                (binary-cong-comp F (first-associator ⁻¹) first-associator
                  (second-associator ⁻¹) second-associator) ⁻¹)
            square = comp₌-unitˡ-One iterated-route ∙
              (comp₌-cong cancelAction (id₌ iterated-route) ∙
                ((comp₌-assoc inverseAction forwardAction iterated-route) ⁻¹ ∙
                  (comp₌-cong (id₌ inverseAction) (binary-pre-iterated F g f σ pr₁) ∙
                    comp₌-assoc inverseAction (binary-pre F g f (σ ∘ pr₁)) output-associator)))
        in comp₌-cong square (id₌ (output-associator ⁻¹)) ∙
          (comp-inv-right changed-route output-associator) ⁻¹

    abstract
      compatibility :
        (binary-pre F (g ∘ σ) (f ∘ σ) pr₁ ∙ ((binary-pre F g f σ ▷ pr₁) ∙ output-coordinate)) =₂
        (binary-cong F first-coordinate second-coordinate ∙
          (binary-pre F (g ∘ pr₁) (f ∘ pr₁) s ∙ (binary-pre F g f pr₁ ▷ s)))
      compatibility =
        let first = (comp₌-unitʳ-One first-coordinate ∙
              comp₌-cong (id₌ first-coordinate) (preWhisker-id₌ (g ∘ pr₁) s)) ⁻¹
            second = (comp₌-unitʳ-One second-coordinate ∙
              comp₌-cong (id₌ second-coordinate) (preWhisker-id₌ (f ∘ pr₁) s)) ⁻¹
            restriction = restriction-diagram pr₁ s (σ ∘ pr₁) δ
            unstaged : {K : CAT Γ} (h : MAP P K) (c : ((h ∘ pr₁) ∘ s) =₁ ((h ∘ σ) ∘ pr₁))
              → (c ∙ (id₌ ((h ∘ pr₁) ∘ s) ∙ (id₌ (h ∘ pr₁) ▷ s))) =₂ (c ∙ (id₌ (h ∘ pr₁) ▷ s))
            unstaged h c = comp₌-cong (id₌ c) (comp₌-unitˡ-One (id₌ (h ∘ pr₁) ▷ s))
            second-stage = binary-pre F (g ∘ pr₁) (f ∘ pr₁) s
            trivial-stage = comp₌-unitˡ-One second-stage ∙
              comp₌-cong (binary-cong-id-One F ((g ∘ pr₁) ∘ s) ((f ∘ pr₁) ∘ s)) (id₌ second-stage)
            binary = binary-compatible restriction F
              (evaluation (first-associator ⁻¹) (id₌ (g ∘ pr₁))
                (id₌ ((g ∘ pr₁) ∘ s)) first-coordinate)
              (evaluation (second-associator ⁻¹) (id₌ (f ∘ pr₁))
                (id₌ ((f ∘ pr₁) ∘ s)) second-coordinate)
              ((unstaged g first-coordinate) ⁻¹ ∙ first) ((unstaged f second-coordinate) ⁻¹ ∙ second)
            assembled = comp₌-cong (id₌ (binary-cong F first-coordinate second-coordinate))
                (comp₌-cong trivial-stage (id₌ _)) ∙
              binary
            left = comp₌-cong (new-normalization ⁻¹) (id₌ tail) ∙
              ((comp₌-assoc iterated-route (output-associator ⁻¹) tail) ⁻¹ ∙
                (comp₌-assoc (binary-pre F (g ∘ σ) (f ∘ σ) pr₁) (binary-pre F g f σ ▷ pr₁)
                  output-coordinate) ⁻¹)
            right = comp₌-cong (id₌ (binary-cong F first-coordinate second-coordinate))
              (comp₌-cong (id₌ (binary-pre F (g ∘ pr₁) (f ∘ pr₁) s))
                (preWhisker s ◁ old-normalization))
        in right ∙ (assembled ∙ left)
```

## Associativity

Successive substitutions along `σ` and `τ` agree with the substitution along
`σ ∘ τ`, compatibly with the comparisons. The first coordinate is a
comparison of postcomposed square cells; the second keeps the unitor.

```agda
  module _ {Q R X : CAT Γ} where
    open Terms.InContext X using (Term)

    first-coordinate-assoc : {Z : CAT Γ} (C : CAT Γ)
      (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
      → (Coordinates.first C f (σ ∘ τ) ∙
            (((f ∘ pr₁) ◁ productMap-first-comp {C = C} σ τ) ∙
              comp-assoc (productMap τ (id C)) (productMap σ (id C)) (f ∘ pr₁))) =₂
          ((comp-assoc τ σ f ▷ pr₁) ∙
            (Coordinates.first C (f ∘ σ) τ ∙
              (Coordinates.first C f σ ▷ productMap τ (id C))))
    first-coordinate-assoc C f σ τ =
      let h = productMap σ (id C)
          k = productMap τ (id C)
          l = productMap (σ ∘ τ) (id C)
          change = productMap-first-comp {C = C} σ τ
          b = pair-β₁ (σ ∘ pr₁) (id C ∘ pr₂)
          b′ = pair-β₁ ((σ ∘ τ) ∘ pr₁) (id C ∘ pr₂)
          c = Coordinates.first C σ τ
          outside = (comp-assoc pr₁ (σ ∘ τ) f) ⁻¹
          leftImage = f ◁ b′
          inputA = comp-assoc l pr₁ f
          image-change = (f ∘ pr₁) ◁ change
          sourceA = comp-assoc k h (f ∘ pr₁)
          normalizeShort = comp₌-cong (id₌ outside)
            (post-triangle-change f pr₁ h k l change b b′ c (Coordinates.projection₁ C σ τ)) ∙
            comp₌-assoc outside (leftImage ∙ inputA) (image-change ∙ sourceA)
          u = Coordinates.first C f σ
          w = Coordinates.first C (f ∘ σ) τ
          delta = comp-assoc τ σ f ▷ pr₁
          sourceCorner = comp-assoc pr₁ σ f
          imageBefore = (f ◁ b) ∙ comp-assoc h pr₁ f
          nextCoordinate = post-square-cell f pr₁ (σ ∘ τ) (σ ∘ pr₁) k c
          outerSquare = (post-square-cell-comp pr₁ τ pr₁ k
            (pair-β₁ (τ ∘ pr₁) (id C ∘ pr₂)) σ f) ⁻¹
          simplifyCorner = (preWhisker k ◁ comp-inv-left sourceCorner imageBefore) ∙
            (preWhisker-comp₌ sourceCorner u k) ⁻¹
          normalizeLong = comp₌-cong (id₌ outside)
            (comp₌-assoc (f ◁ c) (comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k)) ∙
            (comp₌-assoc outside ((f ◁ c) ∙ comp-assoc k (σ ∘ pr₁) f) (imageBefore ▷ k) ∙
              (comp₌-cong (id₌ nextCoordinate) simplifyCorner ∙
                (comp₌-assoc nextCoordinate (sourceCorner ▷ k) (u ▷ k) ∙
                  (comp₌-cong outerSquare (id₌ (u ▷ k)) ∙
                    (comp₌-assoc delta w (u ▷ k)) ⁻¹))))
      in normalizeLong ⁻¹ ∙ normalizeShort

    productMap-first-comp-assoc : {Z : CAT Γ} (C : CAT Γ)
      (f : MAP X Z) (σ : MAP R X) (τ : MAP Q R)
      → (productMap-first-comp {C = C} f (σ ∘ τ) ∙
            ((productMap f (id C) ◁ productMap-first-comp {C = C} σ τ) ∙
              comp-assoc (productMap τ (id C)) (productMap σ (id C)) (productMap f (id C)))) =₂
          (productMap-cong (comp-assoc τ σ f) (id₌ (id C)) ∙
            (productMap-first-comp {C = C} (f ∘ σ) τ ∙
              (productMap-first-comp {C = C} f σ ▷ productMap τ (id C))))
    productMap-first-comp-assoc C f σ τ =
      let h = productMap σ (id C)
          k = productMap τ (id C)
          l = productMap (σ ∘ τ) (id C)
          change = productMap-first-comp {C = C} σ τ
          sourceTail = (productMap f (id C) ◁ change) ∙ comp-assoc k h (productMap f (id C))
          delta = productMap-cong (comp-assoc τ σ f) (id₌ (id C))
          normalizeShort = comp₌-cong (Coordinates.normalization C f (σ ∘ τ)) (id₌ sourceTail)
          normalizeLong = comp₌-cong (id₌ delta)
            (comp₌-cong (Coordinates.normalization C (f ∘ σ) τ)
              (preWhisker k ◁ Coordinates.normalization C f σ))
          successive = restriction-diagram h k l change
          first-evaluation = evaluation (Coordinates.first C f (σ ∘ τ)) (Coordinates.first C f σ)
            (Coordinates.first C (f ∘ σ) τ) (comp-assoc τ σ f ▷ pr₁)
          second-evaluation = evaluation (Coordinates.second C f (σ ∘ τ))
            (Coordinates.second C f σ) (Coordinates.second C (f ∘ σ) τ) (id₌ (id C) ▷ pr₂)
          assembled = pair-compatible-One successive first-evaluation second-evaluation
            (first-coordinate-assoc C f σ τ) (second-coordinate-assoc C f σ τ)
      in normalizeLong ⁻¹ ∙ (assembled ∙ normalizeShort)
```

## Unit laws

The fixed identity coordinate is merged with the unit of the varying
coordinate. The right unit uses the identification of the two unitors of
`id K`.

```agda
  private
    module _ {X : CAT Γ} where
      open Terms.InContext X using (Term)

      merge-fixed-unit : {Y : CAT Γ} (K : CAT Γ) {x y : Term Y} (p : x =₁ y)
        → (productMap-cong p (id₌ (id K)) ∙ productMap-cong (id₌ x) (comp-unitˡ (id K))) =₂
            productMap-cong p (comp-unitˡ (id K))
      merge-fixed-unit K p =
        productMap-cong₂ (comp₌-unitʳ-One p) (comp₌-unitˡ-One (comp-unitˡ (id K))) ∙
          (productMap-cong-comp p (id₌ _) (id₌ (id K)) (comp-unitˡ (id K))) ⁻¹

  module _ {X : CAT Γ} where
    open Terms.InContext X using (Term)

    abstract

      productMap-first-comp-unitˡ : {Y : CAT Γ} (K : CAT Γ) (z : Term Y)
        → (productMap-cong (comp-unitˡ z) (id₌ (id K)) ∙ productMap-first-comp (id Y) z) =₂
            (comp-unitˡ (productMap z (id K)) ∙ (productMap-id Y K ▷ productMap z (id K)))
      productMap-first-comp-unitˡ  {Y} K z = productMap-unitˡ z (id K) ∙
        (comp₌-cong (merge-fixed-unit K (comp-unitˡ z))
          (id₌ (productMap-comp z (id Y) (id K) (id K))) ∙
        (comp₌-assoc (productMap-cong (comp-unitˡ z) (id₌ (id K)))
          (productMap-cong (id₌ (id Y ∘ z)) (comp-unitˡ (id K)))
          (productMap-comp z (id Y) (id K) (id K))) ⁻¹)

      productMap-first-comp-unitʳ : {Y : CAT Γ} (K : CAT Γ) (z : Term Y)
        → (productMap-cong (comp-unitʳ z) (id₌ (id K)) ∙ productMap-first-comp z (id X)) =₂
            (comp-unitʳ (productMap z (id K)) ∙ (productMap z (id K) ◁ productMap-id X K))
      productMap-first-comp-unitʳ  {Y} K z = productMap-unitʳ z (id K) ∙
        (comp₌-cong (productMap-cong₂ (id₌ (comp-unitʳ z)) ((identity-unitors K) ⁻¹) ∙
          merge-fixed-unit K (comp-unitʳ z)) (id₌ (productMap-comp (id X) z (id K) (id K))) ∙
        (comp₌-assoc (productMap-cong (comp-unitʳ z) (id₌ (id K)))
          (productMap-cong (id₌ (z ∘ id X)) (comp-unitˡ (id K)))
          (productMap-comp (id X) z (id K) (id K))) ⁻¹)
```

## The projection pairing under a product functor

Postcomposing `pair-projections` with a product functor gives
`productMap-pair` at the projections, and the same holds for the
identification `pair pr₁ z = id` built from `u : z = pr₂`.

```agda
  pair-projections-post : {A B C D : CAT Γ} (f : MAP A B) (g : MAP C D)
    → (comp-unitʳ (productMap f g) ∙ (productMap f g ◁ pair-projections)) =₂
        productMap-pair f g pr₁ pr₂
  pair-projections-post f g =
    let a = f ∘ pr₁
        b = g ∘ pr₂
        H = pair pr₁ pr₂
        η = pair-projections
        left = comp-unitʳ a
        right = comp-unitʳ b
        first = a ◁ η
        second = b ◁ η
        outer = pair⁼ left right
        inner = pair⁼ first second
        pre = pair-pre a b H
        normalize = pair⁼-cong
          (identity-post-coordinate pr₁ f H η (pair-β₁ pr₁ pr₂) pair-projections-triangle₁)
          (identity-post-coordinate pr₂ g H η (pair-β₂ pr₁ pr₂) pair-projections-triangle₂)
    in comp₌-cong normalize (id₌ pre) ∙
      (comp₌-cong ((pair⁼-comp left first right second) ⁻¹) (id₌ pre) ∙
      ((comp₌-assoc outer inner pre) ⁻¹ ∙
      (comp₌-cong (id₌ outer) (pair-pre-natural-substitution-One a b η) ∙
      (comp₌-assoc outer (pair-pre a b (id _)) (productMap f g ◁ η) ∙
        comp₌-cong ((pair-pre-id a b) ⁻¹) (id₌ (productMap f g ◁ η))))))

  pair-pr₁-id-post : {P Q C : CAT Γ} (σ : MAP Q P) {x : MAP (Q × C) C}
    (u : x =₁ pr₂)
    → (comp-unitʳ (productMap σ (id C)) ∙
          (productMap σ (id C) ◁ (pair-projections ∙ pair⁼ (id₌ pr₁) u))) =₂
        (pair⁼ (id₌ (σ ∘ pr₁)) (id C ◁ u) ∙ productMap-pair σ (id C) pr₁ x)
  pair-pr₁-id-post {C = C} σ {x} u =
    let s = productMap σ (id C)
        η = pair-projections
        r = pair⁼ (id₌ pr₁) u
    in comp₌-cong (pair⁼-cong (postWhisker-id₌ σ pr₁) (id₌ (id C ◁ u)))
        (id₌ (productMap-pair σ (id C) pr₁ x)) ∙
      (productMap-pair-inner-One σ (id C) (id₌ pr₁) u ∙
      (comp₌-cong (pair-projections-post σ (id C)) (id₌ (s ◁ r)) ∙
      ((comp₌-assoc (comp-unitʳ s) (s ◁ η) (s ◁ r)) ⁻¹ ∙
        comp₌-cong (id₌ (comp-unitʳ s)) (postWhisker-comp₌ s η r))))
```

## Reassociation

Changing the first factor of a triple product commutes with the
associativity functors of ProductConstructions. Both comparisons are
assembled from their coordinates.

```agda
module _ {Γ : Context} {R Y X C : CAT Γ} (σ : MAP R Y) where
  private
    leftChange : MAP ((R × X) × C) ((Y × X) × C)
    leftChange = productMap (productMap σ (id X)) (id C)
    rightChange : MAP (R × (X × C)) (Y × (X × C))
    rightChange = productMap σ (id (X × C))

  forward-natural :
    (Associativity.forward Y X C ∘ leftChange) =₁ (rightChange ∘ Associativity.forward R X C)
  forward-natural =
    let first = project-product₁ σ (id X) pr₁ ∙
          ((pr₁ ◁ pair-β₁ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)) ∙
            comp-assoc leftChange pr₁ pr₁)
        second = comp-unitˡ (pr₂ ∘ pr₁) ∙
          (project-product₂ σ (id X) pr₁ ∙
          ((pr₂ ◁ pair-β₁ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)) ∙
            comp-assoc leftChange pr₁ pr₂))
        third = comp-unitˡ pr₂ ∙ pair-β₂ (productMap σ (id X) ∘ pr₁) (id C ∘ pr₂)
        left-normal = pair⁼ first
          (pair⁼ second third ∙ pair-pre (pr₂ ∘ pr₁) pr₂ leftChange) ∙
          pair-pre (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂) leftChange
        right-normal = pair⁼ (id₌ (σ ∘ (pr₁ ∘ pr₁)))
          (comp-unitˡ (pair (pr₂ ∘ pr₁) pr₂)) ∙
          productMap-pair σ (id (X × C)) (pr₁ ∘ pr₁) (pair (pr₂ ∘ pr₁) pr₂)
    in right-normal ⁻¹ ∙ left-normal

  backward-natural :
    (Associativity.backward Y X C ∘ rightChange) =₁ (leftChange ∘ Associativity.backward R X C)
  backward-natural =
    let first = pair-β₁ (σ ∘ pr₁) (id (X × C) ∘ pr₂)
        secondProjection = comp-unitˡ pr₂ ∙ pair-β₂ (σ ∘ pr₁) (id (X × C) ∘ pr₂)
        second = (pr₁ ◁ secondProjection) ∙ comp-assoc rightChange pr₂ pr₁
        third = (pr₂ ◁ secondProjection) ∙ comp-assoc rightChange pr₂ pr₂
        left-normal = pair⁼
          (pair⁼ first second ∙ pair-pre pr₁ (pr₁ ∘ pr₂) rightChange)
          third ∙ pair-pre (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂) rightChange
        right-normal = pair⁼
          (pair⁼ (id₌ (σ ∘ pr₁)) (comp-unitˡ (pr₁ ∘ pr₂)) ∙
            productMap-pair σ (id X) pr₁ (pr₁ ∘ pr₂))
          (comp-unitˡ (pr₂ ∘ pr₂)) ∙
          productMap-pair (productMap σ (id X)) (id C) (pair pr₁ (pr₁ ∘ pr₂)) (pr₂ ∘ pr₂)
    in right-normal ⁻¹ ∙ left-normal
```
