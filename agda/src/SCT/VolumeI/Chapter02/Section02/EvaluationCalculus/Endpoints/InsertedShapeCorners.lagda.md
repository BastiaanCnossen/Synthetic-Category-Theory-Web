# Inserting a specified corner of a diagram shape

A corner identification between two restricted vertices determines a
comparison between their parameterized insertions. Both projections below
retain that particular identification. The parameter projection agrees
with the corner obtained from currying a square. The corresponding diagram
projection calculation is completed in `RectangularCornerNormalization`.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories

module SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.InsertedShapeCorners
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) where

open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.EndpointEvaluation 𝒯 M ℱ public
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.RestrictionInsertions as Restriction
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Restriction.InsertionRestrictionCompatibility as Compatibility
import SCT.VolumeI.Chapter02.Section02.EvaluationCalculus.Endpoints.EndpointInputNaturality as Objects
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareParameterCorner as Parameter
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCorner as CurriedCorner
import SCT.VolumeI.Chapter02.Section02.SquareCalculus.SquareCurryingCoordinates as Coordinates
import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares as Projections
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingCoherence as Pairing
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Naturality
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (pair-cong-triangle₁; pair-cong-triangle₂; pair-iso-extensionality)
open Naturality vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-left-reflect; cancel-right)
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.ProductFunctorUnits as ProductUnits
open ProductUnits vocabulary terminal products productLaws composition vertical whiskering pentagonTriangle
  using (pair-pre-cong-triangle₁; pair-pre-cong-triangle₂; left-unitor-comp)
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.SplitProjectionCalculus 𝒯 using (section-pre)
open import SCT.VolumeI.Chapter01.Section04.Substitution.IdentityParameterChange 𝒯 M using (terminal-Iso₂)
open import SCT.VolumeI.Chapter01.Section04.Substitution.ConstantSubstitution 𝒯 M using (const-pre-compose)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms
  vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
open Structural vocabulary terminal products productLaws composition whiskering using (postWhisker-id-at)
module PS = Projections 𝒯

module At {A B D : CAT} (Γ : CAT) (f : MAP A D) (g : MAP B D)
  (u : Obj-abs A) (v : Obj-abs B) (δ : (f ∘ u) =₁ (g ∘ v)) where
  i = insert {X = Γ} u
  j = insert {X = Γ} v
  F = productMap (id Γ) f
  G = productMap (id Γ) g
  κ = Restriction.insertion 𝒯 M ℱ Γ f u
  κ′ = Restriction.insertion 𝒯 M ℱ Γ g v
  middle = Objects.insert-cong 𝒯 M ℱ {X = Γ} δ
  constant-corner = δ ▷ terminate Γ

  comparison : (F ∘ i) =₁ (G ∘ j)
  comparison = κ′ ⁻¹ ∙ (middle ∙ κ)

  module FirstF = Compatibility.RestrictionFirst 𝒯 M ℱ Γ f u
  module FirstG = Compatibility.RestrictionFirst 𝒯 M ℱ Γ g v
  first-source = FirstF.source
  first-target = FirstG.source
  first-middle-source = pair-β₁ (id Γ) (const (f ∘ u))
  first-middle-target = pair-β₁ (id Γ) (const (g ∘ v))

  abstract
    middle-parameter : PS.Square pr₁ first-middle-source first-middle-target middle
    middle-parameter = isoComp-unitˡ-at first-middle-source ∙
      pair-cong-triangle₁ (idIso (id Γ)) constant-corner

    parameter : PS.Square pr₁ first-source first-target comparison
    parameter = PS.compose-square pr₁ first-source first-middle-target first-target
      (κ′ ⁻¹) (middle ∙ κ)
      (PS.inverse-square pr₁ first-target first-middle-target κ′ FirstG.square)
      (PS.compose-square pr₁ first-source first-middle-source first-middle-target
        middle κ middle-parameter FirstF.square)

  module SecondF = Restriction.At 𝒯 M ℱ Γ f u
  module SecondG = Restriction.At 𝒯 M ℱ Γ g v
  diagram-frame : {I : CAT} (r : MAP I D) (x : Obj-abs I) →
    (pr₂ ∘ (productMap (id Γ) r ∘ insert x)) =₁ const (r ∘ x)
  diagram-frame r x = Restriction.At.second 𝒯 M ℱ Γ r x ∙
    ((pair-β₂ (id Γ ∘ pr₁) (r ∘ pr₂) ▷ insert x) ∙
      (comp-assoc (insert x) (productMap (id Γ) r) pr₂) ⁻¹)
  diagram-source = constant-corner ∙ diagram-frame f u
  diagram-target = diagram-frame g v
  diagram-middle-source = constant-corner ∙ pair-β₂ (id Γ) (const (f ∘ u))
  diagram-middle-target = pair-β₂ (id Γ) (const (g ∘ v))

  abstract
    incoming-diagram : PS.Square pr₂ diagram-source diagram-middle-source κ
    incoming-diagram = isoComp-cong (idIso constant-corner) SecondF.projection₂ ∙
      isoComp-assoc-at constant-corner (pair-β₂ (id Γ) (const (f ∘ u))) (pr₂ ◁ κ)

    middle-diagram : PS.Square pr₂ diagram-middle-source diagram-middle-target middle
    middle-diagram = pair-cong-triangle₂ (idIso (id Γ)) constant-corner

    diagram : PS.Square pr₂ diagram-source diagram-target comparison
    diagram = PS.compose-square pr₂ diagram-source diagram-middle-target diagram-target
      (κ′ ⁻¹) (middle ∙ κ)
      (PS.inverse-square pr₂ diagram-target diagram-middle-target κ′ SecondG.projection₂)
      (PS.compose-square pr₂ diagram-source diagram-middle-source diagram-middle-target
        middle κ middle-diagram incoming-diagram)

-- Specializing the shape to a rectangle identifies the parameter
-- projection with that of the actual five-factor currying corner.
module Rectangle (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B)
  (δ : (Coordinates.coinsert 𝒯 M ℱ u ∘ v) =₁ (insert v ∘ u)) where
  module Shape = At Γ (Coordinates.coinsert 𝒯 M ℱ u) (insert v) v u δ
  module Curried = Parameter.At 𝒯 M ℱ Γ A B u v

  abstract
    parameter-comparison : (pr₁ ◁ Curried.matching) =₂ (pr₁ ◁ Shape.comparison)
    parameter-comparison = cancel-left-reflect Shape.first-target
      (Shape.parameter ⁻¹ ∙ Curried.matching-parameter)
```


The rectangular vertex comparison itself is specified by the two pairing
comparisons to `(u, v)`. Its two projection equations are recorded before
inserting it into a parameterized family. Every application of terminal uniqueness compares functors or
identifications into `One`. The scalar restriction laws following
`constant-at-object` retain the associator and the chosen `const-pre`.

```agda
constant-at-object : {A B : CAT} (u : Obj-abs A) (v : Obj-abs B) →
  (const u ∘ v) =₁ u
constant-at-object {B = B} u v = comp-unitʳ u ∙
  ((u ◁ terminal-iso (terminate B ∘ v) (id One)) ∙ comp-assoc v (terminate B) u)

abstract
  constant-at-object-pre : {Γ A B : CAT} (u : Obj-abs A) (v : Obj-abs B) →
    (((constant-at-object u v) ▷ terminate Γ) ∙
      (comp-assoc (terminate Γ) v (const u)) ⁻¹) =₂ (const-pre u (const v))
  constant-at-object-pre {Γ} {A} {B} u v =
    let t = terminate Γ
        b = terminal-iso (terminate B ∘ v) (id One)
        tail = ((constant-at-object u v) ▷ t) ∙ (comp-assoc t v (const u)) ⁻¹
    in isoComp-cong
        (postWhisker u ◁ terminal-Iso₂
          (PS.compose-base (terminate B) v b t (comp-unitˡ t)) (terminal-iso _ _))
        (idIso (comp-assoc (const v) (terminate B) u)) ∙
      section-pre (terminate B) v b t u ∙ (isoComp-unitˡ-at tail) ⁻¹

  constant-pre-natural : {X Y A : CAT} (u : Obj-abs A)
    {f g : MAP X Y} (α : f =₁ g) →
    PS.Square (const u) (const-pre u f) (const-pre u g) α
  constant-pre-natural {X} {Y} u {f} {g} α =
    PS.lift-square u (terminate Y) (terminal-iso _ _) (terminal-iso _ _) α
      (terminal-Iso₂ _ _)

  constant-coordinate : {X Y Z A : CAT} (u : Obj-abs A)
    (p : MAP Y Z) (r : MAP X Y) {q : MAP X Z} (β : (p ∘ r) =₁ q) →
    (const-pre u q ∙ (const u ◁ β)) =₂
      PS.compose-base (const u) p (const-pre u p) r (const-pre u r)
  constant-coordinate u p r β = (const-pre-compose u r p) ⁻¹ ∙ constant-pre-natural u β

  identity-coordinate : {X Y Z : CAT} (p : MAP Y Z) (r : MAP X Y)
    {q : MAP X Z} (β : (p ∘ r) =₁ q) →
    (comp-unitˡ q ∙ (id Z ◁ β)) =₂ PS.compose-base (id Z) p (comp-unitˡ p) r β
  identity-coordinate {Z = Z} p r β = isoComp-cong (idIso β)
    (isoComp-cong (left-unitor-comp r p) (idIso ((comp-assoc r p (id Z)) ⁻¹)) ∙
      (cancel-right (comp-assoc r p (id Z)) (comp-unitˡ (p ∘ r))) ⁻¹) ∙
    postWhisker-id-at β

module Vertex {A B : CAT} (u : Obj-abs A) (v : Obj-abs B) where
  horizontal-axis : MAP B (A × B)
  horizontal-axis = Coordinates.coinsert 𝒯 M ℱ u
  vertical-axis : MAP A (A × B)
  vertical-axis = insert {X = A} v
  common = pair u v
  horizontal-first = constant-at-object u v
  horizontal-second = comp-unitˡ v
  vertical-first = comp-unitˡ u
  vertical-second = constant-at-object v u
  horizontal-frame : (horizontal-axis ∘ v) =₁ common
  horizontal-frame = pair-cong horizontal-first horizontal-second ∙ pair-pre (const u) (id B) v
  vertical-frame : (vertical-axis ∘ u) =₁ common
  vertical-frame = pair-cong vertical-first vertical-second ∙ pair-pre (id A) (const v) u

  corner : (horizontal-axis ∘ v) =₁ (vertical-axis ∘ u)
  corner = vertical-frame ⁻¹ ∙ horizontal-frame

  first-source = horizontal-first ∙
    ((pair-β₁ (const u) (id B) ▷ v) ∙ (comp-assoc v horizontal-axis pr₁) ⁻¹)
  first-target = vertical-first ∙
    ((pair-β₁ (id A) (const v) ▷ u) ∙ (comp-assoc u vertical-axis pr₁) ⁻¹)
  second-source = horizontal-second ∙
    ((pair-β₂ (const u) (id B) ▷ v) ∙ (comp-assoc v horizontal-axis pr₂) ⁻¹)
  second-target = vertical-second ∙
    ((pair-β₂ (id A) (const v) ▷ u) ∙ (comp-assoc u vertical-axis pr₂) ⁻¹)

  abstract
    first-projection : PS.Square pr₁ first-source first-target corner
    first-projection = PS.compose-square pr₁ first-source (pair-β₁ u v) first-target
      (vertical-frame ⁻¹) horizontal-frame
      (PS.inverse-square pr₁ first-target (pair-β₁ u v) vertical-frame
        (pair-pre-cong-triangle₁ (id A) (const v) u vertical-first vertical-second))
      (pair-pre-cong-triangle₁ (const u) (id B) v horizontal-first horizontal-second)

    second-projection : PS.Square pr₂ second-source second-target corner
    second-projection = PS.compose-square pr₂ second-source (pair-β₂ u v) second-target
      (vertical-frame ⁻¹) horizontal-frame
      (PS.inverse-square pr₂ second-target (pair-β₂ u v) vertical-frame
        (pair-pre-cong-triangle₂ (id A) (const v) u vertical-first vertical-second))
      (pair-pre-cong-triangle₂ (const u) (id B) v horizontal-first horizontal-second)

module CanonicalRectangle (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module ObjectCorner = Vertex u v
  open Rectangle Γ A B u v ObjectCorner.corner public
```


The two vertex frames extend over a parameter category. Their common
pairing comparison cancels against the image of the specified corner.
These are the frames to compare with the rectangle projection of currying.

```agda
module VertexFamily (Γ : CAT) {A B : CAT} (u : Obj-abs A) (v : Obj-abs B) where
  module V = Vertex u v
  t = terminate Γ
  pairing = pair-pre u v t
  source : const {P = Γ} (V.horizontal-axis ∘ v) =₁ pair (const u) (const v)
  source = pairing ∙ (V.horizontal-frame ▷ t)
  target : const {P = Γ} (V.vertical-axis ∘ u) =₁ pair (const u) (const v)
  target = pairing ∙ (V.vertical-frame ▷ t)

  abstract
    compatible : (target ∙ (V.corner ▷ t)) =₂ source
    compatible = isoComp-cong (idIso pairing)
      ((preWhisker t ◁ cancel-inverse V.vertical-frame V.horizontal-frame) ∙
        (preWhisker-isoComp-at V.vertical-frame V.corner t) ⁻¹) ∙
      isoComp-assoc-at pairing (V.vertical-frame ▷ t) (V.corner ▷ t)
```


The remaining coordinate comparison reduces to two explicit normalizations.
The theorem below consumes proofs of those normalizations; it does not
supply them. Once they are available, product reflection identifies the
currying matching with this particular inserted rectangular corner.

```agda
module CompareCurrying (Γ A B : CAT) (u : Obj-abs A) (v : Obj-abs B) where
  module R = CurriedCorner.At 𝒯 M ℱ Γ A B u v
  module K = CanonicalRectangle Γ A B u v
  module N = VertexFamily Γ u v

  SourceNormalization : Set m
  SourceNormalization = (N.source ∙ K.Shape.diagram-frame (Coordinates.coinsert 𝒯 M ℱ u) v) =₂ R.source
  TargetNormalization : Set m
  TargetNormalization = (N.target ∙ K.Shape.diagram-frame (insert v) u) =₂ R.target

  abstract
    diagram-square : SourceNormalization → TargetNormalization →
      PS.Square pr₂ R.source R.target K.Shape.comparison
    diagram-square source-normalization target-normalization = source-normalization ∙
      isoComp-cong N.compatible (idIso (K.Shape.diagram-frame (Coordinates.coinsert 𝒯 M ℱ u) v)) ∙
      (isoComp-assoc-at N.target K.Shape.constant-corner
        (K.Shape.diagram-frame (Coordinates.coinsert 𝒯 M ℱ u) v)) ⁻¹ ∙
      isoComp-cong (idIso N.target) K.Shape.diagram ∙
      isoComp-assoc-at N.target K.Shape.diagram-target (pr₂ ◁ K.Shape.comparison) ∙
      isoComp-cong (target-normalization ⁻¹) (idIso (pr₂ ◁ K.Shape.comparison))

    comparison : SourceNormalization → TargetNormalization →
      R.matching =₂ K.Shape.comparison
    comparison source-normalization target-normalization = pair-iso-extensionality
      K.parameter-comparison
      (cancel-left-reflect R.target
        ((diagram-square source-normalization target-normalization) ⁻¹ ∙ R.matching-rectangle))
```
