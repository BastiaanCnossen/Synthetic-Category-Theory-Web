# Identifications as a fiber of the diagonal

A cone to the diagonal and the point `(a,b)` is a common source of two
identifications: `v = a u` and `v = b u`. Composing the first with the
inverse of the second gives the fiber cone `b u = a u`.

We construct the diagonal cone in this orientation directly. Its normalized
coordinates are the identity and the universal identification. This is a
new derived choice of matching; literal agreement with the first rebuild's
inverse of a reversed paired matching is not asserted.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.RepresentabilityDiagonal where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp-unitˡ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section03.Identifications.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares
open import SCT.VolumeI.Chapter01.Section06.Representability

module _ {Γ : Context} where
  module Diagonal {E : CAT Γ} (a b : Obj-abs E) where
    private
      F : MAP One (E × E)
      F = pair a b

      Δ : MAP E (E × E)
      Δ = pair (id E) (id E)

      record CommonSource (T : CAT Γ) : Set m where
        open Terms.InContext T using (Term)
        field
          vertex : Term E
          parameter : Term One
          first : vertex =₁ (a ∘ parameter)
          second : vertex =₁ (b ∘ parameter)

      point₁ : {T : CAT Γ} (u : MAP T One) → (pr₁ ∘ (F ∘ u)) =₁ (a ∘ u)
      point₁ = project-pair₁ a b

      point₂ : {T : CAT Γ} (u : MAP T One) → (pr₂ ∘ (F ∘ u)) =₁ (b ∘ u)
      point₂ = project-pair₂ a b

      diagonal₁ : {T : CAT Γ} (v : MAP T E) → (pr₁ ∘ (Δ ∘ v)) =₁ v
      diagonal₁ v = comp-unitˡ v ∙ project-pair₁ (id E) (id E) v

      diagonal₂ : {T : CAT Γ} (v : MAP T E) → (pr₂ ∘ (Δ ∘ v)) =₁ v
      diagonal₂ v = comp-unitˡ v ∙ project-pair₂ (id E) (id E) v

      coordinates : {T : CAT Γ} → Cone Δ F T → CommonSource T
      coordinates s = record
        { vertex = Cone.left s
        ; parameter = Cone.right s
        ; first = point₁ (Cone.right s) ∙
            ((pr₁ ◁ Cone.match s) ∙ (diagonal₁ (Cone.left s)) ⁻¹)
        ; second = point₂ (Cone.right s) ∙
            ((pr₂ ◁ Cone.match s) ∙ (diagonal₂ (Cone.left s)) ⁻¹) }

      as-cone : {T : CAT Γ} → CommonSource T → Cone Δ F T
      as-cone d = record
        { left = vertex; right = parameter
        ; match = pair₌
            ((point₁ parameter) ⁻¹ ∙ (first ∙ diagonal₁ vertex))
            ((point₂ parameter) ⁻¹ ∙ (second ∙ diagonal₂ vertex)) }
        where open CommonSource d

      first-computation : {T : CAT Γ} (d : CommonSource T)
        → CommonSource.first (coordinates (as-cone d)) =₂ CommonSource.first d
      first-computation d = cancel-endpoint-changes (diagonal₁ vertex) (point₁ parameter) first ∙
        comp₌-cong (id₌ (point₁ parameter))
          (comp₌-cong (pair₌-β₁
            ((point₁ parameter) ⁻¹ ∙ (first ∙ diagonal₁ vertex))
            ((point₂ parameter) ⁻¹ ∙ (second ∙ diagonal₂ vertex)))
            (id₌ ((diagonal₁ vertex) ⁻¹)))
        where open CommonSource d

      second-computation : {T : CAT Γ} (d : CommonSource T)
        → CommonSource.second (coordinates (as-cone d)) =₂ CommonSource.second d
      second-computation d = cancel-endpoint-changes (diagonal₂ vertex) (point₂ parameter) second ∙
        comp₌-cong (id₌ (point₂ parameter))
          (comp₌-cong (pair₌-β₂
            ((point₁ parameter) ⁻¹ ∙ (first ∙ diagonal₁ vertex))
            ((point₂ parameter) ⁻¹ ∙ (second ∙ diagonal₂ vertex)))
            (id₌ ((diagonal₂ vertex) ⁻¹)))
        where open CommonSource d

      fiber : {T : CAT Γ} → CommonSource T → Cone b a T
      fiber d = record
        { left = parameter; right = parameter; match = first ∙ second ⁻¹ }
        where open CommonSource d
```

## Comparing the two descriptions

A comparison of common-source diagrams consists of two vertex identifications
and two commuting squares. Projection and product uniqueness convert between
this data and complete cone identifications. Eliminating the common source
pastes one square with the inverse of the other. In the reverse direction,
terminal uniqueness aligns the two parameter identifications; cancellation
then reconstructs the vertex identification and its two squares.

```agda

      record CommonSourceComparison {T : CAT Γ} (s t : CommonSource T) : Set m where
        field
          parameter : CommonSource.parameter s =₁ CommonSource.parameter t
          vertex : CommonSource.vertex s =₁ CommonSource.vertex t
          first : SquareCell₌ vertex (a ◁ parameter)
            (CommonSource.first s) (CommonSource.first t)
          second : SquareCell₌ vertex (b ◁ parameter)
            (CommonSource.second s) (CommonSource.second t)

      point₁-natural : {T : CAT Γ} {u u′ : MAP T One} (L : u =₁ u′)
        → SquareCell₌ (pr₁ ◁ (F ◁ L)) (a ◁ L) (point₁ u) (point₁ u′)
      point₁-natural L = restrict-change-square-One pr₁ F a (pair-β₁ a b) L

      point₂-natural : {T : CAT Γ} {u u′ : MAP T One} (L : u =₁ u′)
        → SquareCell₌ (pr₂ ◁ (F ◁ L)) (b ◁ L) (point₂ u) (point₂ u′)
      point₂-natural L = restrict-change-square-One pr₂ F b (pair-β₂ a b) L

      diagonal₁-natural : {T : CAT Γ} {v v′ : MAP T E} (R : v =₁ v′)
        → SquareCell₌ (pr₁ ◁ (Δ ◁ R)) R (diagonal₁ v) (diagonal₁ v′)
      diagonal₁-natural R = paste-square₌
        (restrict-change-square-One pr₁ Δ (id E) (pair-β₁ (id E) (id E)) R)
        (postWhisker-id-One R)

      diagonal₂-natural : {T : CAT Γ} {v v′ : MAP T E} (R : v =₁ v′)
        → SquareCell₌ (pr₂ ◁ (Δ ◁ R)) R (diagonal₂ v) (diagonal₂ v′)
      diagonal₂-natural R = paste-square₌
        (restrict-change-square-One pr₂ Δ (id E) (pair-β₂ (id E) (id E)) R)
        (postWhisker-id-One R)

      coordinates-identification : {T : CAT Γ} {s t : Cone Δ F T}
        → ConeIdentification₁ s t → CommonSourceComparison (coordinates s) (coordinates t)
      coordinates-identification {s = s} {t} Φ = record
        { parameter = R; vertex = L
        ; first = transport-square
            (diagonal₁ (Cone.left s)) (diagonal₁ (Cone.left t))
            (point₁ (Cone.right s)) (point₁ (Cone.right t))
            (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
            (pr₁ ◁ (Δ ◁ L)) (pr₁ ◁ (F ◁ R)) L (a ◁ R)
            (diagonal₁-natural L) (point₁-natural R) (post-square₌ pr₁ (ConeIdentification₁.compatible Φ))
        ; second = transport-square
            (diagonal₂ (Cone.left s)) (diagonal₂ (Cone.left t))
            (point₂ (Cone.right s)) (point₂ (Cone.right t))
            (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
            (pr₂ ◁ (Δ ◁ L)) (pr₂ ◁ (F ◁ R)) L (b ◁ R)
            (diagonal₂-natural L) (point₂-natural R) (post-square₌ pr₂ (ConeIdentification₁.compatible Φ)) }
        where
        L = ConeIdentification₁.left Φ
        R = ConeIdentification₁.right Φ

      coordinates-reflect : {T : CAT Γ} {s t : Cone Δ F T}
        → CommonSourceComparison (coordinates s) (coordinates t) → ConeIdentification₁ s t
      coordinates-reflect {s = s} {t} Φ = record
        { left = vertex; right = parameter
        ; compatible = pair₌-extensionality
            ((postWhisker-comp₌ pr₁ (F ◁ parameter) (Cone.match s)) ⁻¹ ∙
              (reflect-transported-square
                (diagonal₁ (Cone.left s)) (point₁ (Cone.right s))
                (diagonal₁ (Cone.left t)) (point₁ (Cone.right t))
                (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
                (pr₁ ◁ (Δ ◁ vertex)) (pr₁ ◁ (F ◁ parameter)) vertex (a ◁ parameter)
                (diagonal₁-natural vertex) (point₁-natural parameter) first ∙
                postWhisker-comp₌ pr₁ (Cone.match t) (Δ ◁ vertex)))
            ((postWhisker-comp₌ pr₂ (F ◁ parameter) (Cone.match s)) ⁻¹ ∙
              (reflect-transported-square
                (diagonal₂ (Cone.left s)) (point₂ (Cone.right s))
                (diagonal₂ (Cone.left t)) (point₂ (Cone.right t))
                (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
                (pr₂ ◁ (Δ ◁ vertex)) (pr₂ ◁ (F ◁ parameter)) vertex (b ◁ parameter)
                (diagonal₂-natural vertex) (point₂-natural parameter) second ∙
                postWhisker-comp₌ pr₂ (Cone.match t) (Δ ◁ vertex))) }
        where open CommonSourceComparison Φ

      fiber-identification : {T : CAT Γ} {s t : CommonSource T}
        → CommonSourceComparison s t → ConeIdentification₁ (fiber s) (fiber t)
      fiber-identification Φ = record
        { left = parameter; right = parameter
        ; compatible = paste-square₌ (inverse-square₌ second) first }
        where open CommonSourceComparison Φ

      fiber-reflect : {T : CAT Γ} {s t : CommonSource T}
        → ConeIdentification₁ (fiber s) (fiber t) → CommonSourceComparison s t
      fiber-reflect {s = s} {t} Φ = record
        { parameter = L; vertex = R; first = first-square; second = second-square }
        where
        open CommonSource
        L = ConeIdentification₁.right Φ
        R = (first t) ⁻¹ ∙ ((a ◁ L) ∙ first s)
        aligned : SquareCell₌ (b ◁ L) (a ◁ L)
          (first s ∙ (second s) ⁻¹) (first t ∙ (second t) ⁻¹)
        aligned = replace-edges₌
          (postWhisker b ◁ terminal-unique₂ (ConeIdentification₁.left Φ) L)
          (id₌ (a ◁ L)) (ConeIdentification₁.compatible Φ)
        first-square : SquareCell₌ R (a ◁ L) (first s) (first t)
        first-square = comp-inv-left (first t) ((a ◁ L) ∙ first s)
        second-square : SquareCell₌ R (b ◁ L) (second s) (second t)
        second-square = replace-sides₌ (inverse-inverse (second s)) (inverse-inverse (second t))
          (inverse-square₌
            (replace-sides₌ (inv-comp-left (first s) ((second s) ⁻¹))
              (inv-comp-left (first t) ((second t) ⁻¹))
              (paste-square₌ aligned (inverse-square₌ first-square))))

```

## Restriction of the coordinates

Each normalized projection commutes with restriction. The proof restricts
its triangle, changes the endpoints by the actual cone associators, and
uses the existing normalization laws for product projections. Compatibility
with composition and inversion then gives the full restricted fiber matching.
No uniqueness of higher compatibility witnesses is assumed.

```agda
      module CoordinateRestriction {S T : CAT Γ}
        (π : MAP (E × E) E) (c : Obj-abs E)
        (point-law : (π ∘ F) =₁ c) (diagonal-law : (π ∘ Δ) =₁ id E)
        (s : Cone Δ F T) (r : MAP S T) where
        point : {X : CAT Γ} (u : MAP X One) → (π ∘ (F ∘ u)) =₁ (c ∘ u)
        point = restrict-triangle π F point-law
        diagonal : {X : CAT Γ} (v : MAP X E) → (π ∘ (Δ ∘ v)) =₁ v
        diagonal v = comp-unitˡ v ∙ restrict-triangle π Δ diagonal-law v
        edge : {X : CAT Γ} (q : Cone Δ F X)
          → Cone.left q =₁ (c ∘ Cone.right q)
        edge q = changeEndpoints (diagonal (Cone.left q)) (point (Cone.right q)) (π ◁ Cone.match q)

        v = Cone.left s
        u = Cone.right s
        A = comp-assoc r v Δ
        B = comp-assoc r u F
        C = comp-assoc r u c
        restricted = cone-restrict r s
        L = diagonal (v ∘ r)
        R = point (u ∘ r)
        q = π ◁ Cone.match restricted
        e = edge s ▷ r

        comparison : edge restricted =₂ (C ∙ e)
        comparison = square-to-changeEndpoints L R q (C ∙ e)
          ((comp₌-assoc C e L) ⁻¹ ∙
            (comp₌-cong (id₌ C) extended ∙
              (comp₌-assoc C (C ⁻¹ ∙ R) q ∙
                comp₌-cong ((comp-inv-left C R) ⁻¹) (id₌ q))))
          where
          original : SquareCell₌ (π ◁ (Cone.match s ▷ r)) e
            (restrict-triangle π (Δ ∘ v) (diagonal v) r)
            (restrict-triangle π (F ∘ u) (point u) r)
          original = restrict-square-One π (Cone.match s) (edge s)
            (diagonal v) (point u) r
            (changeEndpoints-to-square (diagonal v) (point u) (π ◁ Cone.match s) (edge s) (id₌ (edge s)))
          extended : SquareCell₌ q e L (C ⁻¹ ∙ R)
          extended = replace-sides₌
            (identity-normalization-pre π Δ diagonal-law v r)
            (simple-normalization-pre π F c point-law u r)
            (replace-edges₌ ((postWhisker-changeEndpoints π A B (Cone.match s ▷ r)) ⁻¹) (id₌ e)
              (changeEndpoints-extend-square (π ◁ A) (π ◁ B) (π ◁ (Cone.match s ▷ r)) original))

      convert : {T : CAT Γ} → Cone Δ F T → Cone b a T
      convert s = fiber (coordinates s)

      convert-identification : {T : CAT Γ} {s t : Cone Δ F T}
        → ConeIdentification₁ s t → ConeIdentification₁ (convert s) (convert t)
      convert-identification Φ = fiber-identification (coordinates-identification Φ)

      convert-reflect : {T : CAT Γ} {s t : Cone Δ F T}
        → ConeIdentification₁ (convert s) (convert t) → ConeIdentification₁ s t
      convert-reflect Φ = coordinates-reflect (fiber-reflect Φ)

      convert-restrict : {S T : CAT Γ} (s : Cone Δ F T) (r : MAP S T)
        → ConeIdentification₁ (convert (cone-restrict r s)) (cone-restrict r (convert s))
      convert-restrict s r = cone-retarget-match-identification
        (convert (cone-restrict r s)) (Cone.match (cone-restrict r (convert s))) matching
        where
        open CommonSource (coordinates s) renaming (first to ξ; second to η)
        A = comp-assoc r parameter a
        B = comp-assoc r parameter b
        x = ξ ▷ r
        y = η ▷ r
        first = CoordinateRestriction.comparison pr₁ a (pair-β₁ a b) (pair-β₁ (id E) (id E)) s r
        second = CoordinateRestriction.comparison pr₂ b (pair-β₂ a b) (pair-β₂ (id E) (id E)) s r
        restricted-matching : ((ξ ∙ η ⁻¹) ▷ r) =₂ (x ∙ y ⁻¹)
        restricted-matching = comp₌-cong (id₌ x) (preWhisker-inverse η r) ∙
          preWhisker-comp₌ ξ (η ⁻¹) r
        matching : Cone.match (convert (cone-restrict r s)) =₂ Cone.match (cone-restrict r (convert s))
        matching = comp₌-cong (id₌ A) (comp₌-cong (restricted-matching ⁻¹) (id₌ (B ⁻¹))) ∙
          (comp₌-cong (id₌ A) ((comp₌-assoc x (y ⁻¹) (B ⁻¹)) ⁻¹) ∙
            (comp₌-assoc A x (y ⁻¹ ∙ B ⁻¹) ∙
              (comp₌-cong (id₌ (A ∙ x)) (inverse-composite B y) ∙
                comp₌-cong first (inv₌ ◁ second))))

```

## The universal diagonal cone

The common source is the constant object a. Its two edges are the identity
and the universal identification from representability. Projection of the
actual paired matching computes these exact normalized coordinates.

```agda
      universal : CommonSource (a ＝ b)
      universal = record
        { vertex = const a; parameter = terminate (a ＝ b)
        ; first = id₌ (const a); second = identification a b }

    diagonal-cone : Cone (pair (id E) (id E)) (pair a b) (a ＝ b)
    diagonal-cone = as-cone universal

    diagonal-first :
      (point₁ (Cone.right diagonal-cone) ∙
        ((pr₁ ◁ Cone.match diagonal-cone) ∙ (diagonal₁ (Cone.left diagonal-cone)) ⁻¹))
      =₂ id₌ (const a)
    diagonal-first = first-computation universal

    diagonal-second :
      (point₂ (Cone.right diagonal-cone) ∙
        ((pr₂ ◁ Cone.match diagonal-cone) ∙ (diagonal₂ (Cone.left diagonal-cone)) ⁻¹))
      =₂ identification a b
    diagonal-second = second-computation universal

    private
      recovered-matching : Cone.match (fiber (coordinates diagonal-cone))
        =₂ (identification a b) ⁻¹
      recovered-matching = comp₌-unitˡ-One ((identification a b) ⁻¹) ∙
        comp₌-cong diagonal-first (inv₌ ◁ diagonal-second)

      fiber-isPullback : IsPullback (fiber (coordinates diagonal-cone))
      fiber-isPullback = isPullback-cone-identification
        (cone-inverse (cone-retarget-match-identification
          (fiber (coordinates diagonal-cone)) ((identification a b) ⁻¹) recovered-matching))
        (identification-isPullback a b)

```

The converted fiber cone has matching identified with the inverse universal
identification, so the representability axiom makes it a pullback. Its factor
and complete beta transfer back through the coordinate description. Reflection
transfers in the same way. This construction works for arbitrary test
categories, so recognition needs no anima hypothesis on E or on the diagonal
pullback.

```agda
      module Fiber = UniversalCone (convert diagonal-cone) fiber-isPullback

      factor : {T : CAT Γ} → Cone Δ F T → MAP T (a ＝ b)
      factor s = Fiber.factor (convert s)

      factor-law : {T : CAT Γ} (s : Cone Δ F T)
        → ConeIdentification₁ (cone-restrict (factor s) diagonal-cone) s
      factor-law s = convert-reflect
        (cone-compose (Fiber.β (convert s)) (convert-restrict diagonal-cone (factor s)))

      reflect : {T : CAT Γ} (h k : MAP T (a ＝ b))
        → ConeIdentification₁ (cone-restrict h diagonal-cone) (cone-restrict k diagonal-cone)
        → h =₁ k
      reflect h k Φ = Fiber.reflect h k
        (cone-compose (convert-restrict diagonal-cone k)
          (cone-compose (convert-identification Φ) (cone-inverse (convert-restrict diagonal-cone h))))

    diagonal-isPullback : IsPullback diagonal-cone
    diagonal-isPullback = pullback-recognize diagonal-cone factor factor-law reflect
```
