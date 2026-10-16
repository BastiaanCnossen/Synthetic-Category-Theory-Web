# Pullbacks as base changes of the diagonal

A cone to the product functor and the diagonal has two identifications
with a common target. Eliminating that target recovers the original cone.
Product uniqueness reconstructs the product-source identification from
the two recovered legs. The complete comparison retains both coordinate
squares and their normalized matching boundaries.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section06.DiagonalPullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp-assoc; comp-unitˡ; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Products
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-comp-One; postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (id-isEquiv; equiv-transport; equiv-compose; equiv-cancel-left)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares

module _ {Γ : Context} where
  module DiagonalPullback {C D E : CAT Γ} (f : MAP C E) (g : MAP D E) where
    F : MAP (C × D) (E × E)
    F = productMap f g

    Δ : MAP E (E × E)
    Δ = pair (id E) (id E)

    private
      record CommonTarget (T : CAT Γ) : Set m where
        open Terms.InContext T using (Term)
        field
          parameter : Term (C × D)
          vertex : Term E
          first : (f ∘ (pr₁ ∘ parameter)) =₁ vertex
          second : (g ∘ (pr₂ ∘ parameter)) =₁ vertex

      left₁ : {T : CAT Γ} (u : MAP T (C × D)) → (pr₁ ∘ (F ∘ u)) =₁ (f ∘ (pr₁ ∘ u))
      left₁ u = comp-assoc u pr₁ f ∙ project-pair₁ (f ∘ pr₁) (g ∘ pr₂) u

      left₂ : {T : CAT Γ} (u : MAP T (C × D)) → (pr₂ ∘ (F ∘ u)) =₁ (g ∘ (pr₂ ∘ u))
      left₂ u = comp-assoc u pr₂ g ∙ project-pair₂ (f ∘ pr₁) (g ∘ pr₂) u

      right₁ : {T : CAT Γ} (v : MAP T E) → (pr₁ ∘ (Δ ∘ v)) =₁ v
      right₁ v = comp-unitˡ v ∙ project-pair₁ (id E) (id E) v

      right₂ : {T : CAT Γ} (v : MAP T E) → (pr₂ ∘ (Δ ∘ v)) =₁ v
      right₂ v = comp-unitˡ v ∙ project-pair₂ (id E) (id E) v

      coordinates : {T : CAT Γ} → Cone F Δ T → CommonTarget T
      coordinates s = record
        { parameter = Cone.left s; vertex = Cone.right s
        ; first = changeEndpoints (left₁ (Cone.left s)) (right₁ (Cone.right s)) (pr₁ ◁ Cone.match s)
        ; second = changeEndpoints (left₂ (Cone.left s)) (right₂ (Cone.right s)) (pr₂ ◁ Cone.match s) }

      as-cone : {T : CAT Γ} → CommonTarget T → Cone F Δ T
      as-cone d = record
        { left = parameter; right = vertex
        ; match = pair₌
            ((right₁ vertex) ⁻¹ ∙ (first ∙ left₁ parameter))
            ((right₂ vertex) ⁻¹ ∙ (second ∙ left₂ parameter)) }
        where open CommonTarget d

      first-computation : {T : CAT Γ} (d : CommonTarget T)
        → CommonTarget.first (coordinates (as-cone d)) =₂ CommonTarget.first d
      first-computation d = cancel-endpoint-changes (left₁ parameter) (right₁ vertex) first ∙
        comp₌-cong (id₌ (right₁ vertex))
          (comp₌-cong (pair₌-β₁
            ((right₁ vertex) ⁻¹ ∙ (first ∙ left₁ parameter))
            ((right₂ vertex) ⁻¹ ∙ (second ∙ left₂ parameter)))
            (id₌ ((left₁ parameter) ⁻¹)))
        where open CommonTarget d

      second-computation : {T : CAT Γ} (d : CommonTarget T)
        → CommonTarget.second (coordinates (as-cone d)) =₂ CommonTarget.second d
      second-computation d = cancel-endpoint-changes (left₂ parameter) (right₂ vertex) second ∙
        comp₌-cong (id₌ (right₂ vertex))
          (comp₌-cong (pair₌-β₂
            ((right₁ vertex) ⁻¹ ∙ (first ∙ left₁ parameter))
            ((right₂ vertex) ⁻¹ ∙ (second ∙ left₂ parameter)))
            (id₌ ((left₂ parameter) ⁻¹)))
        where open CommonTarget d

      recover : {T : CAT Γ} → CommonTarget T → Cone f g T
      recover d = record
        { left = pr₁ ∘ parameter; right = pr₂ ∘ parameter; match = second ⁻¹ ∙ first }
        where open CommonTarget d

      recoverCone : {T : CAT Γ} → Cone F Δ T → Cone f g T
      recoverCone s = recover (coordinates s)
```

## Comparing the coordinate descriptions

Two commuting squares preserve the quotient matching. Conversely, the two
legs of a recovered cone comparison determine the product-source comparison.
The second coordinate determines the common-target comparison by cancellation;
pasting then gives the first coordinate square.

```agda
      record CommonTargetComparison {T : CAT Γ} (s t : CommonTarget T) : Set m where
        field
          parameter : CommonTarget.parameter s =₁ CommonTarget.parameter t
          vertex : CommonTarget.vertex s =₁ CommonTarget.vertex t
          first : SquareCell₌ (f ◁ (pr₁ ◁ parameter)) vertex
            (CommonTarget.first s) (CommonTarget.first t)
          second : SquareCell₌ (g ◁ (pr₂ ◁ parameter)) vertex
            (CommonTarget.second s) (CommonTarget.second t)

      left₁-natural : {T : CAT Γ} {u u′ : MAP T (C × D)} (L : u =₁ u′)
        → SquareCell₌ (pr₁ ◁ (F ◁ L)) (f ◁ (pr₁ ◁ L)) (left₁ u) (left₁ u′)
      left₁-natural L = paste-square₌
        (restrict-change-square-One pr₁ F (f ∘ pr₁) (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) L)
        (postWhisker-comp-One L pr₁ f)

      left₂-natural : {T : CAT Γ} {u u′ : MAP T (C × D)} (L : u =₁ u′)
        → SquareCell₌ (pr₂ ◁ (F ◁ L)) (g ◁ (pr₂ ◁ L)) (left₂ u) (left₂ u′)
      left₂-natural L = paste-square₌
        (restrict-change-square-One pr₂ F (g ∘ pr₂) (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) L)
        (postWhisker-comp-One L pr₂ g)

      right₁-natural : {T : CAT Γ} {v v′ : MAP T E} (R : v =₁ v′)
        → SquareCell₌ (pr₁ ◁ (Δ ◁ R)) R (right₁ v) (right₁ v′)
      right₁-natural R = paste-square₌
        (restrict-change-square-One pr₁ Δ (id E) (pair-β₁ (id E) (id E)) R)
        (postWhisker-id-One R)

      right₂-natural : {T : CAT Γ} {v v′ : MAP T E} (R : v =₁ v′)
        → SquareCell₌ (pr₂ ◁ (Δ ◁ R)) R (right₂ v) (right₂ v′)
      right₂-natural R = paste-square₌
        (restrict-change-square-One pr₂ Δ (id E) (pair-β₂ (id E) (id E)) R)
        (postWhisker-id-One R)

      coordinates-identification : {T : CAT Γ} {s t : Cone F Δ T}
        → ConeIdentification₁ s t → CommonTargetComparison (coordinates s) (coordinates t)
      coordinates-identification {s = s} {t} Φ = record
        { parameter = L; vertex = R
        ; first = transport-square
            (left₁ (Cone.left s)) (left₁ (Cone.left t))
            (right₁ (Cone.right s)) (right₁ (Cone.right t))
            (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
            (pr₁ ◁ (F ◁ L)) (pr₁ ◁ (Δ ◁ R)) (f ◁ (pr₁ ◁ L)) R
            (left₁-natural L) (right₁-natural R) (post-square₌ pr₁ (ConeIdentification₁.compatible Φ))
        ; second = transport-square
            (left₂ (Cone.left s)) (left₂ (Cone.left t))
            (right₂ (Cone.right s)) (right₂ (Cone.right t))
            (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
            (pr₂ ◁ (F ◁ L)) (pr₂ ◁ (Δ ◁ R)) (g ◁ (pr₂ ◁ L)) R
            (left₂-natural L) (right₂-natural R) (post-square₌ pr₂ (ConeIdentification₁.compatible Φ)) }
        where
        L = ConeIdentification₁.left Φ
        R = ConeIdentification₁.right Φ

      coordinates-reflect : {T : CAT Γ} {s t : Cone F Δ T}
        → CommonTargetComparison (coordinates s) (coordinates t) → ConeIdentification₁ s t
      coordinates-reflect {s = s} {t} Φ = record
        { left = parameter; right = vertex
        ; compatible = pair₌-extensionality
            ((postWhisker-comp₌ pr₁ (Δ ◁ vertex) (Cone.match s)) ⁻¹ ∙
              (reflect-transported-square
                (left₁ (Cone.left s)) (right₁ (Cone.right s))
                (left₁ (Cone.left t)) (right₁ (Cone.right t))
                (pr₁ ◁ Cone.match s) (pr₁ ◁ Cone.match t)
                (pr₁ ◁ (F ◁ parameter)) (pr₁ ◁ (Δ ◁ vertex)) (f ◁ (pr₁ ◁ parameter)) vertex
                (left₁-natural parameter) (right₁-natural vertex) first ∙
                postWhisker-comp₌ pr₁ (Cone.match t) (F ◁ parameter)))
            ((postWhisker-comp₌ pr₂ (Δ ◁ vertex) (Cone.match s)) ⁻¹ ∙
              (reflect-transported-square
                (left₂ (Cone.left s)) (right₂ (Cone.right s))
                (left₂ (Cone.left t)) (right₂ (Cone.right t))
                (pr₂ ◁ Cone.match s) (pr₂ ◁ Cone.match t)
                (pr₂ ◁ (F ◁ parameter)) (pr₂ ◁ (Δ ◁ vertex)) (g ◁ (pr₂ ◁ parameter)) vertex
                (left₂-natural parameter) (right₂-natural vertex) second ∙
                postWhisker-comp₌ pr₂ (Cone.match t) (F ◁ parameter))) }
        where open CommonTargetComparison Φ

      recover-identification : {T : CAT Γ} {s t : CommonTarget T}
        → CommonTargetComparison s t → ConeIdentification₁ (recover s) (recover t)
      recover-identification Φ = record
        { left = pr₁ ◁ parameter; right = pr₂ ◁ parameter
        ; compatible = paste-square₌ first (inverse-square₌ second) }
        where open CommonTargetComparison Φ

      recover-reflect : {T : CAT Γ} {s t : CommonTarget T}
        → ConeIdentification₁ (recover s) (recover t) → CommonTargetComparison s t
      recover-reflect {s = s} {t} Φ = record
        { parameter = L; vertex = R
        ; first = replace-edges₌ ((postWhisker f ◁ pair₌-β₁ l r) ⁻¹) (id₌ R) first-square
        ; second = replace-edges₌ ((postWhisker g ◁ pair₌-β₂ l r) ⁻¹) (id₌ R) second-square }
        where
        l : (pr₁ ∘ CommonTarget.parameter s) =₁ (pr₁ ∘ CommonTarget.parameter t)
        l = ConeIdentification₁.left Φ
        r : (pr₂ ∘ CommonTarget.parameter s) =₁ (pr₂ ∘ CommonTarget.parameter t)
        r = ConeIdentification₁.right Φ
        L : CommonTarget.parameter s =₁ CommonTarget.parameter t
        L = pair₌ l r
        R : CommonTarget.vertex s =₁ CommonTarget.vertex t
        R = (CommonTarget.second t ∙ (g ◁ r)) ∙ (CommonTarget.second s) ⁻¹
        second-square : SquareCell₌ (g ◁ r) R (CommonTarget.second s) (CommonTarget.second t)
        second-square = (inv-comp-right (CommonTarget.second t ∙ (g ◁ r)) (CommonTarget.second s)) ⁻¹
        first-square : SquareCell₌ (f ◁ l) R (CommonTarget.first s) (CommonTarget.first t)
        first-square = replace-sides₌
          (comp-inv-left (CommonTarget.second s) (CommonTarget.first s))
          (comp-inv-left (CommonTarget.second t) (CommonTarget.first t))
          (paste-square₌ (ConeIdentification₁.compatible Φ) second-square)

      recoverCone-identification : {T : CAT Γ} {s t : Cone F Δ T}
        → ConeIdentification₁ s t → ConeIdentification₁ (recoverCone s) (recoverCone t)
      recoverCone-identification Φ = recover-identification (coordinates-identification Φ)

      recoverCone-reflect : {T : CAT Γ} {s t : Cone F Δ T}
        → ConeIdentification₁ (recoverCone s) (recoverCone t) → ConeIdentification₁ s t
      recoverCone-reflect Φ = coordinates-reflect (recover-reflect Φ)
```

## The direct cone

The product-source leg pairs the original legs; the common target is the
second composite. Pairing the original matching with the identity, with
the two actual projection normalizations, gives the specified matching.
Its coordinate computations recover the whole original cone.

```agda
      module Direct {T : CAT Γ} (s : Cone f g T) where
        p : MAP T C
        p = Cone.left s
        q : MAP T D
        q = Cone.right s
        τ : (f ∘ p) =₁ (g ∘ q)
        τ = Cone.match s
        diagram : CommonTarget T
        diagram = record
          { parameter = pair p q; vertex = g ∘ q
          ; first = τ ∙ (f ◁ pair-β₁ p q); second = g ◁ pair-β₂ p q }
        value : Cone F Δ T
        value = as-cone diagram
        recover-law : ConeIdentification₁ (recoverCone value) s
        recover-law = record
          { left = pair-β₁ p q; right = pair-β₂ p q
          ; compatible = (first-computation diagram ∙
              (comp-inv-left (CommonTarget.second (coordinates value)) (CommonTarget.first (coordinates value)) ∙
                comp₌-cong ((second-computation diagram) ⁻¹)
                  (id₌ (Cone.match (recoverCone value))))) ⁻¹ }
```

## Restriction of the recovered matching

Restrict each normalized coordinate along its actual associator boundary.
Pasting the two squares gives the quotient square; changing its endpoints
then recovers the full restricted matching. The product-source leg
comparisons are the inverse projection associators.

```agda
      module CoordinateRestriction {S T A : CAT Γ}
        (π : MAP (E × E) E) (j : MAP (C × D) A) (a : MAP A E)
        (projection-law : (π ∘ F) =₁ (a ∘ j)) (diagonal-law : (π ∘ Δ) =₁ id E)
        (s : Cone F Δ T) (r : MAP S T) where
        u : MAP T (C × D)
        u = Cone.left s
        v : MAP T E
        v = Cone.right s
        left : {X : CAT Γ} (x : MAP X (C × D)) → (π ∘ (F ∘ x)) =₁ (a ∘ (j ∘ x))
        left x = comp-assoc x j a ∙ restrict-triangle π F projection-law x
        right : {X : CAT Γ} (y : MAP X E) → (π ∘ (Δ ∘ y)) =₁ y
        right y = comp-unitˡ y ∙ restrict-triangle π Δ diagonal-law y
        edge : {X : CAT Γ} (t : Cone F Δ X) → (a ∘ (j ∘ Cone.left t)) =₁ Cone.right t
        edge t = changeEndpoints (left (Cone.left t)) (right (Cone.right t)) (π ◁ Cone.match t)
        boundary : (a ∘ (j ∘ (u ∘ r))) =₁ ((a ∘ (j ∘ u)) ∘ r)
        boundary = (comp-assoc r (j ∘ u) a) ⁻¹ ∙ (a ◁ (comp-assoc r u j) ⁻¹)
        comparison : edge (cone-restrict r s) =₂ ((edge s ▷ r) ∙ boundary)
        comparison = square-to-changeEndpoints (left (u ∘ r)) (right (v ∘ r))
          (π ◁ Cone.match (cone-restrict r s)) ((edge s ▷ r) ∙ boundary)
          ((comp₌-assoc (edge s ▷ r) boundary (left (u ∘ r))) ⁻¹ ∙ extended)
          where
          original : SquareCell₌ (π ◁ (Cone.match s ▷ r)) (edge s ▷ r)
            (restrict-triangle π (F ∘ u) (left u) r)
            (restrict-triangle π (Δ ∘ v) (right v) r)
          original = restrict-square-One π (Cone.match s) (edge s) (left u) (right v) r
            (changeEndpoints-to-square (left u) (right v) (π ◁ Cone.match s) (edge s) (id₌ (edge s)))
          extended : SquareCell₌ (π ◁ Cone.match (cone-restrict r s)) (edge s ▷ r)
            (boundary ∙ left (u ∘ r)) (right (v ∘ r))
          extended = replace-sides₌
            (composite-normalization-pre π F j a projection-law u r)
            (identity-normalization-pre π Δ diagonal-law v r)
            (replace-edges₌
              ((postWhisker-changeEndpoints π (comp-assoc r u F) (comp-assoc r v Δ) (Cone.match s ▷ r)) ⁻¹)
              (id₌ (edge s ▷ r))
              (changeEndpoints-extend-square (π ◁ comp-assoc r u F) (π ◁ comp-assoc r v Δ)
                (π ◁ (Cone.match s ▷ r)) original))

      recover-pre : {S T : CAT Γ} (r : MAP S T) (s : Cone F Δ T)
        → ConeIdentification₁ (recoverCone (cone-restrict r s)) (cone-restrict r (recoverCone s))
      recover-pre r s = record
        { left = l; right = q
        ; compatible = replace-sides₌ (id₌ restricted-matching)
            (comp₌-cong (id₌ B) (comp₌-cong (matching-pre ⁻¹) (id₌ (A ⁻¹)))) normalized }
        where
        u = Cone.left s
        v = Cone.right s
        l : (pr₁ ∘ (u ∘ r)) =₁ ((pr₁ ∘ u) ∘ r)
        l = (comp-assoc r u pr₁) ⁻¹
        q : (pr₂ ∘ (u ∘ r)) =₁ ((pr₂ ∘ u) ∘ r)
        q = (comp-assoc r u pr₂) ⁻¹
        A = comp-assoc r (pr₁ ∘ u) f
        B = comp-assoc r (pr₂ ∘ u) g
        α = CommonTarget.first (coordinates s) ▷ r
        β = CommonTarget.second (coordinates s) ▷ r
        α′ = CommonTarget.first (coordinates (cone-restrict r s))
        β′ = CommonTarget.second (coordinates (cone-restrict r s))
        restricted-matching = β′ ⁻¹ ∙ α′
        first : SquareCell₌ (A ⁻¹ ∙ (f ◁ l)) (id₌ (v ∘ r)) α′ α
        first = (CoordinateRestriction.comparison pr₁ pr₁ f
          (pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) (pair-β₁ (id E) (id E)) s r ∙ comp₌-unitˡ-One α′) ⁻¹
        second : SquareCell₌ (B ⁻¹ ∙ (g ◁ q)) (id₌ (v ∘ r)) β′ β
        second = (CoordinateRestriction.comparison pr₂ pr₂ g
          (pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) (pair-β₂ (id E) (id E)) s r ∙ comp₌-unitˡ-One β′) ⁻¹
        matching-pre : (Cone.match (recoverCone s) ▷ r) =₂ (β ⁻¹ ∙ α)
        matching-pre = comp₌-cong (preWhisker-inverse (CommonTarget.second (coordinates s)) r) (id₌ α) ∙
          preWhisker-comp₌ ((CommonTarget.second (coordinates s)) ⁻¹) (CommonTarget.first (coordinates s)) r
        normalized : SquareCell₌ (f ◁ l) (g ◁ q) restricted-matching (changeEndpoints A B (β ⁻¹ ∙ α))
        normalized = normalize-transported-square A B (β ⁻¹ ∙ α) restricted-matching (f ◁ l) (g ◁ q)
          (paste-square₌ first (inverse-square₌ second))

      recover-direct-pre : {S T : CAT Γ} (r : MAP S T) (s : Cone f g T)
        → ConeIdentification₁ (recoverCone (cone-restrict r (Direct.value s))) (cone-restrict r s)
      recover-direct-pre r s = cone-compose
        (cone-identification-restrict-One r (Direct.recover-law s)) (recover-pre r (Direct.value s))
```

## Universality and the specified equivalence

The inverse comparison factors the recovered chosen target through the
source universal cone. Recovery reflects its complete beta, and it
transfers endomorphism reflection in the same way. Recognition gives the
diagonal pullback property for every original universal cone.

```agda
    source : Cone f g (Pullback f g)
    source = pullback-cone f g

    target : Cone F Δ (Pullback F Δ)
    target = pullback-cone F Δ

    module Universal {T : CAT Γ} (s : Cone f g T) (es : IsPullback s) where
      private
        module Original = UniversalCone s es
      direct : Cone F Δ T
      direct = Direct.value s
      inverse : MAP (Pullback F Δ) T
      inverse = Original.factor (recoverCone target)
      factor-cone-law : ConeIdentification₁ (cone-restrict inverse direct) target
      factor-cone-law = recoverCone-reflect
        (cone-compose (Original.β (recoverCone target)) (recover-direct-pre inverse s))
      reflect-identifications : (h k : MAP T T)
        → ConeIdentification₁ (cone-restrict h direct) (cone-restrict k direct) → h =₁ k
      reflect-identifications h k Φ = Original.reflect h k
        (cone-compose (recover-direct-pre k s)
          (cone-compose (recoverCone-identification Φ) (cone-inverse (recover-direct-pre h s))))
      isPullback : IsPullback direct
      isPullback = isPullback-from-factor-and-reflection direct inverse factor-cone-law reflect-identifications

    private
      source-isPullback : IsPullback source
      source-isPullback = equiv-transport
        (pullback-reflect (id (Pullback f g)) (pullback-factor source)
          (cone-compose (cone-inverse (pullback-factor-β source)) (cone-restrict-id source)))
        (id-isEquiv (Pullback f g))

    forward : MAP (Pullback f g) (Pullback F Δ)
    forward = pullback-factor (Direct.value source)
    forward-isEquiv : IsEquiv forward
    forward-isEquiv = Universal.isPullback source source-isPullback
    forward-left : (pullback₁ ∘ forward) =₁ pair (pullback₁ {f = f} {g}) pullback₂
    forward-left = pullback-factor-β₁ (Direct.value source)
    forward-right : (pullback₂ ∘ forward) =₁ (g ∘ pullback₂ {f = f} {g})
    forward-right = pullback-factor-β₂ (Direct.value source)
```

## Arbitrary squares and their transported matching

The induced cone is identified with the actual direct value. Changing its
legs retains the full matching equation. Reflection of that complete cone
law compares their factors, proving preservation and reflection of the
pullback property in the original directions.

```agda
    module Square {T : CAT Γ} (s : Cone f g T) where
      value : Cone F Δ T
      value = Direct.value s
      left : MAP T (C × D)
      left = Cone.left value
      right : MAP T E
      right = Cone.right value
      induced : MAP T (Pullback F Δ)
      induced = forward ∘ pullback-factor s
      original : Cone F Δ T
      original = cone-restrict induced target
      source-cone-law : ConeIdentification₁ (cone-restrict (pullback-factor s) (Direct.value source)) value
      source-cone-law = recoverCone-reflect
        (cone-compose (cone-inverse (Direct.recover-law s))
          (cone-compose (pullback-factor-β s) (recover-direct-pre (pullback-factor s) source)))
      cone-law : ConeIdentification₁ original value
      cone-law = cone-compose source-cone-law
        (cone-compose (cone-identification-restrict-One (pullback-factor s) (pullback-factor-β (Direct.value source)))
          (cone-inverse (cone-restrict-assoc (pullback-factor s) forward target)))
      left-law : Cone.left original =₁ left
      left-law = ConeIdentification₁.left cone-law
      right-law : Cone.right original =₁ right
      right-law = ConeIdentification₁.right cone-law
      transported : Cone F Δ T
      transported = record
        { left = left; right = right
        ; match = changeEndpoints (F ◁ left-law) (Δ ◁ right-law) (Cone.match original) }
      matching-law : Cone.match transported =₂ Cone.match value
      matching-law = square-to-changeEndpoints (F ◁ left-law) (Δ ◁ right-law)
        (Cone.match original) (Cone.match value) (transpose-square₌ (ConeIdentification₁.compatible cone-law))
      factor-law : pullback-factor value =₁ induced
      factor-law = pullback-reflect _ _
        (cone-compose (cone-inverse cone-law) (pullback-factor-β value))
      preserve : IsPullback s → IsPullback value
      preserve es = equiv-transport (factor-law ⁻¹) (equiv-compose (pullback-factor s) forward es forward-isEquiv)
      reflect : IsPullback value → IsPullback s
      reflect es = equiv-cancel-left (pullback-factor s) forward forward-isEquiv (equiv-transport factor-law es)
```
