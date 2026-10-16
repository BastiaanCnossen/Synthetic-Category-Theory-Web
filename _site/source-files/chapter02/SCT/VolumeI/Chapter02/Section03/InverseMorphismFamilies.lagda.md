# Inverse morphism families from the specified triangles

The two inverse triangles of the actual isomorphism category give two
possibly different inverse families. Both composition equations retain
the prescribed endpoint frames. The two defining pullback matchings are
used directly; no Rezk assumption is involved.

First compare the native constant-arrow family with the chosen identity
family. Their arrows are not definitionally the same: one is obtained by
restricting the identity-arrow functor, the other by currying a constant
interval diagram. Reflection and evaluation along insertion supply both
endpoint equations for that comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; inv-comp-left; inv-comp-right; comp-inv-right; preWhisker-comp₌; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (paste-square₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; restrict-change-square-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (pullback-cone; pullback-match)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry-β; funUncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; evAt-constant; insert; identityArrow; identity-family;
    constantArrow-image; MorphismFamily; MorphismFamilyIdentification; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons using (compose-family-comparisons)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.RestrictedDiagramEvaluation using (module RestrictedDiagramEvaluation)
open import SCT.VolumeI.Chapter02.Section01.InsertionSectionComparison using (module InsertionSectionComparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (Triangles; edge₀; edge₁; edge₂; short-edges; triangle-cone)
open import SCT.VolumeI.Chapter02.Section02.TriangleCornerFrames using (module TriangleCornerFrames)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations
  using (TrianglePresentation; triangle-presentation; presented-composition)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms
  using (Iso; InverseTriangles; firstInverseTriangle; secondInverseTriangle;
    inverseLongEdges; inverseIdentityEdges; isoTriangles; isoObjects; isoArrow)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC

module _ {Γ : Context} {P C : CAT Γ} where
  constant-frame : (a : MAP One ([1] {Γ = Γ})) (z : MAP P C)
    → (evAt a ∘ (identityArrow ∘ z)) =₁ z
  constant-frame a z = comp-unitˡ z ∙ restrict-triangle (evAt a) identityArrow (evAt-constant a) z

  constant-family : (z : MAP P C) → MorphismFamily z z
  constant-family z = record
    { arrow = identityArrow ∘ z
    ; source-frame = constant-frame zero z
    ; target-frame = constant-frame one z }

  constant-frame-natural : (a : MAP One ([1] {Γ = Γ})) {z y : MAP P C} (rho : z =₁ y)
    → (constant-frame a y ∙ (evAt a ◁ (identityArrow ◁ rho))) =₂ (rho ∙ constant-frame a z)
  constant-frame-natural a rho = paste-square₌
    (restrict-change-square-One (evAt a) identityArrow (id C) (evAt-constant a) rho)
    (postWhisker-id-One rho)

module ConstantIdentity {Γ : Context} {P C : CAT Γ} (r : MAP P C) where
  private
    I : CAT Γ
    I = [1]
    F : MAP C (Ar C)
    F = identityArrow
    H : MAP (C × I) C
    H = pr₁
    K : MAP (P × I) C
    K = r ∘ pr₁
    G : MAP P (Ar C)
    G = MorphismFamily.arrow (identity-family r)
    J : MAP (P × I) (C × I)
    J = productMap r (id I)
    D : (H ∘ J) =₁ K
    D = pair-β₁ (r ∘ pr₁) (id I ∘ pr₂)
    representation : funUncurry (F ∘ r) =₁ (H ∘ J)
    representation = RestrictedDiagramEvaluation.representation zero F H (constantArrow-image I C) r
    theta : funUncurry (F ∘ r) =₁ K
    theta = D ∙ representation
    module Chosen = ReflectedEndpoint {Γ = Γ} (F ∘ r) G K (funCurry-β K) theta

  comparison : (identityArrow ∘ r) =₁ MorphismFamily.arrow (identity-family r)
  comparison = Chosen.comparison

  private
    module Endpoint (a : MAP One I) where
      i : MAP P (P × I)
      i = insert a
      j : MAP C (C × I)
      j = insert a
      b : (H ∘ j) =₁ id C
      b = pair-β₁ (id C) (const {P = C} a)
      b-new : (pr₁ ∘ i) =₁ id P
      b-new = pair-β₁ (id P) (const {P = P} a)
      module E = SectionEvaluation pr₁ i b-new
      module Rep = RestrictedDiagramEvaluation a F H (constantArrow-image I C) r
      module Section = InsertionSectionComparison a r
      output : (K ∘ i) =₁ r
      output = E.image r
      target-frame : (evAt a ∘ G) =₁ r
      target-frame = comp-unitʳ r ∙ ((r ◁ b-new) ∙
        (comp-assoc i pr₁ r ∙ AtPoint.curry-image a K))
      target-normal : (output ∙ AtPoint.curry-image a K) =₂ target-frame
      target-normal = comp₌-cong (id₌ (comp-unitʳ r))
          (comp₌-assoc (r ◁ b-new) (comp-assoc i pr₁ r) (AtPoint.curry-image a K)) ∙
        comp₌-assoc (comp-unitʳ r) ((r ◁ b-new) ∙ comp-assoc i pr₁ r) (AtPoint.curry-image a K)
      d : ((H ∘ J) ∘ i) =₁ (K ∘ i)
      d = D ▷ i
      T : ((H ∘ J) ∘ i) =₁ (H ∘ (J ∘ i))
      T = comp-assoc i J H
      V : ((H ∘ j) ∘ r) =₁ (H ∘ (j ∘ r))
      V = comp-assoc r j H
      eta : (H ∘ (j ∘ r)) =₁ (H ∘ (J ∘ i))
      eta = H ◁ Section.N.value r
      u : (id C ∘ r) =₁ r
      u = comp-unitˡ r
      old-point : (evAt a ∘ F) =₁ (H ∘ j)
      old-point = AtPoint.curry-image a H
      old-point-r : ((evAt a ∘ F) ∘ r) =₁ ((H ∘ j) ∘ r)
      old-point-r = old-point ▷ r
      A : ((evAt a ∘ F) ∘ r) =₁ (evAt a ∘ (F ∘ r))
      A = Rep.input-assoc

      projection : (output ∙ (d ∙ Rep.diagram-route)) =₂ (u ∙ (b ▷ r))
      projection = comp₌-cong (id₌ u) (inv-comp-right (b ▷ r) V) ∙
        (comp₌-assoc u ((b ▷ r) ∙ V ⁻¹) V ∙
          (comp₌-cong Section.compatibility (id₌ V) ∙
            (comp₌-cong (id₌ output) (comp₌-assoc d (T ⁻¹) (eta ∙ V)) ∙
              (comp₌-assoc output (d ∙ T ⁻¹) (eta ∙ V) ∙
                comp₌-assoc (output ∙ (d ∙ T ⁻¹)) eta V)) ⁻¹))

      through-representation : (target-frame ∙ (evAt a ◁ comparison)) =₂ (output ∙ (d ∙ Rep.point))
      through-representation = comp₌-cong (id₌ output)
          (comp₌-assoc d (representation ▷ i) (AtPoint.uncurry-image a (F ∘ r))) ∙
        (comp₌-cong (id₌ output)
          (comp₌-cong (preWhisker-comp₌ D representation i) (id₌ (AtPoint.uncurry-image a (F ∘ r)))) ∙
          (comp₌-cong (id₌ output) (Chosen.endpoint a) ∙
            (comp₌-assoc output (AtPoint.curry-image a K) (evAt a ◁ comparison) ∙
              comp₌-cong (target-normal ⁻¹) (id₌ (evAt a ◁ comparison)))))

      restricted : ((output ∙ (d ∙ Rep.point)) ∙ A) =₂ (u ∙ (evAt-constant a ▷ r))
      restricted = comp₌-cong (id₌ u) ((preWhisker-comp₌ b old-point r) ⁻¹) ∙
        (comp₌-assoc u (b ▷ r) old-point-r ∙
          (comp₌-cong projection (id₌ old-point-r) ∙
            ((comp₌-cong (id₌ output) (comp₌-assoc d Rep.diagram-route old-point-r) ∙
              comp₌-assoc output (d ∙ Rep.diagram-route) old-point-r) ⁻¹ ∙
              (comp₌-cong (id₌ output) (comp₌-cong (id₌ d) Rep.compatibility) ∙
                (comp₌-cong (id₌ output) (comp₌-assoc d Rep.point A) ∙
                  comp₌-assoc output (d ∙ Rep.point) A)))))

      normalized : (output ∙ (d ∙ Rep.point)) =₂ constant-frame a r
      normalized = comp₌-assoc u (evAt-constant a ▷ r) (A ⁻¹) ∙
        (comp₌-cong restricted (id₌ (A ⁻¹)) ∙
          (comp-inv-right (output ∙ (d ∙ Rep.point)) A) ⁻¹)
      compatible : (target-frame ∙ (evAt a ◁ comparison)) =₂ constant-frame a r
      compatible = normalized ∙ through-representation

  value : MorphismFamilyIdentification One (constant-family r) (identity-family r)
  value = family-comparison _ _ comparison (Endpoint.compatible zero) (Endpoint.compatible one)
```

An inverse triangle initially has a constant long edge at its recorded
object. Its corner equations identify that object with the endpoint of
the given family. Transporting the long edge along this identification
allows the other short edge to be framed as an inverse. Each construction
retains the triangle and all three edge comparisons.

```agda
private
  module _ {Γ : Context} {P C : CAT Γ} where
    quotient-square : {a b c d : MAP P C}
      (q : c =₁ d) (p : b =₁ d) (L : a =₁ b) (R : a =₁ c)
      → (p ∙ L) =₂ (q ∙ R) → ((q ⁻¹ ∙ p) ∙ L) =₂ R
    quotient-square q p L R square = inv-comp-left q R ∙
      (comp₌-cong (id₌ (q ⁻¹)) square ∙ comp₌-assoc (q ⁻¹) p L)

    identity-whisker-left : {U : CAT Γ} (e : MAP U C)
      (h : MAP P U) {v : MAP P C} (k : v =₁ (e ∘ h))
      → ((e ◁ id₌ h) ∙ k) =₂ k
    identity-whisker-left e h k = comp₌-unitˡ-One k ∙
      comp₌-cong (postWhisker-id₌ e h) (id₌ k)

    identity-whisker-right : {U : CAT Γ} (e : MAP U C)
      (h : MAP P U) {v : MAP P C} (k : (e ∘ h) =₁ v)
      → (k ∙ (e ◁ id₌ h)) =₂ k
    identity-whisker-right e h k = comp₌-unitʳ-One k ∙
      comp₌-cong (id₌ k) (postWhisker-id₌ e h)

  module MoveConstant {Γ : Context} {P C : CAT Γ}
    {h : MAP P (Ar C)} {z y : MAP P C}
    (long : h =₁ (identityArrow ∘ z)) (rho : z =₁ y) where
    comparison : h =₁ (identityArrow ∘ y)
    comparison = (identityArrow ◁ rho) ∙ long

    endpoint : (a : MAP One ([1] {Γ = Γ})) →
      (constant-frame a y ∙ (evAt a ◁ comparison)) =₂
        (rho ∙ (constant-frame a z ∙ (evAt a ◁ long)))
    endpoint a = comp₌-assoc rho (constant-frame a z) (evAt a ◁ long) ∙
      (comp₌-cong (constant-frame-natural a rho) (id₌ (evAt a ◁ long)) ∙
        ((comp₌-assoc (constant-frame a y) (evAt a ◁ (identityArrow ◁ rho))
          (evAt a ◁ long)) ⁻¹ ∙
          comp₌-cong (id₌ (constant-frame a y))
            (postWhisker-comp₌ (evAt a) (identityArrow ◁ rho) long)))

module RightInverseTriangle {Γ : Context} {P C : CAT Γ}
  {x y z : MAP P C} (f : MorphismFamily x y)
  (sigma : MAP P (Triangles C))
  (second : (edge₀ {C = C} ∘ sigma) =₁ MorphismFamily.arrow f)
  (long : (edge₁ {C = C} ∘ sigma) =₁ (identityArrow ∘ z)) where
  private
    module F = MorphismFamily f
    module Frames = TriangleCornerFrames C
    g : MAP P (Ar C)
    g = edge₂ ∘ sigma
    middle : (ev₁ ∘ g) =₁ (ev₀ ∘ (edge₀ ∘ sigma))
    middle = Cone.match (cone-restrict sigma (triangle-cone C))
    source : (ev₀ ∘ (edge₁ ∘ sigma)) =₁ (ev₀ ∘ g)
    source = Cone.match (cone-restrict sigma Frames.source-cone)
    target : (ev₁ ∘ (edge₁ ∘ sigma)) =₁ (ev₁ ∘ (edge₀ ∘ sigma))
    target = Cone.match (cone-restrict sigma Frames.target-cone)
    t : (ev₁ ∘ (edge₁ ∘ sigma)) =₁ y
    t = F.target-frame ∙ ((ev₁ ◁ second) ∙ target)
    l : (ev₁ ∘ (edge₁ ∘ sigma)) =₁ z
    l = constant-frame one z ∙ (ev₁ ◁ long)
    rho : z =₁ y
    rho = t ∙ l ⁻¹
    module Moved = MoveConstant long rho
    u : (ev₀ ∘ (edge₁ ∘ sigma)) =₁ y
    u = constant-frame zero y ∙ (ev₀ ◁ Moved.comparison)
    v : (ev₁ ∘ g) =₁ (ev₀ ∘ F.arrow)
    v = (ev₀ ◁ second) ∙ middle

  inverse : MorphismFamily y x
  inverse = record
    { arrow = g
    ; source-frame = u ∙ source ⁻¹
    ; target-frame = F.source-frame ∙ v }

  private
    module G = MorphismFamily inverse
    first : (edge₂ {C = C} ∘ sigma) =₁ G.arrow
    first = id₌ g
    middle-compatible :
      ((F.source-frame ⁻¹ ∙ G.target-frame) ∙ (ev₁ ◁ first)) =₂ v
    middle-compatible = inv-comp-left F.source-frame v ∙
      identity-whisker-right ev₁ g (F.source-frame ⁻¹ ∙ G.target-frame)
    source-square :
      (constant-frame zero y ∙ (ev₀ ◁ Moved.comparison)) =₂
        (G.source-frame ∙ ((ev₀ ◁ first) ∙ source))
    source-square = (inv-comp-right u source ∙
      comp₌-cong (id₌ G.source-frame) (identity-whisker-left ev₀ g source)) ⁻¹
    target-square :
      (constant-frame one y ∙ (ev₁ ◁ Moved.comparison)) =₂ t
    target-square = inv-comp-right t l ∙ Moved.endpoint one

  presentation : TrianglePresentation inverse f (constant-family y)
  presentation = triangle-presentation sigma first second Moved.comparison
    middle-compatible
    (quotient-square G.source-frame (constant-frame zero y)
      (ev₀ ◁ Moved.comparison) ((ev₀ ◁ first) ∙ source) source-square)
    (quotient-square F.target-frame (constant-frame one y)
      (ev₁ ◁ Moved.comparison) ((ev₁ ◁ second) ∙ target) target-square)

  law : (segal : IsEquiv (short-edges C)) →
    MorphismFamilyIdentification One (MC.Composition.compose C segal f inverse) (identity-family y)
  law segal = compose-family-comparisons (ConstantIdentity.value y)
    (presented-composition segal inverse f (constant-family y) presentation)

module LeftInverseTriangle {Γ : Context} {P C : CAT Γ}
  {x y z : MAP P C} (f : MorphismFamily x y)
  (sigma : MAP P (Triangles C))
  (first : (edge₂ {C = C} ∘ sigma) =₁ MorphismFamily.arrow f)
  (long : (edge₁ {C = C} ∘ sigma) =₁ (identityArrow ∘ z)) where
  private
    module F = MorphismFamily f
    module Frames = TriangleCornerFrames C
    h : MAP P (Ar C)
    h = edge₀ ∘ sigma
    middle : (ev₁ ∘ (edge₂ ∘ sigma)) =₁ (ev₀ ∘ h)
    middle = Cone.match (cone-restrict sigma (triangle-cone C))
    source : (ev₀ ∘ (edge₁ ∘ sigma)) =₁ (ev₀ ∘ (edge₂ ∘ sigma))
    source = Cone.match (cone-restrict sigma Frames.source-cone)
    target : (ev₁ ∘ (edge₁ ∘ sigma)) =₁ (ev₁ ∘ h)
    target = Cone.match (cone-restrict sigma Frames.target-cone)
    s : (ev₀ ∘ (edge₁ ∘ sigma)) =₁ x
    s = F.source-frame ∙ ((ev₀ ◁ first) ∙ source)
    l : (ev₀ ∘ (edge₁ ∘ sigma)) =₁ z
    l = constant-frame zero z ∙ (ev₀ ◁ long)
    rho : z =₁ x
    rho = s ∙ l ⁻¹
    module Moved = MoveConstant long rho
    u : (ev₁ ∘ (edge₁ ∘ sigma)) =₁ x
    u = constant-frame one x ∙ (ev₁ ◁ Moved.comparison)
    v : (ev₁ ∘ (edge₂ ∘ sigma)) =₁ y
    v = F.target-frame ∙ (ev₁ ◁ first)
    frame : (ev₀ ∘ h) =₁ y
    frame = v ∙ middle ⁻¹

  inverse : MorphismFamily y x
  inverse = record
    { arrow = h
    ; source-frame = frame
    ; target-frame = u ∙ target ⁻¹ }

  private
    module H = MorphismFamily inverse
    second : (edge₀ {C = C} ∘ sigma) =₁ H.arrow
    second = id₌ h
    middle-compatible :
      ((H.source-frame ⁻¹ ∙ F.target-frame) ∙ (ev₁ ◁ first)) =₂
        ((ev₀ ◁ second) ∙ middle)
    middle-compatible = (identity-whisker-left ev₀ h middle) ⁻¹ ∙
      (inv-comp-left frame middle ∙
        (comp₌-cong (id₌ (frame ⁻¹)) ((inv-comp-right v middle) ⁻¹) ∙
          comp₌-assoc (frame ⁻¹) F.target-frame (ev₁ ◁ first)))
    source-square :
      (constant-frame zero x ∙ (ev₀ ◁ Moved.comparison)) =₂ s
    source-square = inv-comp-right s l ∙ Moved.endpoint zero
    target-square :
      (constant-frame one x ∙ (ev₁ ◁ Moved.comparison)) =₂
        (H.target-frame ∙ ((ev₁ ◁ second) ∙ target))
    target-square = (inv-comp-right u target ∙
      comp₌-cong (id₌ H.target-frame) (identity-whisker-left ev₁ h target)) ⁻¹

  presentation : TrianglePresentation f inverse (constant-family x)
  presentation = triangle-presentation sigma first second Moved.comparison
    middle-compatible
    (quotient-square F.source-frame (constant-frame zero x)
      (ev₀ ◁ Moved.comparison) ((ev₀ ◁ first) ∙ source) source-square)
    (quotient-square H.target-frame (constant-frame one x)
      (ev₁ ◁ Moved.comparison) ((ev₁ ◁ second) ∙ target) target-square)

  law : (segal : IsEquiv (short-edges C)) →
    MorphismFamilyIdentification One (MC.Composition.compose C segal inverse f) (identity-family x)
  law segal = compose-family-comparisons (ConstantIdentity.value x)
    (presented-composition segal f inverse (constant-family x) presentation)
```

Finally, use the two raw pullback matchings defining the actual isomorphism
category. Projecting the long-edge matching supplies the two long edges;
restricting the short-edge matching supplies the comparison with the
second triangle. The universal family's arrow is literally `isoArrow`.

```agda
module UniversalIsoFamily {Γ : Context} (C : CAT Γ) where
  private
    P : CAT Γ
    P = Iso C
    q : MAP P (InverseTriangles C)
    q = isoTriangles C
    o : MAP P (C × C)
    o = isoObjects C
    p₁ : MAP (InverseTriangles C) (Triangles C)
    p₁ = firstInverseTriangle C
    p₂ : MAP (InverseTriangles C) (Triangles C)
    p₂ = secondInverseTriangle C

  family : MorphismFamily (ev₀ ∘ isoArrow C) (ev₁ ∘ isoArrow C)
  family = record
    { arrow = isoArrow C
    ; source-frame = id₌ (ev₀ ∘ isoArrow C)
    ; target-frame = id₌ (ev₁ ∘ isoArrow C) }

  right-triangle : MAP P (Triangles C)
  right-triangle = p₁ ∘ q
  left-triangle : MAP P (Triangles C)
  left-triangle = p₂ ∘ q

  common-edge : (edge₀ ∘ right-triangle) =₁ (edge₂ ∘ left-triangle)
  common-edge = Cone.match (cone-restrict q (pullback-cone (edge₀ {C = C}) edge₂))
  right-short : (edge₀ ∘ right-triangle) =₁ isoArrow C
  right-short = (comp-assoc q p₁ edge₀) ⁻¹
  left-short : (edge₂ ∘ left-triangle) =₁ isoArrow C
  left-short = right-short ∙ common-edge ⁻¹
  right-long : (edge₁ ∘ right-triangle) =₁ (identityArrow ∘ (pr₂ ∘ o))
  right-long = comp-assoc o pr₂ identityArrow ∙
    (project-pair₁ (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) o ∙
      ((pr₁ ◁ pullback-match {f = inverseLongEdges C} {g = inverseIdentityEdges C}) ∙
        ((project-pair₁ (edge₁ ∘ p₁) (edge₁ ∘ p₂) q) ⁻¹ ∙
          (comp-assoc q p₁ edge₁) ⁻¹)))
  left-long : (edge₁ ∘ left-triangle) =₁ (identityArrow ∘ (pr₁ ∘ o))
  left-long = comp-assoc o pr₁ identityArrow ∙
    (project-pair₂ (identityArrow ∘ pr₂) (identityArrow ∘ pr₁) o ∙
      ((pr₂ ◁ pullback-match {f = inverseLongEdges C} {g = inverseIdentityEdges C}) ∙
        ((project-pair₂ (edge₁ ∘ p₁) (edge₁ ∘ p₂) q) ⁻¹ ∙
          (comp-assoc q p₂ edge₁) ⁻¹)))

  module Right = RightInverseTriangle family right-triangle right-short right-long
  module Left = LeftInverseTriangle family left-triangle left-short left-long

module _ {Γ : Context} {P C : CAT Γ} {x y : MAP P C} where
  record InverseFamily (segal : IsEquiv (short-edges C)) (f : MorphismFamily x y) : Set m where
    field
      left-inverse right-inverse : MorphismFamily y x
      left-law : MorphismFamilyIdentification One
        (MC.Composition.compose C segal left-inverse f) (identity-family x)
      right-law : MorphismFamilyIdentification One
        (MC.Composition.compose C segal f right-inverse) (identity-family y)

module _ {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
  iso-inverse-family : InverseFamily segal (UniversalIsoFamily.family C)
  iso-inverse-family = record
    { left-inverse = UniversalIsoFamily.Left.inverse C
    ; right-inverse = UniversalIsoFamily.Right.inverse C
    ; left-law = UniversalIsoFamily.Left.law C segal
    ; right-law = UniversalIsoFamily.Right.law C segal }
```
