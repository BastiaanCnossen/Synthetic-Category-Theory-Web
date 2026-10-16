# Postcomposition commutes with edge restriction, with its point images

Restricting the image diagram and taking the image of the restricted diagram
represent the same uncurried diagram. Reflection compares these two arrow
families. Its point image agrees with the existing evaluation comparisons
on both sides. The categorical parameter is arbitrary; both endpoints and
all vertex specializations use the same calculation.

This candidate retains the original precomposition and postcomposition maps.
It chooses the displayed reflected comparison for this parameter family;
it does not assert equality with a different preselected comparison.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PostcompositionRestriction where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-right; preWhisker-comp₌; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (module CompositeEvaluation)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPost; funPre-uncurry; funPost-uncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; evAt; insert; evAt-pre; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition
  using (module InsertionComposition; module PrecompositionPointEvaluation)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationPostcomposition using (module PointPostcomposition)

private
  module PointTail {Γ : Context} {X Y : CAT Γ}
    {r s t z q n m₀ : MAP X Y}
    (w : t =₁ z) (image : s =₁ t) (new : r =₁ s)
    (a₀ : q =₁ r) (b : n =₁ m₀) (p : q =₁ n) (mu : m₀ =₁ z)
    (given : (w ∙ (image ∙ (new ∙ a₀))) =₂ (mu ∙ (b ∙ p))) where
    private
      native = w ∙ (image ∙ new)
      append : (native ∙ a₀) =₂ (w ∙ (image ∙ (new ∙ a₀)))
      append = comp₌-cong (id₌ w) (comp₌-assoc image new a₀) ∙ comp₌-assoc w (image ∙ new) a₀
    compatibility : native =₂ (mu ∙ (b ∙ (p ∙ a₀ ⁻¹)))
    compatibility = comp₌-cong (id₌ mu) (comp₌-assoc b p (a₀ ⁻¹)) ∙
      (comp₌-assoc mu (b ∙ p) (a₀ ⁻¹) ∙
        (comp₌-cong (given ∙ append) (id₌ (a₀ ⁻¹)) ∙
          (comp-inv-right native a₀) ⁻¹))

  module PointImage {Γ : Context} {I P C D : CAT Γ}
    (a : MAP One I) (F : MAP C D) (h : MAP P (Fun I C)) where
    private
      K : MAP (Fun I C) (Fun I D)
      K = funPost {C = I} F
      i = insert {P = P} a
      mu = AtPoint.uncurry-image a h
      U = funPost-uncurry F h ▷ i
      new = AtPoint.uncurry-image a (K ∘ h)
      w = comp-assoc i (funUncurry h) F
      b = comp-assoc h (evAt a) F
      p = evAt-post a F ▷ h
      a₀ = comp-assoc h K (evAt a)
    comparison : (evAt a ∘ (K ∘ h)) =₁ (F ∘ (evAt a ∘ h))
    comparison = b ∙ (p ∙ a₀ ⁻¹)
    native : (evAt a ∘ (K ∘ h)) =₁ (F ∘ (funUncurry h ∘ i))
    native = w ∙ (U ∙ new)
    compatibility : native =₂ ((F ◁ mu) ∙ comparison)
    compatibility = PointTail.compatibility w U new a₀ b p (F ◁ mu)
      (PointPostcomposition.compatibility a F h)

  module TriangleImage {Γ : Context} {P R S C D : CAT Γ}
    (e : MAP S C) (F : MAP C D) (A : MAP S D) (beta : A =₁ (F ∘ e))
    (s : MAP R S) (i : MAP P R) (j : MAP P S) (delta : (s ∘ i) =₁ j) where
    module N = CompositeEvaluation e F A beta s i j delta
    before = post-triangle e s i delta
    after = post-triangle A s i delta
    private
      fc = F ◁ (e ◁ delta)
      fa = F ◁ comp-assoc i s e
      tail = comp-assoc i (e ∘ s) F ∙ (N.N s ▷ i)
    compatibility : (N.N j ∙ after) =₂ ((F ◁ before) ∙ tail)
    compatibility = comp₌-cong ((postWhisker-comp₌ F (e ◁ delta) (comp-assoc i s e)) ⁻¹) (id₌ tail) ∙
      (((comp₌-assoc fc fa tail) ⁻¹) ∙
        (comp₌-cong (id₌ fc) N.iterated ∙
          (comp₌-assoc fc (N.N (s ∘ i)) (comp-assoc i s A) ∙
            (comp₌-cong N.natural (id₌ (comp-assoc i s A)) ∙
              (comp₌-assoc (N.N j) (A ◁ delta) (comp-assoc i s A)) ⁻¹))))

  module FrameImage {Γ : Context} {P R C D : CAT Γ}
    (F : MAP C D) {V U : MAP R C} (beta : V =₁ U) (i : MAP P R)
    {x : MAP P C} (z : (U ∘ i) =₁ x) where
    compatibility : (((F ◁ z) ∙ comp-assoc i U F) ∙ ((F ◁ beta) ▷ i)) =₂
      ((F ◁ (z ∙ (beta ▷ i))) ∙ comp-assoc i V F)
    compatibility = comp₌-cong ((postWhisker-comp₌ F z (beta ▷ i)) ⁻¹) (id₌ (comp-assoc i V F)) ∙
      (((comp₌-assoc (F ◁ z) (F ◁ (beta ▷ i)) (comp-assoc i V F)) ⁻¹) ∙
        (comp₌-cong (id₌ (F ◁ z)) (whisker-mixed-One beta i F) ∙
          comp₌-assoc (F ◁ z) (comp-assoc i U F) ((F ◁ beta) ▷ i)))

module PostRestriction {Γ : Context} {J P C D : CAT Γ}
  (F : MAP C D) (d : MAP ([1] {Γ = Γ}) J) (sigma : MAP P (Fun J C)) where
  private
    H = funPost F ∘ sigma
    R = funPre {D = C} d ∘ sigma
    U = funUncurry sigma
    V = funUncurry H
    L = productMap (id P) d
    source = funPre {D = D} d ∘ H
    target = funPost F ∘ R
    b = funPost-uncurry F sigma
    restriction-image = funPre-uncurry d sigma
    cD = funPre-uncurry d H
    u = funPost-uncurry F R
    beta = (F ◁ restriction-image) ∙ u
    nL = comp-assoc L U F ∙ (b ▷ L)
    theta = nL ∙ cD
    module Lift = ReflectedEndpoint source target (F ∘ (U ∘ L)) beta theta
  comparison : source =₁ target
  comparison = Lift.comparison

  module At (a : MAP One ([1] {Γ = Γ})) where
    private
      i = insert {P = P} a
      j = insert {P = P} (d ∘ a)
      module Shape = InsertionComposition P
      chi = Shape.χ d a
      module Natural = TriangleImage U F V b L i j chi
      module PreC = PrecompositionPointEvaluation a d sigma
      module PreD = PrecompositionPointEvaluation a d H
      module Post = PointImage (d ∘ a) F sigma
      module PostEdge = PointImage a F R
      mu = AtPoint.uncurry-image (d ∘ a) sigma
      muH = AtPoint.uncurry-image (d ∘ a) H
      muR = AtPoint.uncurry-image a R
      muSource = AtPoint.uncurry-image a source
      muTarget = AtPoint.uncurry-image a target
      pc = (evAt-pre {C = C} a d ▷ sigma) ∙ (comp-assoc sigma (funPre d) (evAt a)) ⁻¹
      pd = (evAt-pre {C = D} a d ▷ H) ∙ (comp-assoc H (funPre d) (evAt a)) ⁻¹
      q = Natural.before
      qD = Natural.after
      ni = nL ▷ i
      prefix = (F ◁ q) ∙ comp-assoc i (U ∘ L) F
      z = q ∙ (restriction-image ▷ i)
      module Framed = PointPostcomposition.Framed a F R z
      module Changed = FrameImage F restriction-image i q
      preC : (z ∙ muR) =₂ (mu ∙ pc)
      preC = (PreC.compatibility) ⁻¹ ∙
        comp₌-assoc (U ◁ chi) (comp-assoc i L U) ((restriction-image ▷ i) ∙ muR) ∙
        comp₌-assoc q (restriction-image ▷ i) muR
      preD : (qD ∙ ((cD ▷ i) ∙ muSource)) =₂ (muH ∙ pd)
      preD = (PreD.compatibility) ⁻¹ ∙
        comp₌-assoc (V ◁ chi) (comp-assoc i L V) ((cD ▷ i) ∙ muSource)

    source-route : (evAt a ∘ source) =₁ (F ∘ (evAt (d ∘ a) ∘ sigma))
    source-route = Post.comparison ∙ pd
    target-route : (evAt a ∘ target) =₁ (F ∘ (evAt (d ∘ a) ∘ sigma))
    target-route = (F ◁ pc) ∙ PostEdge.comparison

    private
      target-normal : (prefix ∙ ((beta ▷ i) ∙ muTarget)) =₂ ((F ◁ mu) ∙ target-route)
      target-normal = comp₌-assoc (F ◁ mu) (F ◁ pc) PostEdge.comparison ∙
        (comp₌-cong (postWhisker-comp₌ F mu pc ∙ (postWhisker F ◁ preC)) (id₌ PostEdge.comparison) ∙
          (Framed.frame-image ∙
            (comp₌-cong Changed.compatibility (id₌ ((u ▷ i) ∙ muTarget)) ∙
              ((comp₌-assoc prefix ((F ◁ restriction-image) ▷ i) ((u ▷ i) ∙ muTarget)) ⁻¹ ∙
                (comp₌-cong (id₌ prefix) (comp₌-assoc ((F ◁ restriction-image) ▷ i) (u ▷ i) muTarget) ∙
                  comp₌-cong (id₌ prefix) (comp₌-cong (preWhisker-comp₌ (F ◁ restriction-image) u i) (id₌ muTarget)))))))
      coefficient : (prefix ∙ ni) =₂ (Natural.N.N j ∙ qD)
      coefficient = Natural.compatibility ⁻¹ ∙ comp₌-assoc (F ◁ q) (comp-assoc i (U ∘ L) F) ni
      source-normal : (prefix ∙ ((theta ▷ i) ∙ muSource)) =₂ ((F ◁ mu) ∙ source-route)
      source-normal = comp₌-assoc (F ◁ mu) Post.comparison pd ∙
        (comp₌-cong (Post.compatibility ∙ comp₌-assoc (comp-assoc j U F) (b ▷ j) muH) (id₌ pd) ∙
          (((comp₌-assoc (Natural.N.N j) muH pd) ⁻¹) ∙
            (comp₌-cong (id₌ (Natural.N.N j)) preD ∙
              (comp₌-assoc (Natural.N.N j) qD ((cD ▷ i) ∙ muSource) ∙
                (comp₌-cong coefficient (id₌ ((cD ▷ i) ∙ muSource)) ∙
                  ((comp₌-assoc prefix ni ((cD ▷ i) ∙ muSource)) ⁻¹ ∙
                    (comp₌-cong (id₌ prefix) (comp₌-assoc ni (cD ▷ i) muSource) ∙
                      comp₌-cong (id₌ prefix) (comp₌-cong (preWhisker-comp₌ nL cD i) (id₌ muSource)))))))))
    compatibility : (target-route ∙ (evAt a ◁ comparison)) =₂ source-route
    compatibility = cancel-left (F ◁ mu)
      (source-normal ∙
        (comp₌-cong (id₌ prefix) (Lift.endpoint a) ∙
          (comp₌-assoc prefix ((beta ▷ i) ∙ muTarget) (evAt a ◁ comparison) ∙
            (comp₌-cong (target-normal ⁻¹) (id₌ (evAt a ◁ comparison)) ∙
              (comp₌-assoc (F ◁ mu) target-route (evAt a ◁ comparison)) ⁻¹))))
```
