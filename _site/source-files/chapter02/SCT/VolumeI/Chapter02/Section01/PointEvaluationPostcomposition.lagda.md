# Point evaluation and postcomposition

Evaluation of the same diagram through two factorizations is compatible
with postcomposition. The comparison keeps the supplied identification
between the two factorizations and the original evaluation triangle.
The intended consumer is the native point equation for funPost, needed
to preserve the endpoints of identity families and triangle presentations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationPostcomposition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; comp-inv-left; comp-inv-right; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (cancel-left; postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (module CompositeEvaluation)

module EvaluationFactorizations {Γ : Context} {P Q R Z C D : CAT Γ}
  (e : MAP Z C) (F : MAP C D) (A : MAP Z D) (beta : A =₁ (F ∘ e))
  (H : MAP R Z) (i : MAP P R) (t : MAP Q Z) (h : MAP P Q)
  (n : (t ∘ h) =₁ (H ∘ i)) where
  private
    q = H ∘ i
    module L = CompositeEvaluation e F A beta H i q (id₌ q)
    module Right = CompositeEvaluation e F A beta t h q n
    a₁ = comp-assoc i H A
    a₂ = comp-assoc h t A
    e₁ = comp-assoc i H e
    e₂ = comp-assoc h t e
    d = A ◁ n
    inner-step = e ◁ n
    s = L.N q
    v = L.N H ▷ i
    w = comp-assoc i (e ∘ H) F
    b = comp-assoc h (e ∘ t) F
    u = L.N t ▷ h
    f₁ = F ◁ e₁
    f₂ = F ◁ e₂
    fc = F ◁ inner-step

  before : ((e ∘ t) ∘ h) =₁ ((e ∘ H) ∘ i)
  before = e₁ ⁻¹ ∙ (inner-step ∙ e₂)

  after : ((A ∘ t) ∘ h) =₁ ((A ∘ H) ∘ i)
  after = a₁ ⁻¹ ∙ (d ∙ a₂)

  private
    front : ((w ∙ v) ∙ a₁ ⁻¹) =₂ (f₁ ⁻¹ ∙ s)
    front = cancel-left f₁
      ((comp-inv-left f₁ s) ⁻¹ ∙
        (comp-inv-right s a₁ ∙
          (comp₌-cong (L.iterated ⁻¹) (id₌ (a₁ ⁻¹)) ∙
            (comp₌-assoc f₁ (w ∙ v) (a₁ ⁻¹)) ⁻¹)))

    back : (s ∙ (d ∙ a₂)) =₂ (fc ∙ (f₂ ∙ (b ∙ u)))
    back = comp₌-cong (id₌ fc) Right.iterated ∙
      (comp₌-assoc fc (L.N (t ∘ h)) a₂ ∙
        (comp₌-cong Right.natural (id₌ a₂) ∙ (comp₌-assoc s d a₂) ⁻¹))

    image : (F ◁ before) =₂ (f₁ ⁻¹ ∙ (fc ∙ f₂))
    image = comp₌-cong (postWhisker-inverse F e₁)
      (postWhisker-comp₌ F inner-step e₂) ∙ postWhisker-comp₌ F (e₁ ⁻¹) (inner-step ∙ e₂)

    expose-front : (w ∙ (v ∙ after)) =₂ (((w ∙ v) ∙ a₁ ⁻¹) ∙ (d ∙ a₂))
    expose-front = (comp₌-assoc (w ∙ v) (a₁ ⁻¹) (d ∙ a₂)) ⁻¹ ∙
      (comp₌-assoc w v after) ⁻¹

    collect-image : (f₁ ⁻¹ ∙ (fc ∙ (f₂ ∙ (b ∙ u)))) =₂
      ((F ◁ before) ∙ (b ∙ u))
    collect-image = comp₌-cong (image ⁻¹) (id₌ (b ∙ u)) ∙
      ((comp₌-assoc (f₁ ⁻¹) (fc ∙ f₂) (b ∙ u)) ⁻¹ ∙
        comp₌-cong (id₌ (f₁ ⁻¹)) ((comp₌-assoc fc f₂ (b ∙ u)) ⁻¹))

  compatibility :
    (comp-assoc i (e ∘ H) F ∙ ((L.N H ▷ i) ∙ after)) =₂
      ((F ◁ before) ∙ (comp-assoc h (e ∘ t) F ∙ (L.N t ▷ h)))
  compatibility = collect-image ∙
    (comp₌-cong (id₌ (f₁ ⁻¹)) back ∙
      (comp₌-assoc (f₁ ⁻¹) s (d ∙ a₂) ∙
        (comp₌-cong front (id₌ (d ∙ a₂)) ∙ expose-front)))
```

For the chosen postcomposition functor, its uncurrying comparison and point
comparison use this same beta. The parameter-composition law for uncurrying
therefore gives the following equation for their literal chosen witnesses.

```agda
open import SCT.VolumeI.Chapter01.Section02.Specialization using (preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-β; funPost-uncurry)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module UncurryRoute; module ParameterInsertion; module UncurryParameter)

module PointPostcomposition {Γ : Context} {I P C D : CAT Γ}
  (a : MAP One I) (F : MAP C D) (h : MAP P (Fun I C)) where
  private
    K = funPost {C = I} F
    e = funEval {C = I} {D = C}
    eD = funEval {C = I} {D = D}
    H = productMap h (id I)
    i = insert {P = P} a
    t = insert {P = Fun I C} a
    A = funUncurry K
    beta = funPost-β {C = I} F
    n = ParameterInsertion.value a h
    module G = EvaluationFactorizations e F A beta H i t h n
    module N = CompositeEvaluation e F A beta H i (H ∘ i) (id₌ (H ∘ i))
    module Q = UncurryParameter a K h
    r = evaluate-restrict eD K h
    ri = r ▷ i
    v = N.N H ▷ i
    u = AtPoint.uncurry-image a K ▷ h
    w = comp-assoc i (e ∘ H) F
    b = comp-assoc h (e ∘ t) F
    inner-step = N.N t ▷ h
    point-of-image = AtPoint.uncurry-image a (K ∘ h)
    a₀ = comp-assoc h K (evAt a)
    a₁ = comp-assoc i H A
    a₂ = comp-assoc h t A
    d = A ◁ n

    parameter : (point-of-image ∙ a₀) =₂ (ri ⁻¹ ∙ (G.after ∙ u))
    parameter = comp₌-cong (preWhisker-inverse r i)
      ((comp₌-assoc (a₁ ⁻¹) (d ∙ a₂) u) ⁻¹ ∙
        comp₌-cong (id₌ (a₁ ⁻¹)) ((comp₌-assoc d a₂ u) ⁻¹)) ∙ Q.composition

    split-uncurry : (funPost-uncurry F h ▷ i) =₂ (v ∙ ri)
    split-uncurry = preWhisker-comp₌ (N.N H) r i ∙
      (preWhisker i ◁ ((comp₌-assoc (comp-assoc H e F) (beta ▷ H) r) ⁻¹))

    cancel-parameter : ((v ∙ ri) ∙ (ri ⁻¹ ∙ (G.after ∙ u))) =₂ (v ∙ (G.after ∙ u))
    cancel-parameter = comp₌-cong (id₌ v) (comp-inv-left ri (G.after ∙ u)) ∙
      comp₌-assoc v ri (ri ⁻¹ ∙ (G.after ∙ u))

    split-point : (inner-step ∙ u) =₂ (evAt-post a F ▷ h)
    split-point = (preWhisker h ◁
        ((comp₌-assoc (comp-assoc t e F) (beta ▷ t) (AtPoint.uncurry-image a K)) ⁻¹)) ⁻¹ ∙
      (preWhisker-comp₌ (N.N t) (AtPoint.uncurry-image a K) h) ⁻¹

    finish : ((F ◁ G.before) ∙ (b ∙ (inner-step ∙ u))) =₂
      ((F ◁ AtPoint.uncurry-image a h) ∙ (b ∙ (evAt-post a F ▷ h)))
    finish = comp₌-cong (postWhisker F ◁ (UncurryRoute.factorization a h) ⁻¹)
      (comp₌-cong (id₌ b) split-point)

  compatibility :
    (comp-assoc i (funUncurry h) F ∙
      ((funPost-uncurry F h ▷ i) ∙
        (AtPoint.uncurry-image a (funPost F ∘ h) ∙ comp-assoc h (funPost F) (evAt a)))) =₂
    ((F ◁ AtPoint.uncurry-image a h) ∙
      (comp-assoc h (evAt a) F ∙ (evAt-post a F ▷ h)))
  compatibility = finish ∙
    (comp₌-cong (id₌ (F ◁ G.before)) (comp₌-assoc b inner-step u) ∙
      (comp₌-assoc (F ◁ G.before) (b ∙ inner-step) u ∙
        (comp₌-cong G.compatibility (id₌ u) ∙
          ((comp₌-assoc w (v ∙ G.after) u) ⁻¹ ∙
            (comp₌-cong (id₌ w) ((comp₌-assoc v G.after u) ⁻¹) ∙
              (comp₌-cong (id₌ w) cancel-parameter ∙
                comp₌-cong (id₌ w)
                  (comp₌-cong split-uncurry parameter)))))))

  module Framed {x : MAP P C} (z : (funUncurry h ∘ i) =₁ x) where
    private
      mu = AtPoint.uncurry-image a h
      U = funPost-uncurry F h ▷ i
      p = evAt-post a F ▷ h
      direct = w ∙ (U ∙ point-of-image)
      tail = b ∙ (p ∙ a₀ ⁻¹)
      append : (direct ∙ a₀) =₂ (w ∙ (U ∙ (point-of-image ∙ a₀)))
      append = comp₌-cong (id₌ w) (comp₌-assoc U point-of-image a₀) ∙
        comp₌-assoc w (U ∙ point-of-image) a₀
      solved : direct =₂ ((F ◁ mu) ∙ tail)
      solved = comp₌-cong (id₌ (F ◁ mu)) (comp₌-assoc b p (a₀ ⁻¹)) ∙
        (comp₌-assoc (F ◁ mu) (b ∙ p) (a₀ ⁻¹) ∙
          (comp₌-cong (compatibility ∙ append) (id₌ (a₀ ⁻¹)) ∙
            (comp-inv-right direct a₀) ⁻¹))

    frame-image :
      (((F ◁ z) ∙ comp-assoc i (funUncurry h) F) ∙
        ((funPost-uncurry F h ▷ i) ∙ AtPoint.uncurry-image a (funPost F ∘ h))) =₂
      ((F ◁ (z ∙ AtPoint.uncurry-image a h)) ∙
        (comp-assoc h (evAt a) F ∙ ((evAt-post a F ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹)))
    frame-image = comp₌-cong ((postWhisker-comp₌ F z mu) ⁻¹) (id₌ tail) ∙
      ((comp₌-assoc (F ◁ z) (F ◁ mu) tail) ⁻¹ ∙
        (comp₌-cong (id₌ (F ◁ z)) solved ∙
          comp₌-assoc (F ◁ z) w (U ∙ point-of-image)))
```
