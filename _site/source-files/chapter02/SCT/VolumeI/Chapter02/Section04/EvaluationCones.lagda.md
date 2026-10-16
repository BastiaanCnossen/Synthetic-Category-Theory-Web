# Evaluation of whole diagram cones

Evaluation at a point of the diagram shape agrees with uncurrying the whole
cone and then restricting at that point. The comparison retains the original
matching, not only the two legs. The resulting comparison on pullbacks uses
the already constructed functor-pullback equivalence.

The point-evaluation operations are owned by Chapter 2 Section 1; this owner
therefore stays in Chapter 2 rather than importing them backwards into Chapter 1.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section04.EvaluationCones where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; id₌; inv₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-edges₌; unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-transport; equiv-compose)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints-iterated; transport-square)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-retarget-match-identification)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (pullback-reflect)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality using (CospanMap; pullback-map; pullback-map-β)
import SCT.VolumeI.Chapter01.Section06.SuccessiveCospans as Cospans
import SCT.VolumeI.Chapter01.Section06.ProductPullbacks as Coordinates
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate⁼-absolute)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry)
open import SCT.VolumeI.Chapter01.Section07.FunctorCones using (module FunctorCones)
import SCT.VolumeI.Chapter01.Section07.FunctorPullbacks as Preservation
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (evAt; insert; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (evAt-post)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationPostcomposition using (module PointPostcomposition)

private
  module PostAt {Γ : Context} {I C D T : CAT Γ}
    (a : MAP One I) (F : MAP C D) (h : MAP T (Fun I C)) where
    i = insert {P = T} a
    K = funPost {C = I} F
    A = comp-assoc i (funUncurry h) F
    B = funPost-uncurry F h ▷ i
    mu = AtPoint.uncurry-image a (K ∘ h)
    alpha = comp-assoc h K (evAt a)
    beta = comp-assoc h (evAt a) F
    q = evAt-post a F ▷ h
    image = F ◁ AtPoint.uncurry-image a h
    direct = A ∙ (B ∙ mu)
    point = beta ∙ (q ∙ alpha ⁻¹)
    append : (direct ∙ alpha) =₂ (A ∙ (B ∙ (mu ∙ alpha)))
    append = comp₌-cong (id₌ A) (comp₌-assoc B mu alpha) ∙ comp₌-assoc A (B ∙ mu) alpha
    solved : direct =₂ (image ∙ point)
    solved = comp₌-cong (id₌ image) (comp₌-assoc beta q (alpha ⁻¹)) ∙
      (comp₌-assoc image (beta ∙ q) (alpha ⁻¹) ∙
        (comp₌-cong (PointPostcomposition.compatibility a F h ∙ append) (id₌ (alpha ⁻¹)) ∙
          (comp-inv-right direct alpha) ⁻¹))
    comparison : ((A ∙ B) ∙ mu) =₂ (image ∙ point)
    comparison = solved ∙ comp₌-assoc A B mu

module EvaluationCone {Γ : Context} {I C D E : CAT Γ}
  (a : MAP One I) (f : MAP C E) (g : MAP D E) where
  cospan : CospanMap (funPost {C = I} f) (funPost {C = I} g) f g
  cospan = record
    { left = evAt a; right = evAt a; base = evAt a
    ; left-square = (evAt-post a f) ⁻¹; right-square = (evAt-post a g) ⁻¹ }
  private
    module Act = Cospans.Action cospan using (normalization; map-identification; map-restrict)
    module Coordinate = Coordinates.Coordinate (funPost {C = I} f) (funPost {C = I} g) f g
      (evAt a) (evAt a) (evAt a) (evAt-post a f) (evAt-post a g)
      using (read; left-normal; right-normal)

    normalized-evaluation : {T V : CAT Γ} (F : MAP V E) (h : MAP T (Fun I V)) →
      (comp-assoc h (evAt a) F ∙
        ((((evAt-post a F) ⁻¹) ⁻¹ ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹)) =₂
      (comp-assoc h (evAt a) F ∙
        ((evAt-post a F ▷ h) ∙ (comp-assoc h (funPost F) (evAt a)) ⁻¹))
    normalized-evaluation F h = comp₌-cong (id₌ (comp-assoc h (evAt a) F))
      (comp₌-cong (preWhisker h ◁ inverse-inverse (evAt-post a F))
        (id₌ ((comp-assoc h (funPost F) (evAt a)) ⁻¹)))

    normalized-cone : {T : CAT Γ} (s : Cone (funPost {C = I} f) (funPost {C = I} g) T)
      → ConeIdentification₁ (CospanMap.map-cone cospan s) (Coordinate.read s)
    normalized-cone s = cone-retarget-match-identification _ _
      (comp₌-cong (normalized-evaluation g (Cone.right s))
        (comp₌-cong (id₌ (evAt a ◁ Cone.match s)) (inv₌ ◁ normalized-evaluation f (Cone.left s))) ∙
        Act.normalization s)

  module At {T : CAT Γ} (s : Cone (funPost {C = I} f) (funPost {C = I} g) T) where
    private
      u = Cone.left s
      v = Cone.right s
      tau = Cone.match s
      i = insert {P = T} a
      af = comp-assoc i (funUncurry u) f
      ag = comp-assoc i (funUncurry v) g
      bf = funPost-uncurry f u ▷ i
      bg = funPost-uncurry g v ▷ i
      L = af ∙ bf
      R = ag ∙ bg
      delta = evaluate-cong (funEval {C = I} {D = E}) tau ▷ i
    target : Cone f g T
    target = cone-restrict i (FunctorCones.uncurryCone I f g s)

    private
      target-normal : Cone.match target =₂ (R ∙ (delta ∙ L ⁻¹))
      target-normal = changeEndpoints-iterated bf bg af ag delta ∙
        comp₌-cong (id₌ ag)
          (comp₌-cong
            (comp₌-cong (id₌ bg)
              (comp₌-cong (id₌ delta) (preWhisker-inverse (funPost-uncurry f u) i) ∙
                preWhisker-comp₌ (evaluate-cong (funEval {C = I} {D = E}) tau) ((funPost-uncurry f u) ⁻¹) i) ∙
              preWhisker-comp₌ (funPost-uncurry g v)
                (evaluate-cong (funEval {C = I} {D = E}) tau ∙ (funPost-uncurry f u) ⁻¹) i)
            (id₌ (af ⁻¹)))
      natural : (AtPoint.uncurry-image a (funPost g ∘ v) ∙ (evAt a ◁ tau)) =₂
        (delta ∙ AtPoint.uncurry-image a (funPost f ∘ u))
      natural = unconst-sides₌
        (replace-edges₌ (id₌ (evAt a ◁ tau))
          (preWhisker i ◁ evaluate⁼-absolute (funEval {C = I} {D = E}) tau)
          (AtPoint.uncurry-square a tau))
      evaluated : ConeIdentification₁ (Coordinate.read s) target
      evaluated = record
        { left = AtPoint.uncurry-image a u; right = AtPoint.uncurry-image a v
        ; compatible = transport-square
            (Coordinate.left-normal u) L (Coordinate.right-normal v) R
            (evAt a ◁ tau) delta
            (AtPoint.uncurry-image a (funPost f ∘ u)) (AtPoint.uncurry-image a (funPost g ∘ v))
            (f ◁ AtPoint.uncurry-image a u) (g ◁ AtPoint.uncurry-image a v)
            (PostAt.comparison a f u) (PostAt.comparison a g v) (natural ⁻¹) ∙
              comp₌-cong target-normal (id₌ (f ◁ AtPoint.uncurry-image a u)) }

    comparison : ConeIdentification₁ (CospanMap.map-cone cospan s) target
    comparison = cone-compose evaluated (normalized-cone s)

  module PullbackEvaluation where
    private
      module FunctorSquare = Preservation.FunctorPullback I f g
        using (comparison; comparison-isEquiv; comparison-computation; square)
      original = pullback-cone f g
      middle = pullback-cone (funPost {C = I} f) (funPost {C = I} g)
    comparison : ConeIdentification₁
      (cone-restrict (pullback-map cospan ∘ FunctorSquare.comparison) original)
      (cone-restrict (evAt a) original)
    comparison = cone-compose (cone-restrict-assoc (insert a) (funEval {C = I} {D = Pullback f g}) original)
      (cone-compose (cone-identification-restrict-One (insert a) (Preservation.mappedCone-evaluation I original))
      (cone-compose (At.comparison FunctorSquare.square)
      (cone-compose (Act.map-identification FunctorSquare.comparison-computation)
      (cone-compose (cone-inverse (Act.map-restrict FunctorSquare.comparison middle))
      (cone-compose (cone-identification-restrict-One FunctorSquare.comparison (pullback-map-β cospan))
        (cone-inverse (cone-restrict-assoc FunctorSquare.comparison (pullback-map cospan) original)))))))

    evaluation-comparison : (pullback-map cospan ∘ FunctorSquare.comparison) =₁ evAt a
    evaluation-comparison = pullback-reflect _ _ comparison

    evaluation-isEquiv : IsEquiv (pullback-map cospan) → IsEquiv (evAt {C = Pullback f g} a)
    evaluation-isEquiv e = equiv-transport evaluation-comparison
      (equiv-compose FunctorSquare.comparison (pullback-map cospan) FunctorSquare.comparison-isEquiv e)
```
