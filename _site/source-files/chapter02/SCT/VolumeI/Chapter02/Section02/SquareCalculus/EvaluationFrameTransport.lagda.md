# Evaluation frame transport

Evaluation transports naming and representation identifications with their specified image words, restriction laws and parameter-square compatibilities. This is evaluation of identifications; the theorem owner separately transports the endpoint frames of actual morphism families.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCalculus.EvaluationFrameTransport where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (c; a)
open Operations
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Currying using (reflect-β-One)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre-β)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; module AtPoint)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-One)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName-β)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre-comp; funPre-cong)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost; funPost-uncurry; funPre-uncurry)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong; productMap-cong₂)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; comp₌-inverseˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName-post)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate⁼-absolute)
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section07.PreEvaluationSubstitution using (module PrecompositionCompositor)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (restriction-compositor)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (module Boundaries)
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre⁼-evaluation)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (module SeparationSecondInput)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (pre-square₌; post-square₌; inverse-square₌; paste-square₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-edges₌; unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate⁼-composition)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp-inv-left)
import SCT.VolumeI.Chapter01.Section04.Currying as Mapping
open import SCT.VolumeI.Chapter01.Section04.Points using (name; name-representation)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (mappingInclusion; mappingInclusion-name; mappingInclusion-uncurry)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
  using (evaluate-restrict-assoc; evaluate-restrict-inverse-triangle)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (identification-restriction)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (preWhisker-comp₌; inv-comp-left)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate⁼; evaluate⁼-cong; evaluate⁼-identity)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-inverseˡ; comp-inv-right; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (inverse-unique)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (inv₌)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPost-uncurry-inputs)
import SCT.VolumeI.Chapter01.Section04.Functoriality as Maps
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map; mapEval; uncurry)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (mappingInclusion-uncurry-inputs)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun
  using (mappingInclusion-β; mappingInclusion-post; mappingInclusion-post-image)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (inverse-composite)
open import SCT.VolumeI.Chapter01.Section07.PostEvaluationSubstitution using (funPost-uncurry-restrict)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)

module PostEvaluationFrame {Γ : Context} {T R B C D : CAT Γ}
  (f : MAP C D) (i : MAP T (Fun B C)) (r : MAP R T)
  (d : MAP (T × B) C) (beta : funUncurry i =₁ d) where
  private
    eC = funEval {C = B} {D = C}
    eD = funEval {C = B} {D = D}
    change = productMap r (id B)
    restriction = evaluate-restrict eC i r
    a = f ◁ (beta ▷ change)
    b = f ◁ restriction
    k = f ◁ beta
    u = funPost-uncurry f i
    v = evaluate-restrict eD (funPost {C = B} f ∘ i) r
    x = funPost-uncurry f (i ∘ r)
    z = evaluate-cong eD (comp-assoc r i (funPost {C = B} f))
    tail = (u ▷ change) ∙ v
    input-assoc = comp-assoc change (funUncurry i) f
    output-assoc = comp-assoc change d f
  comparison :
    (((f ◁ ((beta ▷ change) ∙ restriction)) ∙ x) ∙ z) =₂
      (output-assoc ∙ ((((f ◁ beta) ∙ u) ▷ change) ∙ v))
  comparison = comp₌-cong (id₌ output-assoc)
      (comp₌-cong ((preWhisker-comp₌ k u change) ⁻¹) (id₌ v) ∙
        (comp₌-assoc (k ▷ change) (u ▷ change) v) ⁻¹) ∙
    (comp₌-assoc output-assoc (k ▷ change) tail ∙
      (comp₌-cong ((whisker-mixed-One beta change f) ⁻¹) (id₌ tail) ∙
        ((comp₌-assoc a input-assoc tail) ⁻¹ ∙
          (comp₌-cong (id₌ a) (funPost-uncurry-restrict f i r) ∙
            (comp₌-assoc a b (x ∙ z) ∙
              (comp₌-assoc (a ∙ b) x z ∙
                comp₌-cong (comp₌-cong (postWhisker-comp₌ f (beta ▷ change) restriction) (id₌ x)) (id₌ z)))))))

module PostRepresentationChange {Γ : Context} {T B C D : CAT Γ}
  (f : MAP C D) (h k : MAP T (Fun B C)) (N : MAP (T × B) C)
  (theta : funUncurry h =₁ N) (beta : funUncurry k =₁ N) (p : h =₁ k)
  (given : (beta ∙ evaluate-cong (funEval {C = B} {D = C}) p) =₂ theta) where
  private
    eC = funEval {C = B} {D = C}
    eD = funEval {C = B} {D = D}
    Ep = evaluate-cong eC p
    top = evaluate-cong eD (funPost {C = B} f ◁ p)
    Uh = funPost-uncurry f h
    Uk = funPost-uncurry f k
    square : (Uk ∙ top) =₂ ((f ◁ Ep) ∙ Uh)
    square = unconst-sides₌
      (replace-edges₌ (evaluate⁼-absolute eD (funPost {C = B} f ◁ p))
        (postWhisker f ◁ evaluate⁼-absolute eC p) (funPost-uncurry-inputs f p))
  comparison : (((f ◁ beta) ∙ Uk) ∙ top) =₂ (((f ◁ theta) ∙ Uh))
  comparison = comp₌-cong
    ((postWhisker f ◁ given) ∙ (postWhisker-comp₌ f beta Ep) ⁻¹) (id₌ Uh) ∙
      ((comp₌-assoc (f ◁ beta) (f ◁ Ep) Uh) ⁻¹ ∙
        (comp₌-cong (id₌ (f ◁ beta)) square ∙ comp₌-assoc (f ◁ beta) Uk top))

module NamingImageCalculus {Γ : Context} (B D : CAT Γ) where
  private e = funEval {C = B} {D = D}
  E : {T : CAT Γ} {h k : MAP T (Fun B D)} → h =₁ k → funUncurry h =₁ funUncurry k
  E = evaluate-cong e

  congruence : {T : CAT Γ} {h k : MAP T (Fun B D)} {p q : h =₁ k}
    → p =₂ q → E p =₂ E q
  congruence {p = p} {q} given = evaluate⁼-absolute e q ∙
    (evaluate⁼-cong e given ∙ (evaluate⁼-absolute e p) ⁻¹)

  restriction : {R T : CAT Γ} {h k : MAP T (Fun B D)} (p : h =₁ k) (r : MAP R T)
    → (evaluate-restrict e k r ∙ E (p ▷ r)) =₂
      ((E p ▷ productMap r (id B)) ∙ evaluate-restrict e h r)
  restriction p r = unconst-sides₌
    (replace-edges₌ (evaluate⁼-absolute e (p ▷ r))
      (preWhisker (productMap r (id B)) ◁ evaluate⁼-absolute e p)
      (evaluate-restrict-inputs e p r))

  composition : {T : CAT Γ} {h k l : MAP T (Fun B D)} (q : k =₁ l) (p : h =₁ k)
    → E (q ∙ p) =₂ (E q ∙ E p)
  composition q p = comp₌-cong (evaluate⁼-absolute e q) (evaluate⁼-absolute e p) ∙
    (evaluate⁼-composition e q p ∙ (evaluate⁼-absolute e (q ∙ p)) ⁻¹)

  inverse : {T : CAT Γ} {h k : MAP T (Fun B D)} (p : h =₁ k) → E (p ⁻¹) =₂ (E p) ⁻¹
  inverse {h = h} p = (inv₌ ◁ evaluate⁼-absolute e p) ∙
    (((inverse-unique (evaluate⁼ e p) (evaluate⁼ e (p ⁻¹))
      (evaluate⁼-identity e h ∙
        (evaluate⁼-cong e (comp₌-inverseˡ p) ∙ (evaluate⁼-composition e (p ⁻¹) p) ⁻¹))) ⁻¹) ∙
      (evaluate⁼-absolute e (p ⁻¹)) ⁻¹)

  paste : {T : CAT Γ} {h k l : MAP T (Fun B D)} {N : MAP (T × B) D}
    (q : k =₁ l) (p : h =₁ k)
    (rh : funUncurry h =₁ N) (rk : funUncurry k =₁ N) (rl : funUncurry l =₁ N)
    → (rl ∙ E q) =₂ rk → (rk ∙ E p) =₂ rh → (rl ∙ E (q ∙ p)) =₂ rh
  paste q p rh rk rl upper lower = lower ∙
    (comp₌-cong upper (id₌ (E p)) ∙
      ((comp₌-assoc rl (E q) (E p)) ⁻¹ ∙ comp₌-cong (id₌ rl) (composition q p)))

  reverse : {T : CAT Γ} {h k : MAP T (Fun B D)} {N : MAP (T × B) D}
    (p : h =₁ k) (rh : funUncurry h =₁ N) (rk : funUncurry k =₁ N)
    → (rk ∙ E p) =₂ rh → (rh ∙ E (p ⁻¹)) =₂ rk
  reverse p rh rk given = comp-inv-right rk (E p) ∙
    (comp₌-cong (given ⁻¹) (id₌ ((E p) ⁻¹)) ∙
      comp₌-cong (id₌ rh) (inverse p))

  prepend : {T : CAT Γ} {h k : MAP T (Fun B D)} {N M : MAP (T × B) D}
    (p : h =₁ k) (rh : funUncurry h =₁ N) (rk : funUncurry k =₁ N) (tail : N =₁ M)
    → (rk ∙ E p) =₂ rh → ((tail ∙ rk) ∙ E p) =₂ (tail ∙ rh)
  prepend p rh rk tail given = comp₌-cong (id₌ tail) given ∙ comp₌-assoc tail rk (E p)

module EvaluatedEndpointTransport {Γ : Context} {T J B D : CAT Γ}
  (a : MAP One J) (h k : MAP T (Fun J (Fun B D)))
  (epsilon : funUncurry h =₁ funUncurry k)
  (raw : funUncurry (funUncurry h) =₁ funUncurry (funUncurry k))
  (given : evaluate-cong (funEval {C = B} {D = D}) epsilon =₂ raw) where
  private
    module N = NamingImageCalculus B D using (E; composition; inverse; restriction)
    e = funEval {C = B} {D = D}
    i = insert {P = T} a
    step = productMap i (id B)
    muH = AtPoint.uncurry-image a h
    muK = AtPoint.uncurry-image a k
    rH = evaluate-restrict e (funUncurry h) i
    rK = evaluate-restrict e (funUncurry k) i
    R = raw ▷ step
    point-image : N.E (epsilon ▷ i) =₂ ((rK ⁻¹) ∙ (R ∙ rH))
    point-image = comp₌-cong (id₌ (rK ⁻¹))
      (comp₌-cong (preWhisker step ◁ given) (id₌ rH) ∙ N.restriction epsilon i) ∙
        (inv-comp-left rK (N.E (epsilon ▷ i))) ⁻¹
  transport : (evAt a ∘ h) =₁ (evAt a ∘ k)
  transport = (muK ⁻¹) ∙ ((epsilon ▷ i) ∙ muH)
  cornerH : funUncurry (evAt a ∘ h) =₁ (funUncurry (funUncurry h) ∘ step)
  cornerH = rH ∙ N.E muH
  cornerK : funUncurry (evAt a ∘ k) =₁ (funUncurry (funUncurry k) ∘ step)
  cornerK = rK ∙ N.E muK
  image : N.E transport =₂ ((cornerK ⁻¹) ∙ (R ∙ cornerH))
  image = comp₌-cong ((inverse-composite rK (N.E muK)) ⁻¹) (id₌ (R ∙ cornerH)) ∙
    ((comp₌-assoc ((N.E muK) ⁻¹) (rK ⁻¹) (R ∙ cornerH)) ⁻¹ ∙
      (comp₌-cong (id₌ ((N.E muK) ⁻¹))
        (comp₌-cong (id₌ (rK ⁻¹)) (comp₌-assoc R rH (N.E muH)) ∙
          (comp₌-assoc (rK ⁻¹) (R ∙ rH) (N.E muH) ∙
            comp₌-cong point-image (id₌ (N.E muH)))) ∙
        (comp₌-cong (N.inverse muK) (N.composition (epsilon ▷ i) muH) ∙
          N.composition (muK ⁻¹) ((epsilon ▷ i) ∙ muH))))

module DoublePointIdentification {Γ : Context} {T J B D : CAT Γ}
  (a : MAP One J) {h k : MAP T (Fun J (Fun B D))} (delta : h =₁ k) where
  private
    module N = NamingImageCalculus B D
    e = funEval {C = B} {D = D}
    eJ = funEval {C = J} {D = Fun B D}
    i = insert {P = T} a
    step = productMap i (id B)
    muH = AtPoint.uncurry-image a h
    muK = AtPoint.uncurry-image a k
    epsilon = evaluate-cong eJ delta
    edge = evAt a ◁ delta
    rh = evaluate-restrict e (funUncurry h) i
    rk = evaluate-restrict e (funUncurry k) i
    native : (muK ∙ edge) =₂ ((epsilon ▷ i) ∙ muH)
    native = unconst-sides₌
      (replace-edges₌ (id₌ edge)
        (preWhisker i ◁ evaluate⁼-absolute eJ delta) (AtPoint.uncurry-square a delta))
    evaluated : (N.E muK ∙ N.E edge) =₂ (N.E (epsilon ▷ i) ∙ N.E muH)
    evaluated = N.composition (epsilon ▷ i) muH ∙
      (N.congruence native ∙ (N.composition muK edge) ⁻¹)
  cornerH = rh ∙ N.E muH
  cornerK = rk ∙ N.E muK
  compatibility : (cornerK ∙ N.E edge) =₂ ((N.E epsilon ▷ step) ∙ cornerH)
  compatibility = comp₌-assoc (N.E epsilon ▷ step) rh (N.E muH) ∙
    (comp₌-cong (N.restriction epsilon i) (id₌ (N.E muH)) ∙
      ((comp₌-assoc rk (N.E (epsilon ▷ i)) (N.E muH)) ⁻¹ ∙
        (comp₌-cong (id₌ rk) evaluated ∙ comp₌-assoc rk (N.E muK) (N.E edge))))

module RepresentedEvaluationRestriction {Γ : Context} {K F B D : CAT Γ}
  (e : MAP (F × B) D) (d : MAP (K × B) D) (H : MAP K F)
  (beta : evaluate e H =₁ d) where
  comparison : {T : CAT Γ} (g : MAP T K) → evaluate e (H ∘ g) =₁ evaluate d g
  comparison g = (beta ▷ productMap g (id B)) ∙ evaluate-restrict e H g

  comparison-restrict : {R T : CAT Γ} (g : MAP T K) (r : MAP R T)
    → (evaluate-restrict d g r ∙
        (comparison (g ∘ r) ∙ evaluate-cong e (comp-assoc r g H))) =₂
      ((comparison g ▷ productMap r (id B)) ∙ evaluate-restrict e (H ∘ g) r)
  comparison-restrict g r = right-normal ⁻¹ ∙
    (comp₌-cong cancelled (id₌ tail) ∙
      ((comp₌-assoc coefficient ((beta ▷ Q) ∙ change) tail) ⁻¹ ∙
        comp₌-cong (id₌ coefficient)
          ((comp₌-assoc (beta ▷ Q) change tail) ⁻¹ ∙
            (comp₌-cong (id₌ (beta ▷ Q)) iteration ∙
              comp₌-assoc (beta ▷ Q) W Z))))
    where
      S = productMap g (id B)
      restriction-map = productMap r (id B)
      Q = productMap (g ∘ r) (id B)
      delta = productMap-first-comp g r
      A = evaluate e H
      U = evaluate-restrict e H g
      V = evaluate-restrict e (H ∘ g) r
      W = evaluate-restrict e H (g ∘ r)
      Z = evaluate-cong e (comp-assoc r g H)
      tail = (U ▷ restriction-map) ∙ V
      change = (A ◁ delta) ∙ comp-assoc restriction-map S A
      target-change = (d ◁ delta) ∙ comp-assoc restriction-map S d
      coefficient = evaluate-restrict d g r
      double-beta = (beta ▷ S) ▷ restriction-map
      square : (target-change ∙ double-beta) =₂ ((beta ▷ Q) ∙ change)
      square = replace-sides₌
        (comp₌-cong (id₌ (A ◁ delta)) (const-One (comp-assoc restriction-map S A)))
        (comp₌-cong (id₌ (d ◁ delta)) (const-One (comp-assoc restriction-map S d)))
        (identification-restriction beta S restriction-map Q delta)
      cancelled : (coefficient ∙ ((beta ▷ Q) ∙ change)) =₂ double-beta
      cancelled = inv-comp-left target-change double-beta ∙
        comp₌-cong (evaluate-restrict-inverse-triangle d g r) (square ⁻¹)
      iteration : (W ∙ Z) =₂ (change ∙ tail)
      iteration = (comp₌-assoc (A ◁ delta) (comp-assoc restriction-map S A) tail) ⁻¹ ∙
        evaluate-restrict-assoc e H g r
      right-normal : ((comparison g ▷ restriction-map) ∙ V) =₂ (double-beta ∙ tail)
      right-normal = comp₌-assoc double-beta (U ▷ restriction-map) V ∙
        comp₌-cong (preWhisker-comp₌ (beta ▷ S) U restriction-map) (id₌ V)

module SelectedInclusionNameImage {Γ : Context} {X Y : CAT Γ} (h : MAP X Y) where
  private
    e = funEval {C = X} {D = Y}
  route : funUncurry (mappingInclusion X Y ∘ name h) =₁ funUncurry (funName h)
  route = (funName-β h) ⁻¹ ∙
    (Mapping.CurriedRepresentation.evaluation (name-representation h) ∙ mappingInclusion-uncurry (name h))
  image : evaluate-cong e (mappingInclusion-name h) =₂ route
  image = reflect-β-One e (funUniversal X Y) _ _ route

  triangle : (funName-β h ∙ evaluate-cong e (mappingInclusion-name h)) =₂
    (Mapping.CurriedRepresentation.evaluation (name-representation h) ∙ mappingInclusion-uncurry (name h))
  triangle = comp-inv-left (funName-β h)
    (Mapping.CurriedRepresentation.evaluation (name-representation h) ∙ mappingInclusion-uncurry (name h)) ∙
      comp₌-cong (id₌ (funName-β h)) image

module SelectedMappingPostNameImage {Γ : Context} {B C D : CAT Γ}
  (f : MAP C D) (w : MAP B C) where
  private
    a = name w
    b = name (f ∘ w)
    betaA = Mapping.CurriedRepresentation.evaluation (name-representation w)
    betaB = Mapping.CurriedRepresentation.evaluation (name-representation (f ∘ w))
    q = Maps.mapPost-name f w
    eD = funEval {C = B} {D = D}

  normalized : uncurry (Maps.mapPost f ∘ a) =₁ ((f ∘ w) ∘ pr₂)
  normalized = (comp-assoc pr₂ w f) ⁻¹ ∙ ((f ◁ betaA) ∙ Maps.mapPost-uncurry f a)

  native-image : (betaB ∙ Mapping.uncurry⁼ q) =₂ normalized
  native-image = comp-inv-left betaB normalized ∙
    comp₌-cong (id₌ betaB)
      (Mapping.uncurry-reflect-β one-isAn _ _ (betaB ⁻¹ ∙ normalized))

  included-image : ((betaB ∙ mappingInclusion-uncurry b) ∙
      evaluate-cong eD (mappingInclusion B D ◁ q)) =₂
    (normalized ∙ mappingInclusion-uncurry (Maps.mapPost f ∘ a))
  included-image = comp₌-cong native-image (id₌ (mappingInclusion-uncurry (Maps.mapPost f ∘ a))) ∙
    ((comp₌-assoc betaB (Mapping.uncurry⁼ q) (mappingInclusion-uncurry (Maps.mapPost f ∘ a))) ⁻¹ ∙
      (comp₌-cong (id₌ betaB)
        (unconst-sides₌
          (replace-edges₌ (evaluate⁼-absolute eD (mappingInclusion B D ◁ q)) (id₌ (Mapping.uncurry⁼ q))
            (mappingInclusion-uncurry-inputs q))) ∙
        comp₌-assoc betaB (mappingInclusion-uncurry b) (evaluate-cong eD (mappingInclusion B D ◁ q))))

module SelectedPostNameImageProof {Γ : Context} {B C D : CAT Γ}
  (f : MAP C D) (w : MAP B C) where
  private
    module N = NamingImageCalculus B D using (E; paste; reverse; prepend; congruence; restriction)
    eC = funEval {C = B} {D = C}
    eD = funEval {C = B} {D = D}
    i : MAP (Map B C) (Fun B C)
    i = mappingInclusion B C
    j : MAP (Map B D) (Fun B D)
    j = mappingInclusion B D
    P : MAP (Fun B C) (Fun B D)
    P = funPost {C = B} f
    Q : MAP (Map B C) (Map B D)
    Q = Maps.mapPost {C = B} f
    a : MAP One (Map B C)
    a = name w
    b : MAP One (Map B D)
    b = name (f ∘ w)
    change : MAP (One × B) (Map B C × B)
    change = productMap a (id B)
    betaA = Mapping.CurriedRepresentation.evaluation (name-representation w)
    betaB = Mapping.CurriedRepresentation.evaluation (name-representation (f ∘ w))
    s = mappingInclusion-name w
    t = mappingInclusion-name (f ∘ w)
    p = mappingInclusion-post {C = B} f
    q = Maps.mapPost-name f w
    A = (comp-assoc (pr₂ {C = One} {D = B}) w f) ⁻¹
    K = A ∙ (f ◁ betaA)
    L = (f ◁ mappingInclusion-β B C) ∙ funPost-uncurry f i
    R = Maps.mapPost-β {C = B} f ∙ mappingInclusion-uncurry Q
    associateL = comp-assoc a i P
    associateR = comp-assoc a Q j
    p₀ = P ◁ (s ⁻¹)
    p₁ = associateL ⁻¹
    p₂ = p ▷ a
    p₃ = associateR
    p₄ = j ◁ q
    p₅ = t
    baseL = (f ◁ mappingInclusion-uncurry a) ∙ funPost-uncurry f (i ∘ a)
    base₂ = comp-assoc change (mapEval {C = B} {D = C}) f ∙
      ((L ▷ change) ∙ evaluate-restrict eD (P ∘ i) a)
    base₃ = comp-assoc change (mapEval {C = B} {D = C}) f ∙
      ((R ▷ change) ∙ evaluate-restrict eD (j ∘ Q) a)
    baseR = Maps.mapPost-uncurry f a ∙ mappingInclusion-uncurry (Q ∘ a)
    r₀ = A ∙ ((f ◁ funName-β w) ∙ funPost-uncurry f (funName w))
    r₁ = K ∙ baseL
    r₂ = K ∙ base₂
    r₃ = K ∙ base₃
    r₄ = K ∙ baseR
    r₅ = betaB ∙ mappingInclusion-uncurry b
    r₆ = funName-β (f ∘ w)
    theta = betaA ∙ mappingInclusion-uncurry a
    r₁native = A ∙ ((f ◁ theta) ∙ funPost-uncurry f (i ∘ a))
    module PostChange = PostRepresentationChange f (i ∘ a) (funName w) (w ∘ pr₂)
      theta (funName-β w) s (SelectedInclusionNameImage.triangle w)
      using (comparison)
    module InclusionRestriction = RepresentedEvaluationRestriction
      eD (mapEval {C = B} {D = D}) j (mappingInclusion-β B D)
      using (comparison-restrict)

    first-normal : r₁native =₂ r₁
    first-normal = (comp₌-assoc A (f ◁ betaA) baseL) ⁻¹ ∙
      comp₌-cong (id₌ A)
        (comp₌-assoc (f ◁ betaA) (f ◁ mappingInclusion-uncurry a) (funPost-uncurry f (i ∘ a)) ∙
          comp₌-cong (postWhisker-comp₌ f betaA (mappingInclusion-uncurry a))
            (id₌ (funPost-uncurry f (i ∘ a))))
    first : (r₁ ∙ N.E p₀) =₂ r₀
    first = N.reverse (P ◁ s) r₁native r₀
        (N.prepend (P ◁ s)
          ((f ◁ theta) ∙ funPost-uncurry f (i ∘ a))
          ((f ◁ funName-β w) ∙ funPost-uncurry f (funName w)) A PostChange.comparison) ∙
      (comp₌-cong (id₌ r₁native) (N.congruence (postWhisker-inverse P s)) ∙
        comp₌-cong (first-normal ⁻¹) (id₌ (N.E p₀)))

    left-natural : (baseL ∙ N.E associateL) =₂ base₂
    left-natural = PostEvaluationFrame.comparison f i a (mapEval {C = B} {D = C}) (mappingInclusion-β B C)

    global-image : (R ∙ N.E p) =₂ L
    global-image = comp-inv-left R L ∙
      comp₌-cong (id₌ R) (mappingInclusion-post-image {C = B} f)
    restricted-global :
      (((R ▷ change) ∙ evaluate-restrict eD (j ∘ Q) a) ∙ N.E p₂) =₂
        ((L ▷ change) ∙ evaluate-restrict eD (P ∘ i) a)
    restricted-global = comp₌-cong
      ((preWhisker change ◁ global-image) ∙ (preWhisker-comp₌ R (N.E p) change) ⁻¹)
      (id₌ (evaluate-restrict eD (P ∘ i) a)) ∙
        ((comp₌-assoc (R ▷ change) (N.E p ▷ change) (evaluate-restrict eD (P ∘ i) a)) ⁻¹ ∙
          (comp₌-cong (id₌ (R ▷ change)) (N.restriction p a) ∙
            comp₌-assoc (R ▷ change) (evaluate-restrict eD (j ∘ Q) a) (N.E p₂)))
    middle : (base₃ ∙ N.E p₂) =₂ base₂
    middle = N.prepend p₂ _ _ (comp-assoc change (mapEval {C = B} {D = C}) f) restricted-global

    right-natural : (baseR ∙ N.E associateR) =₂ base₃
    right-natural = comp₌-cong (id₌ (comp-assoc change (mapEval {C = B} {D = C}) f))
        (comp₌-cong ((preWhisker-comp₌ (Maps.mapPost-β {C = B} f) (mappingInclusion-uncurry Q) change) ⁻¹)
          (id₌ (evaluate-restrict eD (j ∘ Q) a)) ∙
            (comp₌-assoc (Maps.mapPost-β {C = B} f ▷ change)
              (mappingInclusion-uncurry Q ▷ change) (evaluate-restrict eD (j ∘ Q) a)) ⁻¹) ∙
      comp₌-cong (id₌ (comp-assoc change (mapEval {C = B} {D = C}) f))
        (comp₌-cong (id₌ (Maps.mapPost-β {C = B} f ▷ change)) (InclusionRestriction.comparison-restrict Q a) ∙
          (comp₌-assoc (Maps.mapPost-β {C = B} f ▷ change)
            (Mapping.uncurry-restrict Q a) (mappingInclusion-uncurry (Q ∘ a) ∙ N.E associateR))) ∙
      (comp₌-assoc (comp-assoc change (mapEval {C = B} {D = C}) f)
        ((Maps.mapPost-β {C = B} f ▷ change) ∙ Mapping.uncurry-restrict Q a)
        (mappingInclusion-uncurry (Q ∘ a) ∙ N.E associateR) ∙
          comp₌-assoc (Maps.mapPost-uncurry f a) (mappingInclusion-uncurry (Q ∘ a)) (N.E associateR))

    second : (r₂ ∙ N.E p₁) =₂ r₁
    second = N.prepend p₁ baseL base₂ K (N.reverse associateL base₂ baseL left-natural)
    third : (r₃ ∙ N.E p₂) =₂ r₂
    third = N.prepend p₂ base₂ base₃ K middle
    fourth : (r₄ ∙ N.E p₃) =₂ r₃
    fourth = N.prepend p₃ base₃ baseR K right-natural
    last-normal : (SelectedMappingPostNameImage.normalized f w ∙ mappingInclusion-uncurry (Q ∘ a)) =₂ r₄
    last-normal = (comp₌-assoc A (f ◁ betaA) baseR) ⁻¹ ∙
      (comp₌-cong (id₌ A) (comp₌-assoc (f ◁ betaA) (Maps.mapPost-uncurry f a) (mappingInclusion-uncurry (Q ∘ a))) ∙
        comp₌-assoc A ((f ◁ betaA) ∙ Maps.mapPost-uncurry f a) (mappingInclusion-uncurry (Q ∘ a)))
    fifth : (r₅ ∙ N.E p₄) =₂ r₄
    fifth = last-normal ∙ SelectedMappingPostNameImage.included-image f w
    sixth : (r₆ ∙ N.E p₅) =₂ r₅
    sixth = SelectedInclusionNameImage.triangle (f ∘ w)

  image : (funName-β (f ∘ w) ∙ evaluate-cong eD (funName-post f w)) =₂
    ((comp-assoc pr₂ w f) ⁻¹ ∙ ((f ◁ funName-β w) ∙ funPost-uncurry f (funName w)))
  image = N.paste p₅ (p₄ ∙ (p₃ ∙ (p₂ ∙ (p₁ ∙ p₀)))) r₀ r₅ r₆ sixth
    (N.paste p₄ (p₃ ∙ (p₂ ∙ (p₁ ∙ p₀))) r₀ r₄ r₅ fifth
      (N.paste p₃ (p₂ ∙ (p₁ ∙ p₀)) r₀ r₃ r₄ fourth
        (N.paste p₂ (p₁ ∙ p₀) r₀ r₂ r₃ third
          (N.paste p₁ p₀ r₀ r₁ r₂ second first))))

module SelectedPrecompositionImage {Γ : Context} {X Y Z D : CAT Γ}
  (k : MAP X Y) (h : MAP Y Z) where
  private
    eX = funEval {C = X} {D = D}
    eZ = funEval {C = Z} {D = D}
    change = productMap (id (Fun Z D)) k

  route : funUncurry (funPre {D = D} k ∘ funPre {D = D} h) =₁
    funUncurry (funPre {D = D} (h ∘ k))
  route = (funPre-β {D = D} (h ∘ k)) ⁻¹ ∙
    ((eZ ◁
      (productMap-cong (comp-unitˡ (id (Fun Z D))) (id₌ (h ∘ k)) ∙
        productMap-comp (id (Fun Z D)) (id (Fun Z D)) k h)) ∙
      (comp-assoc change (productMap (id (Fun Z D)) h) eZ ∙
        ((funPre-β {D = D} h ▷ change) ∙ funPre-uncurry k (funPre {D = D} h))))

  image : evaluate-cong eX (funPre-comp {D = D} k h) =₂ route
  image = reflect-β-One eX (funUniversal X D) _ _ route
module SelectedPrecompositionAtParameter {Γ : Context} {A B C D : CAT Γ}
  (f : MAP A B) (g : MAP B C) where
  private
    eA = funEval {C = A} {D = D}
    eB = funEval {C = B} {D = D}
    eC = funEval {C = C} {D = D}
    Hf = funPre {D = D} f
    Hg = funPre {D = D} g
    Hgf = funPre {D = D} (g ∘ f)
    Jf = productMap (id (Fun C D)) f
    Jg = productMap (id (Fun C D)) g
    beta = funPre-β {D = D} (g ∘ f)
    p = eC ◁ restriction-compositor {P = Fun C D} f g
    q = comp-assoc Jf Jg eC
    before = (funPre-β {D = D} g ▷ Jf) ∙ funPre-uncurry f Hg
    module Image = SelectedPrecompositionImage {D = D} f g
    base-square : (beta ∙ evaluate-cong eA (funPre-comp {D = D} f g)) =₂ ((p ∙ q) ∙ before)
    base-square = (comp₌-assoc p q before) ⁻¹ ∙
      (comp-inv-left beta (p ∙ (q ∙ before)) ∙
        comp₌-cong (id₌ beta) Image.image)
    module Native = PrecompositionCompositor eA eB eC f g Hf Hg Hgf
      (funPre-β {D = D} f) (funPre-β {D = D} g) beta (funPre-comp {D = D} f g)
  comparison : {P : CAT Γ} (h : MAP P (Fun C D))
    → SquareCell₌ (evaluate-cong eA (funPre-comp {D = D} f g ▷ h))
        ((funUncurry h ◁ restriction-compositor {P = P} f g) ∙
          comp-assoc (productMap (id P) f) (productMap (id P) g) (funUncurry h))
        ((funPre-uncurry g h ▷ productMap (id P) f) ∙
          (funPre-uncurry f (Hg ∘ h) ∙ evaluate-cong eA (comp-assoc h Hg Hf)))
        (funPre-uncurry (g ∘ f) h)
  comparison = Native.comparison base-square

module SelectedPrecompositionInput {Γ : Context} {P A B D : CAT Γ}
  (h : MAP P (Fun B D)) {f g : MAP A B} (alpha : f =₁ g) where
  private
    Q = Fun B D
    RA = productMap h (id A)
    RB = productMap h (id B)
    JQf = productMap (id Q) f
    JQg = productMap (id Q) g
    JPf = productMap (id P) f
    JPg = productMap (id P) g
    deltaQ = productMap-cong (id₌ (id Q)) alpha
    deltaP = productMap-cong (id₌ (id P)) alpha
    e = funEval {C = B} {D = D}
    eA = funEval {C = A} {D = D}
    first : SquareCell₌ (evaluate-cong eA (funPre-cong {D = D} alpha ▷ h))
      (evaluate-cong eA (funPre-cong {D = D} alpha) ▷ RA)
      (evaluate-restrict eA (funPre {D = D} f) h) (evaluate-restrict eA (funPre {D = D} g) h)
    first = replace-edges₌ (evaluate⁼-absolute eA (funPre-cong {D = D} alpha ▷ h))
      (preWhisker RA ◁ evaluate⁼-absolute eA (funPre-cong {D = D} alpha))
      (unconst-sides₌ (evaluate-restrict-inputs eA (funPre-cong {D = D} alpha) h))
    base : SquareCell₌ (evaluate-cong eA (funPre-cong {D = D} alpha)) (e ◁ deltaQ)
      (funPre-β {D = D} f) (funPre-β {D = D} g)
    base = replace-edges₌ (evaluate⁼-absolute eA (funPre-cong {D = D} alpha))
      (postWhisker e ◁ productMap-cong₂ (const-One (id₌ (id Q))) (id₌ alpha))
      (unconst-sides₌ (funPre⁼-evaluation {D = D} alpha))
    second = pre-square₌ RA base
    third : SquareCell₌ ((e ◁ deltaQ) ▷ RA) (e ◁ (deltaQ ▷ RA))
      (comp-assoc RA JQf e) (comp-assoc RA JQg e)
    third = whisker-mixed-One deltaQ RA e
    fourth : SquareCell₌ (e ◁ (deltaQ ▷ RA)) (e ◁ (RB ◁ deltaP))
      (e ◁ productMap-separate h f) (e ◁ productMap-separate h g)
    fourth = post-square₌ e (SeparationSecondInput.compatibility h alpha)
    fifth : SquareCell₌ (e ◁ (RB ◁ deltaP)) (funUncurry h ◁ deltaP)
      ((comp-assoc JPf RB e) ⁻¹) ((comp-assoc JPg RB e) ⁻¹)
    fifth = inverse-square₌ (postWhisker-comp-One deltaP RB e)
  compatibility : SquareCell₌ (evaluate-cong eA (funPre-cong {D = D} alpha ▷ h))
    (funUncurry h ◁ productMap-cong (id₌ (id P)) alpha)
    (funPre-uncurry f h) (funPre-uncurry g h)
  compatibility = paste-square₌
    (paste-square₌ (paste-square₌ (paste-square₌ first second) third) fourth) fifth

module ProductIdentificationInverse {Γ : Context} {P Q B A : CAT Γ}
  {f g : MAP Q P} (n : f =₁ g) (s : MAP A B) where
  private
    p = productMap-cong n (id₌ s)
    q = productMap-cong (n ⁻¹) (id₌ s)
    cancels : (q ∙ p) =₂ const (id₌ (productMap f s))
    cancels = (const-One (id₌ (productMap f s))) ⁻¹ ∙
      (productMap-cong-id-One f s ∙
        (productMap-cong₂ (comp₌-inverseˡ-One n) (comp₌-unitˡ-One (id₌ s)) ∙
          (productMap-cong-comp (n ⁻¹) n (id₌ s) (id₌ s)) ⁻¹))
  image : q =₂ (p ⁻¹)
  image = (inverse-unique p q cancels) ⁻¹

module ProductFirstUnitSquare {Γ : Context} {P Q B : CAT Γ}
  {f g : MAP Q P} (n : f =₁ g) where
  private
    u = comp-unitˡ (id B)
  source = productMap-cong (id₌ f) u
  target = productMap-cong (id₌ g) u
  upper = productMap-cong n (id₌ (id B))
  lower = productMap-cong n (id₌ (id B ∘ id B))
  private
    upper-normal : (upper ∙ source) =₂ productMap-cong n u
    upper-normal = productMap-cong₂ (comp₌-unitʳ-One n) (comp₌-unitˡ-One u) ∙
      (productMap-cong-comp n (id₌ f) (id₌ (id B)) u) ⁻¹
    lower-normal : (target ∙ lower) =₂ productMap-cong n u
    lower-normal = productMap-cong₂ (comp₌-unitˡ-One n) (comp₌-unitʳ-One u) ∙
      (productMap-cong-comp (id₌ g) n u (id₌ (id B ∘ id B))) ⁻¹
  compatibility : (upper ∙ source) =₂ (target ∙ lower)
  compatibility = (lower-normal ⁻¹) ∙ upper-normal

module EvaluatedParameterSquare {Γ : Context} {P Q R S B D : CAT Γ}
  (d : MAP P (Fun B D)) (i : MAP Q S) (k : MAP S P)
  (t : MAP R P) (h : MAP Q R) (n : (t ∘ h) =₁ (k ∘ i)) where
  private
    module N = NamingImageCalculus B D
    e = funEval {C = B} {D = D}
    As = comp-assoc h t d
    At = comp-assoc i k d
    dn = d ◁ n
    rs = evaluate-restrict e d (t ∘ h)
    rt = evaluate-restrict e d (k ∘ i)
  native = post-square-cell d i k t h n
  lifted = productMap-cong n (id₌ (id B))
  source-frame = rs ∙ N.E As
  target-frame = rt ∙ N.E At
  private
    native-triangle : (At ∙ native) =₂ (dn ∙ As)
    native-triangle = comp-inv-left At (dn ∙ As)
    evaluated-triangle : (N.E At ∙ N.E native) =₂ (N.E dn ∙ N.E As)
    evaluated-triangle = N.composition dn As ∙
      (N.congruence native-triangle ∙ (N.composition At native) ⁻¹)
    substitution : (rt ∙ N.E dn) =₂ ((funUncurry d ◁ lifted) ∙ rs)
    substitution = unconst-sides₌
      (replace-edges₌ (evaluate⁼-absolute e dn)
        (postWhisker (funUncurry d) ◁
          productMap-cong₂ (id₌ n) (const-One (id₌ (id B))))
        (evaluate-restrict-substitution e d n))
  compatibility : (target-frame ∙ N.E native) =₂
    ((funUncurry d ◁ lifted) ∙ source-frame)
  compatibility = comp₌-assoc (funUncurry d ◁ lifted) rs (N.E As) ∙
    (comp₌-cong substitution (id₌ (N.E As)) ∙
      ((comp₌-assoc rt (N.E dn) (N.E As)) ⁻¹ ∙
        (comp₌-cong (id₌ rt) evaluated-triangle ∙
          comp₌-assoc rt (N.E At) (N.E native))))

  private
    Sfirst = productMap h (id B)
    Tfirst = productMap t (id B)
    Ifirst = productMap i (id B)
    Kfirst = productMap k (id B)
    Cs = productMap-first-comp {C = B} t h
    Ct = productMap-first-comp {C = B} k i
    V = funUncurry d
  source-restrictions =
    (evaluate-restrict e d t ▷ Sfirst) ∙ evaluate-restrict e (d ∘ t) h
  target-restrictions =
    (evaluate-restrict e d k ▷ Ifirst) ∙ evaluate-restrict e (d ∘ k) i
  source-normalization : source-frame =₂
    ((V ◁ Cs) ∙ (comp-assoc Sfirst Tfirst V ∙ source-restrictions))
  source-normalization = evaluate-restrict-assoc e d t h
  target-normalization : target-frame =₂
    ((V ◁ Ct) ∙ (comp-assoc Ifirst Kfirst V ∙ target-restrictions))
  target-normalization = evaluate-restrict-assoc e d k i
  compatibility-with-product-coefficients :
    (((V ◁ Ct) ∙ (comp-assoc Ifirst Kfirst V ∙ target-restrictions)) ∙ N.E native) =₂
      ((V ◁ lifted) ∙ ((V ◁ Cs) ∙ (comp-assoc Sfirst Tfirst V ∙ source-restrictions)))
  compatibility-with-product-coefficients = comp₌-cong (id₌ (V ◁ lifted)) source-normalization ∙
    (compatibility ∙ comp₌-cong (target-normalization ⁻¹) (id₌ (N.E native)))

  lifted-composite = (Ct ⁻¹) ∙ (lifted ∙ Cs)
  full-lifted-composite = (productMap-comp i k (id B) (id B)) ⁻¹ ∙
    (productMap-cong n (id₌ (id B ∘ id B)) ∙ productMap-comp h t (id B) (id B))
  private
    module Unit = ProductFirstUnitSquare {B = B} n
    fs = productMap-comp h t (id B) (id B)
    ft = productMap-comp i k (id B) (id B)
  lifted-composite-normalization : lifted-composite =₂ full-lifted-composite
  lifted-composite-normalization = comp₌-cong (id₌ (ft ⁻¹))
    (inv-comp-left Unit.target (Unit.lower ∙ fs) ∙
      (comp₌-cong (id₌ (Unit.target ⁻¹))
        (comp₌-assoc Unit.target Unit.lower fs ∙
          (comp₌-cong Unit.compatibility (id₌ fs) ∙
            (comp₌-assoc Unit.upper Unit.source fs) ⁻¹)))) ∙
      (comp₌-assoc (ft ⁻¹) (Unit.target ⁻¹) (Unit.upper ∙ Cs) ∙
        comp₌-cong (inverse-composite Unit.target ft) (id₌ (Unit.upper ∙ Cs)))
  lifted-square = post-square-cell V Ifirst Kfirst Tfirst Sfirst lifted-composite
  private
    as = comp-assoc Sfirst Tfirst V
    at = comp-assoc Ifirst Kfirst V
    cs = V ◁ Cs
    ct = V ◁ Ct
    g = V ◁ lifted
    W = ct ∙ at
    rest = as ∙ source-restrictions
    Rfull = g ∙ (cs ∙ rest)
    lift-image : (V ◁ lifted-composite) =₂ ((ct ⁻¹) ∙ (g ∙ cs))
    lift-image = comp₌-cong (postWhisker-inverse V Ct)
      (postWhisker-comp₌ V lifted Cs) ∙
        postWhisker-comp₌ V (Ct ⁻¹) (lifted ∙ Cs)
    coefficient-square : (W ∙ (target-restrictions ∙ N.E native)) =₂ Rfull
    coefficient-square = compatibility-with-product-coefficients ∙
      (comp₌-cong (comp₌-assoc ct at target-restrictions) (id₌ (N.E native)) ∙
        (comp₌-assoc W target-restrictions (N.E native)) ⁻¹)
    solved : (target-restrictions ∙ N.E native) =₂ ((W ⁻¹) ∙ Rfull)
    solved = comp₌-cong (id₌ (W ⁻¹)) coefficient-square ∙
      (inv-comp-left W (target-restrictions ∙ N.E native)) ⁻¹
    normalized-tail : ((W ⁻¹) ∙ Rfull) =₂ (lifted-square ∙ source-restrictions)
    normalized-tail = (comp₌-assoc (at ⁻¹) ((V ◁ lifted-composite) ∙ as)
      source-restrictions) ⁻¹ ∙
      (comp₌-cong (id₌ (at ⁻¹))
        ((comp₌-assoc (V ◁ lifted-composite) as source-restrictions) ⁻¹ ∙
          (comp₌-cong (lift-image ⁻¹) (id₌ rest) ∙
            ((comp₌-assoc (ct ⁻¹) (g ∙ cs) rest) ⁻¹ ∙
              comp₌-cong (id₌ (ct ⁻¹)) ((comp₌-assoc g cs rest) ⁻¹)))) ∙
        (comp₌-assoc (at ⁻¹) (ct ⁻¹) Rfull ∙
          comp₌-cong (inverse-composite ct at) (id₌ Rfull)))
  native-compatibility : (target-restrictions ∙ N.E native) =₂
    (lifted-square ∙ source-restrictions)
  native-compatibility = normalized-tail ∙ solved

module PathWord {Γ : Context} {X Y : CAT Γ} where
  append-three : {a b c d e : MAP X Y}
    (p : d =₁ e) (q : c =₁ d) (r : b =₁ c) (s : a =₁ b)
    → ((p ∙ (q ∙ r)) ∙ s) =₂ (p ∙ (q ∙ (r ∙ s)))
  append-three p q r s = comp₌-cong (id₌ p) (comp₌-assoc q r s) ∙
    comp₌-assoc p (q ∙ r) s
  append-four : {a b c d e f : MAP X Y}
    (p : e =₁ f) (q : d =₁ e) (r : c =₁ d) (s : b =₁ c) (t : a =₁ b)
    → ((p ∙ (q ∙ (r ∙ s))) ∙ t) =₂ (p ∙ (q ∙ (r ∙ (s ∙ t))))
  append-four p q r s t = comp₌-cong (id₌ p) (append-three q r s t) ∙
    comp₌-assoc p (q ∙ (r ∙ s)) t
  join-front : {a b c d e f : MAP X Y}
    (p : e =₁ f) (q : d =₁ e) (r : c =₁ d) (s : b =₁ c) (t : a =₁ b)
    → ((p ∙ q) ∙ (r ∙ (s ∙ t))) =₂ ((p ∙ ((q ∙ r) ∙ s)) ∙ t)
  join-front p q r s t = (append-three p (q ∙ r) s t) ⁻¹ ∙
    (comp₌-cong (id₌ p) ((comp₌-assoc q r (s ∙ t)) ⁻¹) ∙ comp₌-assoc p q (r ∙ (s ∙ t)))

module RestrictedFrameWord {Γ : Context} {K X T C : CAT Γ}
  (pi : MAP K C) (z : MAP X K) {b0 b1 b2 : MAP X C}
  (q : (pi ∘ z) =₁ b0) (c : b0 =₁ b1) (p : b1 =₁ b2) (r : MAP T X) where
  private
    A = (comp-assoc r z pi) ⁻¹
  compatibility : restrict-triangle pi z (p ∙ (c ∙ q)) r =₂
    ((p ▷ r) ∙ ((c ▷ r) ∙ restrict-triangle pi z q r))
  compatibility = PathWord.append-three (p ▷ r) (c ▷ r) (q ▷ r) A ∙
    comp₌-cong
      (comp₌-cong (id₌ (p ▷ r)) (preWhisker-comp₌ c q r) ∙
        preWhisker-comp₌ p (c ∙ q) r) (id₌ A)

```
