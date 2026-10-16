# Compatibility of the native square corner with double currying

The actual reflected side comparisons are evaluated before comparing the
coordinate routes. Generic pasting retains every external associator. This
offsource draft is not yet reviewed or checked.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCornerCompatibility where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left; inv-comp-left; inv-comp-right;
    comp-inv-right; preWhisker-comp₌; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (paste-square₌; inverse-square₌; post-square₌; replace-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (cancel-left; preWhisker-inverse; postWhisker-inverse; inverse-composite)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (whisker-mixed-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-comp)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry-β; funUncurry)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-uncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (insert; evAt; evAt-pre; evAt-cong; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters using (module PointNaturality)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition
  using (module InsertionComposition; module PrecompositionPointEvaluation)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality
  using (module PostcompositionPointsAt)
open import SCT.VolumeI.Chapter02.Section01.RestrictedDiagramEvaluation
  using (module RestrictedDiagramEvaluation; parameter-square-image)
open import SCT.VolumeI.Chapter02.Section01.RepresentedDiagramPostcomposition
  using (module RepresentedDiagramPostcomposition)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert; module SquareCoordinates)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
open import SCT.VolumeI.Chapter02.Section02.SquareCurrying using (module SquareCurrying)
open import SCT.VolumeI.Chapter02.Section02.SquareCornerCoordinates using (module SquareCornerCoordinates)

private
  module _ {Γ : Context} where
    opaque
      paste-represented-interior : {B C : CAT Γ}
        {x₀ x₁ x₂ x₃ x₄ : MAP B C}
        (i : x₂ =₁ x₄) (middle : x₁ =₁ x₂) (u : x₀ =₁ x₁)
        (o : x₀ =₁ x₂) (E : x₃ =₁ x₄) (t : x₁ =₁ x₃)
        → (i ∙ middle) =₂ (E ∙ t)
        → (middle ∙ u) =₂ o
        → (i ∙ o) =₂ (E ∙ (t ∙ u))
      paste-represented-interior i middle u o E t inner outer =
        comp₌-assoc E t u ∙
          (comp₌-cong inner (id₌ u) ∙
            ((comp₌-assoc i middle u) ⁻¹ ∙
              comp₌-cong (id₌ i) (outer ⁻¹)))

    opaque
      framed-pasting : {B C : CAT Γ}
        {x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : MAP B C}
        (K : x₀ =₁ x₁) (middle : x₂ =₁ x₃) (action : x₆ =₁ x₇)
        (preH : x₀ =₁ x₂) (preV : x₁ =₁ x₃)
        (MH : x₂ =₁ x₆) (MV : x₃ =₁ x₇)
        (left : x₀ =₁ x₄) (right : x₁ =₁ x₅)
        (hframe : x₄ =₁ x₆) (vframe : x₅ =₁ x₇)
        → (preV ∙ K) =₂ (middle ∙ preH)
        → (MV ∙ middle) =₂ (action ∙ MH)
        → (MH ∙ preH) =₂ (hframe ∙ left)
        → (MV ∙ preV) =₂ (vframe ∙ right)
        → (vframe ∙ (right ∙ K)) =₂ ((action ∙ hframe) ∙ left)
      framed-pasting {B = B} {C = C} K middle action preH preV MH MV
        left right hframe vframe upper lower horizontal vertical =
        (comp₌-assoc action hframe left) ⁻¹ ∙
          (replace-sides₌ {X = One} {C = B} {D = C} horizontal vertical
            (paste-square₌ {X = One} {C = B} {D = C} upper lower) ∙
              (comp₌-assoc vframe right K) ⁻¹)

    pre-chain : {X Y Z : CAT Γ} {f g h : MAP Y Z} (alpha : g =₁ h) (beta : f =₁ g)
      (r : MAP X Y) {s : MAP X Z} (tail : s =₁ (f ∘ r))
      → (((alpha ∙ beta) ▷ r) ∙ tail) =₂ ((alpha ▷ r) ∙ ((beta ▷ r) ∙ tail))
    pre-chain alpha beta r tail = comp₌-assoc (alpha ▷ r) (beta ▷ r) tail ∙
      comp₌-cong (preWhisker-comp₌ alpha beta r) (id₌ tail)

    change-axes : {X Y K L C : CAT Γ} (D : MAP L C) (f : MAP X Y) (i : MAP X K)
      {F F' : MAP K L} {j j' : MAP Y L} (p : j =₁ j') (q : F =₁ F')
      (alpha : (j ∘ f) =₁ (F ∘ i)) (beta : (j' ∘ f) =₁ (F' ∘ i))
      → (beta ∙ (p ▷ f)) =₂ ((q ▷ i) ∙ alpha)
      → (post-square-cell D i F' j' f beta ∙ ((D ◁ p) ▷ f)) =₂
        (((D ◁ q) ▷ i) ∙ post-square-cell D i F j f alpha)
    change-axes D f i p q alpha beta square =
      paste-square₌ (paste-square₌ (whisker-mixed-One p f D) (post-square₌ D square))
        (inverse-square₌ (whisker-mixed-One q i D))
```

Postcomposition of the coordinate square respects the two axis frames.
Its two nested associators are supplied by the existing composition law
for post-square-cell.

```agda
private
  module EvaluatedCoordinates {Γ : Context} {P C : CAT Γ}
    (D : MAP (P × ([1] × [1])) C) (a b : MAP One ([1] {Γ = Γ})) where
    module Coordinates = SquareCoordinates P
    module H = Coordinates.Horizontal a
    module V = Coordinates.Vertical b
    module Corner = SquareCornerCoordinates P a b
    private
      J = Coordinates.permute
      ia = Corner.ia
      ib = Corner.ib
      chi = Corner.chi
      p = H.comparison ▷ ib
      q = V.comparison ▷ ia
      fourth = (comp-assoc ia V.step J) ⁻¹
      third = J ◁ chi
      second = comp-assoc ib H.step J
      E₀ = post-square-cell J ia V.step H.step ib chi
      E₁ = post-square-cell D ia (J ∘ V.step) (J ∘ H.step) ib E₀
      left-associator = comp-assoc H.step J D ▷ ib
      right-associator = comp-assoc V.step J D ▷ ia
      hhead = (D ◁ H.comparison) ▷ ib
      vhead = (D ◁ V.comparison) ▷ ia
      matching-normal : Corner.matching =₂ (q ∙ (E₀ ∙ p ⁻¹))
      matching-normal = comp₌-cong (id₌ q)
        ((comp₌-assoc fourth (third ∙ second) (p ⁻¹)) ⁻¹ ∙
          comp₌-cong (id₌ fourth) ((comp₌-assoc third second (p ⁻¹)) ⁻¹))
      matching-square : (Corner.matching ∙ p) =₂ (q ∙ E₀)
      matching-square = comp₌-cong (id₌ q) (inv-comp-right E₀ p) ∙
        (comp₌-assoc q (E₀ ∙ p ⁻¹) p ∙ comp₌-cong matching-normal (id₌ p))
    raw : (((D ∘ J) ∘ H.step) ∘ ib) =₁ (((D ∘ J) ∘ V.step) ∘ ia)
    raw = parameter-square-image {I = [1]} {C = C} {P = P × [1]} {Q = P}
      a (D ∘ J) ib
    result : ((D ∘ H.restriction) ∘ ib) =₁ ((D ∘ V.restriction) ∘ ia)
    result = post-square-cell D ia V.restriction H.restriction ib Corner.matching
    private
      axes : (result ∙ hhead) =₂ (vhead ∙ E₁)
      axes = change-axes D ib ia H.comparison V.comparison E₀ Corner.matching matching-square
      permutation : (E₁ ∙ left-associator) =₂ (right-associator ∙ raw)
      permutation = post-square-cell-comp ia V.step H.step ib chi J D
    compatibility : (vhead ∙ (right-associator ∙ raw)) =₂
      (result ∙ (hhead ∙ left-associator))
    compatibility = comp₌-assoc result hhead left-associator ∙
      (comp₌-cong (axes ⁻¹) (id₌ left-associator) ∙
        ((comp₌-assoc vhead E₁ left-associator) ⁻¹ ∙
          comp₌-cong (id₌ vhead) (permutation ⁻¹)))
```

The raw currying equation retains both reflected side comparisons, the
original curry betas, and the specified postcomposition point comparison.

```agda
module SquareCornerCompatibility {Γ : Context} {P C : CAT Γ}
  (sigma : MAP P (Fun ([1] × [1]) C)) (a b : MAP One ([1] {Γ = Γ})) where
  private
    I : CAT Γ
    I = [1]
    module S = SquareCurrying sigma
    module H = S.Horizontal a
    module V = S.Vertical b
    module Coordinates = SquareCoordinates P
    module HC = Coordinates.Horizontal a
    module VC = Coordinates.Vertical b
    module Corner = SquareCornerCoordinates P a b
    module Native = SquareCorner a b
    module Inner = RestrictedDiagramEvaluation a S.first-curry S.reordered
      (funCurry-β S.reordered) (insert b)
    module Outer = RepresentedDiagramPostcomposition (evAt {C = C} a)
      S.nested S.first-curry (funCurry-β S.first-curry) b
    module Evaluated = EvaluatedCoordinates S.diagram a b
    ia = Corner.ia
    ib = Corner.ib
    qH : funUncurry {C = I} {D = C} H.side =₁ (S.diagram ∘ HC.restriction)
    qH = H.beta
    qV = V.beta
    aH = comp-assoc HC.step Coordinates.permute S.diagram
    aV = comp-assoc VC.step Coordinates.permute S.diagram
    headH = S.diagram ◁ HC.comparison
    headV = S.diagram ◁ VC.comparison
    curry-edge = Inner.original-point
    thetaH : funUncurry {C = I} {D = C} H.evaluated =₁ (S.diagram ∘ HC.restriction)
    thetaH = H.theta
    thetaV = V.theta
    left = (qH ▷ ib) ∙ AtPoint.uncurry-image b H.side
    right = (qV ▷ ia) ∙ AtPoint.uncurry-image a V.side
    outer-endpoint = AtPoint.uncurry-image b H.evaluated
    inner-endpoint = AtPoint.uncurry-image a (S.first-curry ∘ ib)
    outer-tail = Outer.point-tail
    inner-tail = Inner.point
    mu = PostcompositionPointsAt.point (evAt {C = C} a) S.nested b
    outer-boundary = Outer.native
    boundary = (evAt a ◁ V.boundary) ∙ mu
    top = curry-edge ▷ ib
    middle = Inner.input-assoc
    vhead = headV ▷ ia
    va = aV ▷ ia
    hhead = headH ▷ ib
    ha = aH ▷ ib
    Hb = (thetaH ▷ ib) ∙ outer-endpoint
    Va = (thetaV ▷ ia) ∙ inner-endpoint
    h-axis = (headH ∙ aH) ▷ ib
    v-axis = (headV ∙ aV) ▷ ia
    U = ((curry-edge ∙ Outer.representation) ▷ ib) ∙ outer-endpoint
    W = inner-tail

    horizontal-raw : (left ∙ (evAt {C = C} b ◁ H.comparison)) =₂ Hb
    horizontal-raw = H.Comparison.endpoint b
    vertical-raw : (right ∙ (evAt a ◁ V.Comparison.comparison)) =₂ Va
    vertical-raw = V.Comparison.endpoint a
    boundary-image : (right ∙ boundary) =₂ (Va ∙ outer-boundary)
    boundary-image = comp₌-cong vertical-raw (id₌ outer-boundary) ∙
      ((comp₌-assoc right (evAt a ◁ V.Comparison.comparison) outer-boundary) ⁻¹ ∙
        comp₌-cong (id₌ right)
          (comp₌-assoc (evAt a ◁ V.Comparison.comparison)
            (evAt a ◁ AtPoint.curry-image b S.first-curry) mu ∙
              comp₌-cong (postWhisker-comp₌ (evAt a) V.Comparison.comparison
                (AtPoint.curry-image b S.first-curry)) (id₌ mu)))
    inner-owned-cell : (Inner.point ∙ Inner.input-assoc) =₂
      (Inner.diagram-route ∙ (Inner.original-point ▷ ib))
    inner-owned-cell = Inner.compatibility
    outer-owned-cell : (Outer.input-assoc ∙ Outer.point-tail) =₂ Outer.native
    outer-owned-cell = Outer.compatibility
    middle-owner-join : Inner.input-assoc =₂ Outer.input-assoc
    middle-owner-join = id₌ Inner.input-assoc
    outer-cell-for-inner : (Inner.input-assoc ∙ Outer.point-tail) =₂ Outer.native
    outer-cell-for-inner = outer-owned-cell ∙
      comp₌-cong middle-owner-join (id₌ Outer.point-tail)
    owned-interior : (Inner.point ∙ Outer.native) =₂
      (Inner.diagram-route ∙ ((Inner.original-point ▷ ib) ∙ Outer.point-tail))
    owned-interior = paste-represented-interior {B = P} {C = C}
      Inner.point Inner.input-assoc Outer.point-tail Outer.native
      Inner.diagram-route (Inner.original-point ▷ ib)
      inner-owned-cell outer-cell-for-inner
    interior : (inner-tail ∙ outer-boundary) =₂ (Evaluated.raw ∙ (top ∙ outer-tail))
    interior = owned-interior

    horizontal-group : Hb =₂ (h-axis ∙ U)
    horizontal-group = H.representation-group b
    vertical-group : Va =₂ (v-axis ∙ W)
    vertical-group = V.representation-group a
    represented-interior : (W ∙ outer-boundary) =₂ (Evaluated.raw ∙ U)
    represented-interior = comp₌-cong (id₌ Evaluated.raw)
      ((pre-chain curry-edge Outer.representation ib outer-endpoint) ⁻¹) ∙ interior
    represented-axes : (v-axis ∙ Evaluated.raw) =₂ (Evaluated.result ∙ h-axis)
    represented-axes = comp₌-cong (id₌ Evaluated.result)
      ((preWhisker-comp₌ headH aH ib) ⁻¹) ∙
      (Evaluated.compatibility ∙
        (comp₌-assoc vhead va Evaluated.raw ∙
          comp₌-cong (preWhisker-comp₌ headV aV ia) (id₌ Evaluated.raw)))
    represented-corner : (Va ∙ outer-boundary) =₂ (Evaluated.result ∙ Hb)
    represented-corner = replace-sides₌ {X = One} {C = P} {D = C}
      (horizontal-group ⁻¹) (vertical-group ⁻¹)
      (paste-square₌ {X = One} {C = P} {D = C} represented-interior represented-axes)
    currying-image : (right ∙ boundary) =₂
      (Evaluated.result ∙ (left ∙ (evAt b ◁ H.comparison)))
    currying-image = comp₌-cong (id₌ Evaluated.result) (horizontal-raw ⁻¹) ∙
      (represented-corner ∙ boundary-image)

    module NativeEvaluation = Native.Evaluated C
    module Shape = InsertionComposition P
    module HPre = PrecompositionPointEvaluation {C = C} b (coinsert a) sigma
    module VPre = PrecompositionPointEvaluation {C = C} a (insert {P = I} b) sigma
    module Point = PointNaturality sigma
    K = Cone.match (NativeEvaluation.at-family sigma)
    p = evAt-pre {C = C} b (coinsert a)
    q = evAt-pre {C = C} a (insert {P = I} b)
    corner-evaluation = evAt-cong {C = C} Native.corner
    ps = p ▷ sigma
    qs = q ▷ sigma
    ms = corner-evaluation ▷ sigma
    aL = comp-assoc sigma (funPre {D = C} (coinsert a)) (evAt b)
    aR = comp-assoc sigma (funPre {D = C} (insert {P = I} b)) (evAt a)
    preH = ps ∙ aL ⁻¹
    preV = qs ∙ aR ⁻¹
    tau = q ⁻¹ ∙ (corner-evaluation ∙ p)
    MH = AtPoint.uncurry-image (coinsert a ∘ b) sigma
    MV = AtPoint.uncurry-image (insert {P = I} b ∘ a) sigma
    sh = Shape.χ (coinsert a) b
    sv = Shape.χ (insert {P = I} b) a
    dh = S.diagram ◁ sh
    dv = S.diagram ◁ sv
    point-action = S.diagram ◁ Corner.point-action
    ah = comp-assoc ib HC.restriction S.diagram
    av = comp-assoc ia VC.restriction S.diagram
    h-frame = dh ∙ ah
    v-frame = dv ∙ av

    matching-image : (tau ▷ sigma) =₂ (qs ⁻¹ ∙ (ms ∙ ps))
    matching-image = comp₌-cong (preWhisker-inverse q sigma) (preWhisker-comp₌ corner-evaluation p sigma) ∙
      preWhisker-comp₌ (q ⁻¹) (corner-evaluation ∙ p) sigma
    clear-frames : (preV ∙ K) =₂ (ms ∙ preH)
    clear-frames = comp₌-assoc ms ps (aL ⁻¹) ∙
      (comp₌-cong (comp-inv-left qs (ms ∙ ps)) (id₌ (aL ⁻¹)) ∙
        ((comp₌-assoc qs (qs ⁻¹ ∙ (ms ∙ ps)) (aL ⁻¹)) ⁻¹ ∙
          (comp₌-cong (id₌ qs) (comp₌-cong matching-image (id₌ (aL ⁻¹))) ∙
            (comp₌-cong (id₌ qs) (inv-comp-left aR ((tau ▷ sigma) ∙ aL ⁻¹)) ∙
              comp₌-assoc qs (aR ⁻¹) K))))
    horizontal-pre : (MH ∙ preH) =₂ (h-frame ∙ left)
    horizontal-pre = (comp₌-assoc dh ah left) ⁻¹ ∙ HPre.compatibility
    vertical-pre : (MV ∙ preV) =₂ (v-frame ∙ right)
    vertical-pre = (comp₌-assoc dv av right) ⁻¹ ∙ VPre.compatibility
    point-square : (MV ∙ ms) =₂ (point-action ∙ MH)
    point-square = Point.uncurry-point-square Native.corner

    native-image-boundary : (v-frame ∙ (right ∙ K)) =₂ ((point-action ∙ h-frame) ∙ left)
    native-image-boundary = framed-pasting
      K ms point-action preH preV MH MV left right h-frame v-frame
      clear-frames point-square horizontal-pre vertical-pre

    native-route = v-frame ⁻¹ ∙ (point-action ∙ h-frame)
    cancel-native : (v-frame ∙ (native-route ∙ left)) =₂ ((point-action ∙ h-frame) ∙ left)
    cancel-native = comp₌-cong (comp-inv-left v-frame (point-action ∙ h-frame)) (id₌ left) ∙
      (comp₌-assoc v-frame native-route left) ⁻¹
    native-cancelled : (right ∙ K) =₂ (native-route ∙ left)
    native-cancelled = cancel-left v-frame (cancel-native ⁻¹ ∙ native-image-boundary)

    native-word : (S.diagram ◁ Corner.native) =₂ (dv ⁻¹ ∙ (point-action ∙ dh))
    native-word = comp₌-cong (postWhisker-inverse S.diagram sv)
      (postWhisker-comp₌ S.diagram Corner.point-action sh) ∙
        postWhisker-comp₌ S.diagram (sv ⁻¹) (Corner.point-action ∙ sh)
    native-result = post-square-cell S.diagram ia VC.restriction HC.restriction ib Corner.native
    native-route-image : native-route =₂ native-result
    native-route-image = comp₌-cong (id₌ (av ⁻¹))
      (comp₌-cong (native-word ⁻¹) (id₌ ah) ∙
        ((comp₌-assoc (dv ⁻¹) (point-action ∙ dh) ah) ⁻¹ ∙
          comp₌-cong (id₌ (dv ⁻¹)) ((comp₌-assoc point-action dh ah) ⁻¹))) ∙
      (comp₌-assoc (av ⁻¹) (dv ⁻¹) (point-action ∙ h-frame) ∙
        comp₌-cong (inverse-composite dv av) (id₌ (point-action ∙ h-frame)))
    native-image : (right ∙ K) =₂ (native-result ∙ left)
    native-image = comp₌-cong native-route-image (id₌ left) ∙ native-cancelled

    coordinate-image : Evaluated.result =₂ native-result
    coordinate-image = comp₌-cong (id₌ (av ⁻¹))
      (comp₌-cong (postWhisker S.diagram ◁ Corner.coordinate-agreement) (id₌ ah))
    native-joined : (right ∙ (K ∙ (evAt b ◁ H.comparison))) =₂
      (native-result ∙ (left ∙ (evAt b ◁ H.comparison)))
    native-joined = comp₌-assoc native-result left (evAt b ◁ H.comparison) ∙
      (comp₌-cong native-image (id₌ (evAt b ◁ H.comparison)) ∙
        (comp₌-assoc right K (evAt b ◁ H.comparison)) ⁻¹)

  compatibility :
    (Cone.match (NativeEvaluation.at-family sigma) ∙ (evAt b ◁ H.comparison)) =₂
      ((evAt a ◁ V.boundary) ∙ PostcompositionPointsAt.point (evAt {C = C} a) S.nested b)
  compatibility = (cancel-left right
    (native-joined ⁻¹ ∙
      (comp₌-cong coordinate-image (id₌ (left ∙ (evAt b ◁ H.comparison))) ∙ currying-image))) ⁻¹
```
