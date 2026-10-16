# Successive postcomposition with specified endpoint frames

Represent the original family by its uncurried diagram. Postcomposition
transports that same representation and its endpoint computations. The
comparison of two successive postcompositions with a prescribed composite
functor is therefore reflected from the corresponding diagram comparison.
Both endpoint equations use the original mapped-family frames.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.MorphismFamilyPostcompositionPasting where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-assoc; comp₌-cong; inv-comp-right; comp-inv-right; comp-inv-left;
    postWhisker-comp₌; preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; preWhisker-inverse; cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; post-triangle-outer)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; insert; evAt; MorphismFamily; MorphismFamilyIdentification; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.MorphismFunctor using (map-morphism-family)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations using (retarget-family; family-comparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.PostcompositionPointNaturality using (module PostcompositionPointsAt)
open import SCT.VolumeI.Chapter02.Section01.RepresentedDiagramPostcomposition
  using (module RepresentedDiagramPostcomposition)

private
  module ImagePoint {Γ : Context} {P C D : CAT Γ} (F : MAP C D)
    {u v : MAP P C} (alpha : MorphismFamily u v)
    (H : MAP (P × [1]) C) (beta : funUncurry (MorphismFamily.arrow alpha) =₁ H)
    (a : MAP One ([1] {Γ = Γ})) {x : MAP P C}
    (p : (H ∘ insert a) =₁ x)
    (frame : (evAt a ∘ MorphismFamily.arrow alpha) =₁ x)
    (given : (p ∙ ((beta ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow alpha))) =₂ frame) where
    private
      module R = RepresentedDiagramPostcomposition F (MorphismFamily.arrow alpha) H beta a
      module Points = PostcompositionPointsAt F (MorphismFamily.arrow alpha)
      image-p = F ◁ p
      original-point = R.original-point
      tail = R.point-tail
      assoc = R.input-assoc
      point = Points.point a
    compatibility : ((post-triangle F H (insert a) p) ∙ tail) =₂ ((F ◁ frame) ∙ point)
    compatibility = comp₌-cong
      ((postWhisker F ◁ given) ∙ (postWhisker-comp₌ F p original-point) ⁻¹)
      (id₌ point) ∙
      ((comp₌-assoc image-p (F ◁ original-point) point) ⁻¹ ∙
        (comp₌-cong (id₌ image-p) R.compatibility ∙ comp₌-assoc image-p assoc tail))

module Image {Γ : Context} {P C D : CAT Γ} (F : MAP C D)
  {x y : MAP P C} (alpha : MorphismFamily x y)
  (H : MAP (P × [1]) C) (beta : funUncurry (MorphismFamily.arrow alpha) =₁ H)
  (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y)
  (source : (p ∙ ((beta ▷ insert zero) ∙ AtPoint.uncurry-image zero (MorphismFamily.arrow alpha))) =₂
    MorphismFamily.source-frame alpha)
  (target : (q ∙ ((beta ▷ insert one) ∙ AtPoint.uncurry-image one (MorphismFamily.arrow alpha))) =₂
    MorphismFamily.target-frame alpha) where
  family : MorphismFamily (F ∘ x) (F ∘ y)
  family = map-morphism-family F alpha
  diagram : MAP (P × [1]) D
  diagram = F ∘ H
  representation : funUncurry (MorphismFamily.arrow family) =₁ diagram
  representation = RepresentedDiagramPostcomposition.representation F (MorphismFamily.arrow alpha) H beta zero
  first : (diagram ∘ insert zero) =₁ (F ∘ x)
  first = post-triangle F H (insert zero) p
  last : (diagram ∘ insert one) =₁ (F ∘ y)
  last = post-triangle F H (insert one) q
  first-image : (first ∙ ((representation ▷ insert zero) ∙ AtPoint.uncurry-image zero (MorphismFamily.arrow family))) =₂
    MorphismFamily.source-frame family
  first-image = ImagePoint.compatibility F alpha H beta zero p (MorphismFamily.source-frame alpha) source
  last-image : (last ∙ ((representation ▷ insert one) ∙ AtPoint.uncurry-image one (MorphismFamily.arrow family))) =₂
    MorphismFamily.target-frame family
  last-image = ImagePoint.compatibility F alpha H beta one q (MorphismFamily.target-frame alpha) target

private
  module DiagramPasting {Γ : Context} {P W B A D : CAT Γ}
    (i : MAP P W) (H : MAP W B) (r : MAP B A) (s : MAP A D) (t : MAP B D)
    (eta : (s ∘ r) =₁ t) {x : MAP P B} (p : (H ∘ i) =₁ x) where
    first = post-triangle r H i p
    twice = post-triangle s (r ∘ H) i first
    composite = post-triangle (s ∘ r) H i p
    output = post-triangle t H i p
    aH = comp-assoc H r s
    ax = comp-assoc x r s
    change = (eta ▷ x) ∙ ax ⁻¹
    diagram = (eta ▷ H) ∙ aH ⁻¹
    private
      aHi = aH ▷ i
      etaHi = (eta ▷ H) ▷ i
      etax = eta ▷ x
      assoc : (twice ∙ aHi) =₂ (ax ∙ composite)
      assoc = (post-triangle-comp s r H i p) ⁻¹ ∙
        comp₌-assoc (s ◁ first) (comp-assoc i (r ∘ H) s) aHi
      natural : (output ∙ etaHi) =₂ (etax ∙ composite)
      natural = unconst-sides₌ (post-triangle-outer eta H i p)
      moved : (composite ∙ aHi ⁻¹) =₂ (ax ⁻¹ ∙ twice)
      moved = cancel-left ax
        ((comp-inv-left ax twice) ⁻¹ ∙
          (comp-inv-right twice aHi ∙
            (comp₌-cong (assoc ⁻¹) (id₌ (aHi ⁻¹)) ∙
              (comp₌-assoc ax composite (aHi ⁻¹)) ⁻¹)))
    comparison : (output ∙ (diagram ▷ i)) =₂ (change ∙ twice)
    comparison = (comp₌-assoc etax (ax ⁻¹) twice) ⁻¹ ∙
      (comp₌-cong (id₌ etax) moved ∙
        (comp₌-assoc etax composite (aHi ⁻¹) ∙
          (comp₌-cong natural (id₌ (aHi ⁻¹)) ∙
            ((comp₌-assoc output etaHi (aHi ⁻¹)) ⁻¹ ∙
              comp₌-cong (id₌ output)
                (comp₌-cong (id₌ etaHi) (preWhisker-inverse aH i) ∙
                  preWhisker-comp₌ (eta ▷ H) (aH ⁻¹) i)))))

module ReflectedFrames {Γ : Context} {P C : CAT Γ} {x y : MAP P C}
  (alpha beta : MorphismFamily x y) (H : MAP (P × [1]) C)
  (a : funUncurry (MorphismFamily.arrow alpha) =₁ H)
  (b : funUncurry (MorphismFamily.arrow beta) =₁ H)
  (p : (H ∘ insert zero) =₁ x) (q : (H ∘ insert one) =₁ y)
  (asrc : (p ∙ ((a ▷ insert zero) ∙ AtPoint.uncurry-image zero (MorphismFamily.arrow alpha))) =₂ MorphismFamily.source-frame alpha)
  (atgt : (q ∙ ((a ▷ insert one) ∙ AtPoint.uncurry-image one (MorphismFamily.arrow alpha))) =₂ MorphismFamily.target-frame alpha)
  (bsrc : (p ∙ ((b ▷ insert zero) ∙ AtPoint.uncurry-image zero (MorphismFamily.arrow beta))) =₂ MorphismFamily.source-frame beta)
  (btgt : (q ∙ ((b ▷ insert one) ∙ AtPoint.uncurry-image one (MorphismFamily.arrow beta))) =₂ MorphismFamily.target-frame beta) where
  private
    module Lift = ReflectedEndpoint (MorphismFamily.arrow alpha) (MorphismFamily.arrow beta) H b a
    endpoint : (v : MAP One ([1] {Γ = Γ})) {z : MAP P C}
      (frame : (H ∘ insert v) =₁ z)
      (af : (evAt v ∘ MorphismFamily.arrow alpha) =₁ z)
      (bf : (evAt v ∘ MorphismFamily.arrow beta) =₁ z)
      → (frame ∙ ((a ▷ insert v) ∙ AtPoint.uncurry-image v (MorphismFamily.arrow alpha))) =₂ af
      → (frame ∙ ((b ▷ insert v) ∙ AtPoint.uncurry-image v (MorphismFamily.arrow beta))) =₂ bf
      → (bf ∙ (evAt v ◁ Lift.comparison)) =₂ af
    endpoint v frame af bf source target = source ∙
      (comp₌-cong (id₌ frame) (Lift.endpoint v) ∙
        (comp₌-assoc frame ((b ▷ insert v) ∙ AtPoint.uncurry-image v (MorphismFamily.arrow beta)) (evAt v ◁ Lift.comparison) ∙
          comp₌-cong (target ⁻¹) (id₌ (evAt v ◁ Lift.comparison))))
  value : MorphismFamilyIdentification One alpha beta
  value = family-comparison alpha beta Lift.comparison
    (endpoint zero p _ _ asrc bsrc) (endpoint one q _ _ atgt btgt)

module Pasting {Γ : Context} {P B A D : CAT Γ}
  (r : MAP B A) (s : MAP A D) (t : MAP B D) (eta : (s ∘ r) =₁ t)
  {x y : MAP P B} (alpha : MorphismFamily x y) where
  private
    module Original = MorphismFamily alpha
    U : MAP (P × [1]) B
    U = funUncurry Original.arrow
    identity = id₌ U
    base : (a : MAP One ([1] {Γ = Γ})) {z : MAP P B}
      → (evAt a ∘ Original.arrow) =₁ z → (U ∘ insert a) =₁ z
    base a frame = frame ∙ (AtPoint.uncurry-image a Original.arrow) ⁻¹
    base-image : (a : MAP One ([1] {Γ = Γ})) {z : MAP P B}
      (frame : (evAt a ∘ Original.arrow) =₁ z)
      → (base a frame ∙ ((identity ▷ insert a) ∙ AtPoint.uncurry-image a Original.arrow)) =₂ frame
    base-image a frame = inv-comp-right frame (AtPoint.uncurry-image a Original.arrow) ∙
      comp₌-cong (id₌ (base a frame))
        (comp₌-unitˡ-One (AtPoint.uncurry-image a Original.arrow) ∙
          comp₌-cong (preWhisker-id₌ U (insert a)) (id₌ (AtPoint.uncurry-image a Original.arrow)))
    p = base zero Original.source-frame
    q = base one Original.target-frame
    module First = Image r alpha U identity p q (base-image zero Original.source-frame) (base-image one Original.target-frame)
    module Second = Image s First.family First.diagram First.representation First.first First.last First.first-image First.last-image
    module Last = Image t alpha U identity p q (base-image zero Original.source-frame) (base-image one Original.target-frame)
    module Source = DiagramPasting (insert zero) U r s t eta p
    module Target = DiagramPasting (insert one) U r s t eta q
  source-change : (s ∘ (r ∘ x)) =₁ (t ∘ x)
  source-change = (eta ▷ x) ∙ (comp-assoc x r s) ⁻¹
  target-change : (s ∘ (r ∘ y)) =₁ (t ∘ y)
  target-change = (eta ▷ y) ∙ (comp-assoc y r s) ⁻¹
  private
    changed = retarget-family Second.family source-change target-change
    diagram-change : Second.diagram =₁ Last.diagram
    diagram-change = (eta ▷ U) ∙ (comp-assoc U r s) ⁻¹
    representation : funUncurry (MorphismFamily.arrow changed) =₁ Last.diagram
    representation = diagram-change ∙ Second.representation
    endpoint : (a : MAP One ([1] {Γ = Γ})) {v w : MAP P D}
      (before : (Second.diagram ∘ insert a) =₁ v)
      (after : (Last.diagram ∘ insert a) =₁ w)
      (change : v =₁ w)
      (mapped-frame : (evAt a ∘ MorphismFamily.arrow Second.family) =₁ v)
      (image : (before ∙ ((Second.representation ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow changed))) =₂
        mapped-frame)
      → (after ∙ (diagram-change ▷ insert a)) =₂ (change ∙ before)
      → (after ∙ ((representation ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow changed))) =₂
        (change ∙ mapped-frame)
    endpoint a before after change mapped-frame image square = comp₌-cong (id₌ change) image ∙
      (comp₌-assoc change before ((Second.representation ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow changed)) ∙
        (comp₌-cong square (id₌ ((Second.representation ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow changed))) ∙
          ((comp₌-assoc after (diagram-change ▷ insert a) ((Second.representation ▷ insert a) ∙ AtPoint.uncurry-image a (MorphismFamily.arrow changed))) ⁻¹ ∙
            (comp₌-cong (id₌ after) (comp₌-assoc (diagram-change ▷ insert a) (Second.representation ▷ insert a) (AtPoint.uncurry-image a (MorphismFamily.arrow changed))) ∙
              comp₌-cong (id₌ after) (comp₌-cong (preWhisker-comp₌ diagram-change Second.representation (insert a)) (id₌ (AtPoint.uncurry-image a (MorphismFamily.arrow changed))))))))
  comparison : MorphismFamilyIdentification One
    (retarget-family (map-morphism-family s (map-morphism-family r alpha)) source-change target-change)
    (map-morphism-family t alpha)
  comparison = ReflectedFrames.value changed Last.family Last.diagram representation Last.representation Last.first Last.last
    (endpoint zero Second.first Last.first source-change (MorphismFamily.source-frame Second.family) Second.first-image Source.comparison)
    (endpoint one Second.last Last.last target-change (MorphismFamily.target-frame Second.family) Second.last-image Target.comparison)
    Last.first-image Last.last-image
```
