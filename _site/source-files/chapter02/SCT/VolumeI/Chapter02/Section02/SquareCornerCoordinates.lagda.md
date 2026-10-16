# The two actual coordinate pastings at a square corner

This offsource candidate derives equality of the two coordinate pastings
by their parameter and rectangle projections, retaining the original insertion
and vertex comparisons. The complete draft awaits independent review and
Agda checking. It does not derive the evaluated corner law.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCornerCoordinates where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const; terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc; comp-inv-left; const-pre; postWhisker-comp₌;
    preWhisker-comp₌; inv-comp-right; const-One; const-evaluate; comp-inv-right)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (postWhisker-inverse; cancel-right; cancel-left; comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; post-triangle-outer; post-triangle-id; lies-over-comp; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; compose-triangle; compatible-comp; compatible-inverse;
    compatible-pre; compatible-post; compatible-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-id-One; identity-unitors; right-unitor-comp;
    triangle-whiskered; whisker-mixed-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (const-pre-change; const-pre-iterated; unit-corner)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation
  using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-triangle₁-One; pair⁼-triangle₂-One; pair⁼-cong; pair⁼-comp; pair⁼-id-One;
    pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One;
    pair-pre-iterated; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1])
open import SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames
  using (pair-action-image; module PairedBaseImage)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module ParameterInsertion)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition using (module InsertionComposition)
open import SCT.VolumeI.Chapter02.Section01.InsertionSectionEvaluation
  using (module InsertionSectionEvaluation)
open import SCT.VolumeI.Chapter02.Section02.SquareCoordinates using (coinsert; module SquareCoordinates)
open import SCT.VolumeI.Chapter02.Section02.SquareCorners using (module SquareCorner)
```

Evaluation along a section is natural in its evaluated functor. At the
identity, its value is the original section triangle with the left unitor.
These two equations normalize the parameter frame without changing it.

```agda
private
  module SectionFrames {Γ : Context} {X K : CAT Γ}
    (pi : MAP K X) (i : MAP X K) (b : (pi ∘ i) =₁ id X) where
    module E = SectionEvaluation pi i b
    natural : {Y : CAT Γ} {f g : MAP X Y} (p : f =₁ g)
      → (E.image g ∙ ((p ▷ pi) ▷ i)) =₂ (p ∙ E.image f)
    natural p = paste-square₌ (unconst-sides₌ (post-triangle-outer p pi i b))
      (preWhisker-id-One p)
    identity : E.image (id X) =₂ (b ∙ (comp-unitˡ pi ▷ i))
    identity = post-triangle-id pi i b ∙
      comp₌-cong (identity-unitors X) (id₌ (post-triangle (id X) pi i b))

    collapsed : {f : MAP X X} (p : f =₁ id X)
      → ((b ∙ (comp-unitˡ pi ▷ i)) ∙ ((p ▷ pi) ▷ i)) =₂ (p ∙ E.image f)
    collapsed p = natural p ∙ comp₌-cong (identity ⁻¹) (id₌ ((p ▷ pi) ▷ i))

    constant : {Y : CAT Γ} (x : MAP One Y)
      → E.image (const {P = X} x) =₂ (const-pre x i ∙ (const-pre x pi ▷ i))
    constant x = const-pre-change x pi i (id X) b ∙
      comp₌-cong (constant-id ⁻¹) (id₌ (post-triangle (const x) pi i b))
      where
        constant-id : const-pre {R = X} {X = X} x (id X) =₂ comp-unitʳ (const {P = X} x)
        constant-id = (right-unitor-comp (terminate X) x) ⁻¹ ∙
          comp₌-cong
            (postWhisker x ◁ terminal-unique₂
              (terminal-identification (terminate X ∘ id X) (terminate X))
              (comp-unitʳ (terminate X)))
            (id₌ (comp-assoc (id X) (terminate X) x))

    constant-collapsed : {Y : CAT Γ} {f : MAP X Y} (x : MAP One Y)
      (p : f =₁ const x)
      → ((const-pre x i ∙ (const-pre x pi ▷ i)) ∙ ((p ▷ pi) ▷ i)) =₂
        (p ∙ E.image f)
    constant-collapsed x p = natural p ∙
      comp₌-cong (constant x ⁻¹) (id₌ ((p ▷ pi) ▷ i))
```

The quotient of the paired front and back evaluations retains both coordinate
frames. This is the same cancellation for each projection; the second
projection is needed to track the inner coordinate of the currying permutation.

```agda
module InsertionProjections {Γ : Context} {I P Q : CAT Γ}
  (a : MAP One I) (r : MAP Q P) where
  private
    module N = ParameterInsertion a
    i : MAP Q (Q × I)
    i = insert a
    first = post-triangle r pr₁ i (pair-β₁ (id Q) (const a))
    second = post-triangle (id I) pr₂ i (pair-β₂ (id Q) (const a))

  incoming₁ : (pr₁ ∘ (insert a ∘ r)) =₁ r
  incoming₁ = comp-unitˡ r ∙ project-pair₁ (id P) (const a) r
  incoming₂ : (pr₂ ∘ (insert a ∘ r)) =₁ const a
  incoming₂ = const-pre a r ∙ project-pair₂ (id P) (const a) r
  outgoing₁ : (pr₁ ∘ (productMap r (id I) ∘ i)) =₁ r
  outgoing₁ = (comp-unitʳ r ∙ first) ∙
    project-pair₁ (r ∘ pr₁) (id I ∘ pr₂) i
  outgoing₂ : (pr₂ ∘ (productMap r (id I) ∘ i)) =₁ const a
  outgoing₂ = (comp-unitˡ (const a) ∙ second) ∙
    project-pair₂ (r ∘ pr₁) (id I ∘ pr₂) i

  private
    front-image₁ : (pair-β₁ r (const a) ∙ (pr₁ ◁ N.front r)) =₂ incoming₁
    front-image₁ = pair-evaluation-over₁-One (id P) (const a) r
      (comp-unitˡ r) (const-pre a r)
    front-image₂ : (pair-β₂ r (const a) ∙ (pr₂ ◁ N.front r)) =₂ incoming₂
    front-image₂ = pair-evaluation-over₂-One (id P) (const a) r
      (comp-unitˡ r) (const-pre a r)
    back-image₁ : (pair-β₁ r (const a) ∙ (pr₁ ◁ N.back r)) =₂ outgoing₁
    back-image₁ = lies-over-comp pr₁
      (pair-evaluation-over₁-One (r ∘ pr₁) (id I ∘ pr₂) i first second)
      (pair⁼-triangle₁-One (comp-unitʳ r) (comp-unitˡ (const a)))
    back-image₂ : (pair-β₂ r (const a) ∙ (pr₂ ◁ N.back r)) =₂ outgoing₂
    back-image₂ = lies-over-comp pr₂
      (pair-evaluation-over₂-One (r ∘ pr₁) (id I ∘ pr₂) i first second)
      (pair⁼-triangle₂-One (comp-unitʳ r) (comp-unitˡ (const a)))

    quotient-projection : {B : CAT Γ} (pi : MAP (P × I) B)
      {z : MAP Q B} (common : (pi ∘ pair r (const a)) =₁ z)
      (incoming : (pi ∘ (insert a ∘ r)) =₁ z)
      (outgoing : (pi ∘ (productMap r (id I) ∘ i)) =₁ z)
      → (common ∙ (pi ◁ N.front r)) =₂ incoming
      → (common ∙ (pi ◁ N.back r)) =₂ outgoing
      → (outgoing ∙ (pi ◁ N.value r)) =₂ incoming
    quotient-projection pi common incoming outgoing front-image back-image =
      front-image ∙
        (comp₌-cong (id₌ common) (comp-inv-left back front) ∙
          (comp₌-assoc common back (back ⁻¹ ∙ front) ∙
            comp₌-cong (back-image ⁻¹) quotient-image))
      where
        front = pi ◁ N.front r
        back = pi ◁ N.back r
        quotient-image : (pi ◁ N.value r) =₂ (back ⁻¹ ∙ front)
        quotient-image = comp₌-cong (postWhisker-inverse pi (N.back r)) (id₌ front) ∙
          postWhisker-comp₌ pi (N.back r ⁻¹) (N.front r)

  projection₁ : (outgoing₁ ∙ (pr₁ ◁ N.value r)) =₂ incoming₁
  projection₁ = quotient-projection pr₁ (pair-β₁ r (const a))
    incoming₁ outgoing₁ front-image₁ back-image₁
  projection₂ : (outgoing₂ ∙ (pr₂ ◁ N.value r)) =₂ incoming₂
  projection₂ = quotient-projection pr₂ (pair-β₂ r (const a))
    incoming₂ outgoing₂ front-image₂ back-image₂
```

The native shape-insertion triangle retains the normalized parameter frame.
The first-coordinate unitor is normalized by the already proved actual
InsertionComposition.At law.

```agda
private
  module ShapeParameter {Γ : Context} (P : CAT Γ) {I J : CAT Γ}
    (f : MAP I J) (a : MAP One I) where
    module Shape = InsertionComposition P
    module At = Shape.At f a
    private
      i : MAP P (P × I)
      i = insert a
      beta = pair-β₁ (id P) (const {P = P} a)
      L = comp-unitˡ (pr₁ {C = P} {D = I}) ▷ i
      B = Shape.b₁ f ▷ i
      A = (comp-assoc i (Shape.J f) (pr₁ {C = P} {D = J})) ⁻¹
      projected = project-pair₁ Shape.q (f ∘ pr₂) i
    before : (pr₁ ∘ (Shape.J f ∘ i)) =₁ id P
    before = compose-triangle pr₁ (Shape.J f)
      (comp-unitˡ pr₁ ∙ Shape.b₁ f) i beta
    after : (pr₁ ∘ insert {P = P} (f ∘ a)) =₁ id P
    after = pair-β₁ (id P) (const (f ∘ a))
    private
      normalize : before =₂ (At.first ∙ projected)
      normalize = comp₌-cong (At.first-normalization ⁻¹) (id₌ projected) ∙
        ((comp₌-assoc beta L projected) ⁻¹ ∙
          comp₌-cong (id₌ beta)
            (comp₌-assoc L B A ∙
              comp₌-cong (preWhisker-comp₌ (comp-unitˡ pr₁) (Shape.b₁ f) i) (id₌ A)))
    compatibility : CompatibleOver pr₁ before after (Shape.χ f a)
    compatibility = normalize ⁻¹ ∙ At.projection₁
```

A composite of paired frames is the pairing of the two composite frames.
The calculation uses the original pair-pre comparisons and their actual
iterated-restriction law.

```agda
private
  module PairedCompositeFrame {Γ : Context} {X R Q C D : CAT Γ}
    (f : MAP X C) (g : MAP X D) (r : MAP R X) (s : MAP Q R)
    {x : MAP R C} {y : MAP R D} {z : MAP Q C} {w : MAP Q D}
    (u : (f ∘ r) =₁ x) (v : (g ∘ r) =₁ y)
    (p : (x ∘ s) =₁ z) (q : (y ∘ s) =₁ w) where
    private
      old = pair⁼ u v ∙ pair-pre f g r
      side = pair⁼ p q ∙ pair-pre x y s
      us = u ▷ s
      vs = v ▷ s
      af = comp-assoc s r f
      ag = comp-assoc s r g
      ap = comp-assoc s r (pair f g)
      first = p ∙ restrict-triangle f r u s
      second = q ∙ restrict-triangle g r v s
      before = pair⁼ first second
      units = pair⁼ af ag
      combined = pair⁼ (p ∙ us) (q ∙ vs)
      finish = pair⁼ p q
      pair-s = pair⁼ us vs
      old-s = pair⁼ u v ▷ s
      side-pre = pair-pre x y s
      b₀ = pair-pre f g r ▷ s
      b₁ = pair-pre (f ∘ r) (g ∘ r) s
      b₂ = pair-pre f g (r ∘ s)
    composed : (pair f g ∘ (r ∘ s)) =₁ pair z w
    composed = side ∙ restrict-triangle (pair f g) r old s
    direct : (pair f g ∘ (r ∘ s)) =₁ pair z w
    direct = before ∙ b₂
    private
      first-normal : (first ∙ af) =₂ (p ∙ us)
      first-normal = comp₌-cong (id₌ p) (inv-comp-right us af) ∙
        comp₌-assoc p (us ∙ af ⁻¹) af
      second-normal : (second ∙ ag) =₂ (q ∙ vs)
      second-normal = comp₌-cong (id₌ q) (inv-comp-right vs ag) ∙
        comp₌-assoc q (vs ∙ ag ⁻¹) ag
      join-normal : (before ∙ units) =₂ combined
      join-normal = pair⁼-cong first-normal second-normal ∙
        (pair⁼-comp first af second ag) ⁻¹
      direct-expanded : (direct ∙ ap) =₂ (combined ∙ (b₁ ∙ b₀))
      direct-expanded = comp₌-cong join-normal (id₌ (b₁ ∙ b₀)) ∙
        ((comp₌-assoc before units (b₁ ∙ b₀)) ⁻¹ ∙
          (comp₌-cong (id₌ before) (pair-pre-iterated f g r s) ∙
            comp₌-assoc before b₂ ap))
      middle-normal : (side ∙ old-s) =₂ ((finish ∙ pair-s) ∙ b₁)
      middle-normal = (comp₌-assoc finish pair-s b₁) ⁻¹ ∙
        (comp₌-cong (id₌ finish) (pair-pre-natural-inputs-One u v s) ∙
          comp₌-assoc finish side-pre old-s)
      common-expanded : (side ∙ (old ▷ s)) =₂ (combined ∙ (b₁ ∙ b₀))
      common-expanded = comp₌-assoc combined b₁ b₀ ∙
        (comp₌-cong (comp₌-cong ((pair⁼-comp p us q vs) ⁻¹) (id₌ b₁)) (id₌ b₀) ∙
          (comp₌-cong middle-normal (id₌ b₀) ∙
            ((comp₌-assoc side old-s b₀) ⁻¹ ∙
              comp₌-cong (id₌ side) (preWhisker-comp₌ (pair⁼ u v) (pair-pre f g r) s))))
      composed-expanded : (composed ∙ ap) =₂ (side ∙ (old ▷ s))
      composed-expanded = comp₌-cong (id₌ side) (inv-comp-right (old ▷ s) ap) ∙
        comp₌-assoc side ((old ▷ s) ∙ ap ⁻¹) ap
    compatibility : composed =₂ direct
    compatibility = cancel-right ap
      (direct-expanded ⁻¹ ∙ (common-expanded ∙ composed-expanded))
```

The original paired triangle is transparent. Its compatibility with
composition is one ordinary theorem, proved at generic arguments before
specialization. Concrete callers supply the original coordinate triangles;
they do not instantiate the module of intermediate proof calculations.

```agda
private
  module _ {Γ : Context} where
    paired-triangle : {X R C D : CAT Γ}
      (f : MAP X C) (g : MAP X D) (r : MAP R X)
      {x : MAP R C} {y : MAP R D}
      → (f ∘ r) =₁ x → (g ∘ r) =₁ y → (pair f g ∘ r) =₁ pair x y
    paired-triangle f g r u v = pair⁼ u v ∙ pair-pre f g r

    opaque
      pairing-compose-triangle : {X R Q C D : CAT Γ}
        (f : MAP X C) (g : MAP X D) (r : MAP R X) (s : MAP Q R)
        {x : MAP R C} {y : MAP R D} {z : MAP Q C} {w : MAP Q D}
        (u : (f ∘ r) =₁ x) (v : (g ∘ r) =₁ y)
        (p : (x ∘ s) =₁ z) (q : (y ∘ s) =₁ w)
        → compose-triangle (pair f g) r (paired-triangle f g r u v) s
            (paired-triangle x y s p q) =₂
          paired-triangle f g (r ∘ s)
            (compose-triangle f r u s p) (compose-triangle g r v s q)
      pairing-compose-triangle f g r s u v p q =
        PairedCompositeFrame.compatibility f g r s u v p q
```

Restricting an evaluated constant point gives the specified constant
restriction. Terminal uniqueness supplies the only comparison of terminal
triangles used here.

```agda
private
  module ConstantPointRestriction {Γ : Context} (P : CAT Γ) {X Y : CAT Γ}
    (x : MAP One X) (b : MAP One Y) where
    private
      t : MAP P (One {Γ = Γ})
      t = terminate P
      delta : (terminate (One {Γ = Γ})) =₁ (id (One {Γ = Γ}))
      delta = terminal-identification (terminate (One {Γ = Γ})) (id (One {Γ = Γ}))
      L : (x ∘ (id (One {Γ = Γ}) ∘ t)) =₁ (x ∘ t)
      L = x ◁ comp-unitˡ t
      M : ((x ∘ id (One {Γ = Γ})) ∘ t) =₁ (x ∘ (id (One {Γ = Γ}) ∘ t))
      M = comp-assoc t (id One) x
      N : ((x ∘ terminate (One {Γ = Γ})) ∘ t) =₁ ((x ∘ id (One {Γ = Γ})) ∘ t)
      N = (x ◁ delta) ▷ t
      B : (x ∘ (terminate (One {Γ = Γ}) ∘ t)) =₁ (x ∘ (id (One {Γ = Γ}) ∘ t))
      B = x ◁ (delta ▷ t)
      C : ((x ∘ terminate (One {Γ = Γ})) ∘ t) =₁ (x ∘ (terminate (One {Γ = Γ}) ∘ t))
      C = comp-assoc t (terminate One) x
      terminal-normal : (comp-unitˡ t ∙ (delta ▷ t)) =₂
        terminal-identification (terminate (One {Γ = Γ}) ∘ t) t
      terminal-normal = terminal-unique₂
        (comp-unitˡ t ∙ (delta ▷ t))
        (terminal-identification (terminate One ∘ t) t)
      one-restriction : (const-One x ▷ t) =₂ const-pre x t
      one-restriction = comp₌-cong (postWhisker x ◁ terminal-normal) (id₌ C) ∙
        (comp₌-cong ((postWhisker-comp₌ x (comp-unitˡ t) (delta ▷ t)) ⁻¹) (id₌ C) ∙
          ((comp₌-assoc L B C) ⁻¹ ∙
            (comp₌-cong (id₌ L) (whisker-mixed-One delta t x) ∙
              (comp₌-assoc L M N ∙
                (comp₌-cong (triangle-whiskered t x) (id₌ N) ∙
                  preWhisker-comp₌ (comp-unitʳ x) (x ◁ delta) t)))))
      A = comp-assoc t b (const {P = Y} x)
      evaluated-image : (const-evaluate x b ▷ t) =₂
        (const-pre x t ∙ (const-pre x b ▷ t))
      evaluated-image = comp₌-cong one-restriction (id₌ (const-pre x b ▷ t)) ∙
        preWhisker-comp₌ (const-One x) (const-pre x b) t
    compatibility : restrict-triangle (const {P = Y} x) b (const-evaluate x b) t =₂
      const-pre x (const {P = P} b)
    compatibility = comp-inv-right (const-pre x (const {P = P} b)) A ∙
      (comp₌-cong ((const-pre-iterated x b t) ⁻¹) (id₌ (A ⁻¹)) ∙
        comp₌-cong evaluated-image (id₌ (A ⁻¹)))

  module PairedPointRestriction {Γ : Context} (P : CAT Γ) {I C D : CAT Γ}
    (f : MAP I C) (g : MAP I D) (b : MAP One I)
    {x : MAP One C} {y : MAP One D}
    (u : (f ∘ b) =₁ x) (v : (g ∘ b) =₁ y)
    (U : (f ∘ const {P = P} b) =₁ const x)
    (V : (g ∘ const {P = P} b) =₁ const y)
    (first : restrict-triangle f b u (terminate P) =₂ U)
    (second : restrict-triangle g b v (terminate P) =₂ V) where
    private
      t = terminate P
      module Pairing = PairedCompositeFrame f g b t u v
        (id₌ (const {P = P} x)) (id₌ (const {P = P} y))
      vertex = pair⁼ u v ∙ pair-pre f g b
      pair-at-point = pair-pre x y t
      A = comp-assoc t b (pair f g)
      side = pair⁼ (id₌ (const {P = P} x)) (id₌ (const {P = P} y)) ∙ pair-at-point
      side-normal : side =₂ pair-at-point
      side-normal = comp₌-unitˡ-One pair-at-point ∙
        comp₌-cong (pair⁼-id-One (const {P = P} x) (const {P = P} y)) (id₌ pair-at-point)
      composed-normal : Pairing.composed =₂
        ((pair-at-point ∙ (vertex ▷ t)) ∙ A ⁻¹)
      composed-normal = (comp₌-assoc pair-at-point (vertex ▷ t) (A ⁻¹)) ⁻¹ ∙
        comp₌-cong side-normal (id₌ (restrict-triangle (pair f g) b vertex t))
      direct-normal : Pairing.direct =₂ (pair⁼ U V ∙ pair-pre f g (const {P = P} b))
      direct-normal = comp₌-cong
        (pair⁼-cong (first ∙ comp₌-unitˡ-One (restrict-triangle f b u t))
          (second ∙ comp₌-unitˡ-One (restrict-triangle g b v t)))
        (id₌ (pair-pre f g (const {P = P} b)))
    compatibility : (pair⁼ U V ∙ pair-pre f g (const {P = P} b)) =₂
      ((pair-pre x y t ∙ (vertex ▷ t)) ∙ A ⁻¹)
    compatibility = composed-normal ∙ (Pairing.compatibility ⁻¹ ∙ direct-normal ⁻¹)
```

The native point restriction uses the same paired triangle values. This
ordinary corollary retains both proved coordinate restriction equations;
its generic proof is closed before concrete native points are supplied.

```agda
private
  module _ {Γ : Context} where
    opaque
      pairing-point-restriction : (P : CAT Γ) {I C D : CAT Γ}
        (f : MAP I C) (g : MAP I D) (b : MAP One I)
        {x : MAP One C} {y : MAP One D}
        (u : (f ∘ b) =₁ x) (v : (g ∘ b) =₁ y)
        (U : (f ∘ const {P = P} b) =₁ const x)
        (V : (g ∘ const {P = P} b) =₁ const y)
        (first : restrict-triangle f b u (terminate P) =₂ U)
        (second : restrict-triangle g b v (terminate P) =₂ V)
        → paired-triangle f g (const {P = P} b) U V =₂
          ((pair-pre x y (terminate P) ∙
            (paired-triangle f g b u v ▷ terminate P)) ∙
              (comp-assoc (terminate P) b (pair f g)) ⁻¹)
      pairing-point-restriction P f g b u v U V first second =
        PairedPointRestriction.compatibility P f g b u v U V first second

      pairing-base-change : {P T K C D : CAT Γ}
        (f : MAP K C) (g : MAP K D) (r : MAP P K) (q : MAP T P)
        (s : MAP T K) (delta : (r ∘ q) =₁ s)
        {x : MAP P C} {y : MAP P D} {x′ : MAP T C} {y′ : MAP T D}
        (b : (f ∘ r) =₁ x) (d : (g ∘ r) =₁ y)
        (b′ : (f ∘ s) =₁ x′) (d′ : (g ∘ s) =₁ y′)
        (c : (x ∘ q) =₁ x′) (e : (y ∘ q) =₁ y′)
        (left-square : (b′ ∙ ((f ◁ delta) ∙ comp-assoc q r f)) =₂ (c ∙ (b ▷ q)))
        (right-square : (d′ ∙ ((g ◁ delta) ∙ comp-assoc q r g)) =₂ (e ∙ (d ▷ q)))
        → (paired-triangle f g s b′ d′ ∙
            ((pair f g ◁ delta) ∙ comp-assoc q r (pair f g))) =₂
          (paired-triangle x y q c e ∙ (paired-triangle f g r b d ▷ q))
      pairing-base-change f g r q s delta {x} {y} {x′} {y′}
        b d b′ d′ c e left-square right-square =
          PairedBaseImage.image f g r q s delta {x = x} {y = y} {x′ = x′} {y′ = y′}
            b d b′ d′ c e left-square right-square
```

The two routes below are independently fixed by the adopted constructions.
The final declaration derives CoordinateAgreement through their two
projection equations. No conditional replacement for the evaluated corner
theorem is exported.

```agda
module SquareCornerCoordinates {Γ : Context} (P : CAT Γ)
  (a b : MAP One ([1] {Γ = Γ})) where
  private
    I : CAT Γ
    I = [1]
    module Coordinates = SquareCoordinates P
    module H = Coordinates.Horizontal a
    module V = Coordinates.Vertical b
    module Shape = InsertionComposition P
    module Native = SquareCorner a b
  ia : MAP P (P × I)
  ia = insert a
  ib : MAP P (P × I)
  ib = insert b
  chi : (H.step ∘ ib) =₁ (V.step ∘ ia)
  chi = ParameterInsertion.value a ib
  module Insertion = InsertionProjections a ib

  matching : (H.restriction ∘ ib) =₁ (V.restriction ∘ ia)
  matching = (V.comparison ▷ ia) ∙
    ((comp-assoc ia V.step Coordinates.permute) ⁻¹ ∙
      ((Coordinates.permute ◁ chi) ∙
        (comp-assoc ib H.step Coordinates.permute ∙ (H.comparison ▷ ib) ⁻¹)))

  point-action : insert {P = P} (coinsert a ∘ b) =₁ insert (insert b ∘ a)
  point-action = pair⁼ (const (id₌ (id P))) (Native.corner ▷ terminate P)

  native : (H.restriction ∘ ib) =₁ (V.restriction ∘ ia)
  native = (Shape.χ (insert b) a) ⁻¹ ∙ (point-action ∙ Shape.χ (coinsert a) b)

  CoordinateAgreement : Set m
  CoordinateAgreement = matching =₂ native

  module ParameterCorner where
    private
      gamma : MAP ((P × I) × I) P
      gamma = Coordinates.parameter
      ba = pair-β₁ (id P) (const {P = P} a)
      bb = pair-β₁ (id P) (const {P = P} b)
      module Change = InsertionSectionEvaluation a ib (pr₁ {C = P} {D = I})
      module Frames = SectionFrames pr₁ ia ba
      h-frame = Change.Before.image (pr₁ {C = P} {D = I})
      v-frame = comp-unitˡ (pr₁ {C = P} {D = I}) ∙
        ((bb ▷ pr₁) ∙ Change.comparison)
      E = Change.After.image (pr₁ ∘ ib)
      R = Change.comparison ▷ ia
      L = comp-unitˡ (pr₁ {C = P} {D = I}) ▷ ia
      B = (bb ▷ pr₁) ▷ ia
      incoming-assoc = comp-assoc ib H.step gamma
      outgoing-assoc = comp-assoc ia V.step gamma
      action = gamma ◁ chi
      raw-target = (bb ∙ E) ∙ R

      v-frame-image : (v-frame ▷ ia) =₂ (L ∙ (B ∙ R))
      v-frame-image = comp₌-cong (id₌ L)
        (preWhisker-comp₌ (bb ▷ pr₁) Change.comparison ia) ∙
          preWhisker-comp₌ (comp-unitˡ pr₁)
            ((bb ▷ pr₁) ∙ Change.comparison) ia

      target-shift : (ba ∙ (v-frame ▷ ia)) =₂ raw-target
      target-shift = comp₌-cong (Frames.collapsed bb) (id₌ R) ∙
        ((comp₌-assoc (ba ∙ L) B R) ⁻¹ ∙
          ((comp₌-assoc ba L (B ∙ R)) ⁻¹ ∙
            comp₌-cong (id₌ ba) v-frame-image))

      route-law : (raw-target ∙ Change.route) =₂ (bb ∙ (h-frame ▷ ib))
      route-law = comp₌-cong (id₌ bb) Change.compatibility ∙
        (comp₌-assoc bb E (R ∙ Change.route) ∙
          comp₌-assoc (bb ∙ E) R Change.route)

    incoming : (gamma ∘ (H.step ∘ ib)) =₁ id P
    incoming = compose-triangle gamma H.step h-frame ib bb
    outgoing : (gamma ∘ (V.step ∘ ia)) =₁ id P
    outgoing = compose-triangle gamma V.step v-frame ia ba

    private
      clear-input : ((outgoing ∙ action) ∙ incoming-assoc) =₂
        ((ba ∙ (v-frame ▷ ia)) ∙ Change.route)
      clear-input = (comp₌-assoc ba (v-frame ▷ ia) Change.route) ⁻¹ ∙
        (comp₌-cong (id₌ ba)
          (comp₌-assoc (v-frame ▷ ia) (outgoing-assoc ⁻¹) (action ∙ incoming-assoc)) ∙
            (comp₌-assoc ba ((v-frame ▷ ia) ∙ outgoing-assoc ⁻¹)
              (action ∙ incoming-assoc) ∙
                comp₌-assoc outgoing action incoming-assoc))
      clear-source : (incoming ∙ incoming-assoc) =₂ (bb ∙ (h-frame ▷ ib))
      clear-source = comp₌-cong (id₌ bb)
        (inv-comp-right (h-frame ▷ ib) incoming-assoc) ∙
          comp₌-assoc bb ((h-frame ▷ ib) ∙ incoming-assoc ⁻¹) incoming-assoc

    compatibility : CompatibleOver gamma incoming outgoing chi
    compatibility = cancel-right incoming-assoc
      (clear-source ⁻¹ ∙
        (route-law ∙
          (comp₌-cong target-shift (id₌ Change.route) ∙ clear-input)))

  module ParameterProjection where
    private
      J = Coordinates.permute
      betaJ = pair-β₁ Coordinates.parameter Coordinates.rectangle
      ba = pair-β₁ (id P) (const {P = P} a)
      bb = pair-β₁ (id P) (const {P = P} b)
      module Change = InsertionSectionEvaluation a ib (pr₁ {C = P} {D = I})
      h-frame = Change.Before.image (pr₁ {C = P} {D = I})
      v-frame = comp-unitˡ (pr₁ {C = P} {D = I}) ∙
        ((bb ▷ pr₁) ∙ Change.comparison)
      first = (H.comparison ▷ ib) ⁻¹
      second = comp-assoc ib H.step J
      third = J ◁ chi
      fourth = (comp-assoc ia V.step J) ⁻¹
      fifth = V.comparison ▷ ia
      stage₁ = compose-triangle pr₁ (J ∘ H.step) H.source-first ib bb
      stage₂ = compose-triangle pr₁ J betaJ (H.step ∘ ib) ParameterCorner.incoming
      stage₃ = compose-triangle pr₁ J betaJ (V.step ∘ ia) ParameterCorner.outgoing
      stage₄ = compose-triangle pr₁ (J ∘ V.step) V.source-first ia ba

    source : (pr₁ ∘ (H.restriction ∘ ib)) =₁ id P
    source = compose-triangle pr₁ H.restriction H.target-first ib bb
    target : (pr₁ ∘ (V.restriction ∘ ia)) =₁ id P
    target = compose-triangle pr₁ V.restriction V.target-first ia ba

    compatibility : CompatibleOver pr₁ source target matching
    compatibility = compatible-comp pr₁ source stage₄ target fifth _
      (compatible-pre pr₁ ia V.source-first V.target-first ba V.comparison V.projection₁)
      (compatible-comp pr₁ source stage₃ stage₄ fourth _
        (compatible-inverse pr₁ stage₄ stage₃ (comp-assoc ia V.step J)
          (compatible-assoc pr₁ J V.step ia betaJ v-frame ba))
        (compatible-comp pr₁ source stage₂ stage₃ third _
          (compatible-post pr₁ J betaJ ParameterCorner.incoming ParameterCorner.outgoing chi
            ParameterCorner.compatibility)
          (compatible-comp pr₁ source stage₁ stage₂ second first
            (compatible-assoc pr₁ J H.step ib betaJ h-frame bb)
            (compatible-inverse pr₁ stage₁ source (H.comparison ▷ ib)
              (compatible-pre pr₁ ib H.source-first H.target-first bb
                H.comparison H.projection₁)))))

  module NativeParameterProjection where
    private
      module Horizontal = ShapeParameter P (coinsert a) b
      module Vertical = ShapeParameter P (insert {P = I} b) a
      at-horizontal = Horizontal.after
      at-vertical = Vertical.after
      original-identity : id P =₁ id P
      original-identity = const (id₌ (id P))
      point-projection : CompatibleOver pr₁ at-horizontal at-vertical point-action
      point-projection = comp₌-unitˡ-One at-horizontal ∙
        (comp₌-cong (const-One (id₌ (id P))) (id₌ at-horizontal) ∙
          pair⁼-triangle₁-One original-identity (Native.corner ▷ terminate P))
    compatibility : CompatibleOver pr₁
      ParameterProjection.source ParameterProjection.target native
    compatibility = compatible-comp pr₁
      ParameterProjection.source at-vertical ParameterProjection.target
      ((Shape.χ (insert b) a) ⁻¹) (point-action ∙ Shape.χ (coinsert a) b)
      (compatible-inverse pr₁ Vertical.before Vertical.after (Shape.χ (insert b) a)
        Vertical.compatibility)
      (compatible-comp pr₁ Horizontal.before Horizontal.after Vertical.after
        point-action (Shape.χ (coinsert a) b) point-projection Horizontal.compatibility)

  parameter-agreement : (pr₁ ◁ matching) =₂ (pr₁ ◁ native)
  parameter-agreement = cancel-left ParameterProjection.target
    (NativeParameterProjection.compatibility ⁻¹ ∙ ParameterProjection.compatibility)

  module OuterCorner where
    private
      gamma : MAP ((P × I) × I) I
      gamma = Coordinates.outer
      ba = pair-β₁ (id P) (const {P = P} a)
      bb = pair-β₂ (id P) (const {P = P} b)
      output = const-pre b ia
      module Change = InsertionSectionEvaluation a ib (pr₂ {C = P} {D = I})
      module Frames = SectionFrames pr₁ ia ba
      h-frame = Change.Before.image (pr₂ {C = P} {D = I})
      v-frame = const-pre b pr₁ ∙ ((bb ▷ pr₁) ∙ Change.comparison)
      E = Change.After.image (pr₂ ∘ ib)
      R = Change.comparison ▷ ia
      L = const-pre b (pr₁ {C = P} {D = I}) ▷ ia
      B = (bb ▷ pr₁) ▷ ia
      incoming-assoc = comp-assoc ib H.step gamma
      outgoing-assoc = comp-assoc ia V.step gamma
      action = gamma ◁ chi
      raw-target = (bb ∙ E) ∙ R
      v-frame-image : (v-frame ▷ ia) =₂ (L ∙ (B ∙ R))
      v-frame-image = comp₌-cong (id₌ L)
        (preWhisker-comp₌ (bb ▷ pr₁) Change.comparison ia) ∙
          preWhisker-comp₌ (const-pre b pr₁)
            ((bb ▷ pr₁) ∙ Change.comparison) ia
      target-shift : (output ∙ (v-frame ▷ ia)) =₂ raw-target
      target-shift = comp₌-cong (Frames.constant-collapsed b bb) (id₌ R) ∙
        ((comp₌-assoc (output ∙ L) B R) ⁻¹ ∙
          ((comp₌-assoc output L (B ∙ R)) ⁻¹ ∙
            comp₌-cong (id₌ output) v-frame-image))
      route-law : (raw-target ∙ Change.route) =₂ (bb ∙ (h-frame ▷ ib))
      route-law = comp₌-cong (id₌ bb) Change.compatibility ∙
        (comp₌-assoc bb E (R ∙ Change.route) ∙
          comp₌-assoc (bb ∙ E) R Change.route)

    incoming : (gamma ∘ (H.step ∘ ib)) =₁ const b
    incoming = compose-triangle gamma H.step h-frame ib bb
    outgoing : (gamma ∘ (V.step ∘ ia)) =₁ const b
    outgoing = compose-triangle gamma V.step v-frame ia output

    private
      clear-input : ((outgoing ∙ action) ∙ incoming-assoc) =₂
        ((output ∙ (v-frame ▷ ia)) ∙ Change.route)
      clear-input = (comp₌-assoc output (v-frame ▷ ia) Change.route) ⁻¹ ∙
        (comp₌-cong (id₌ output)
          (comp₌-assoc (v-frame ▷ ia) (outgoing-assoc ⁻¹) (action ∙ incoming-assoc)) ∙
            (comp₌-assoc output ((v-frame ▷ ia) ∙ outgoing-assoc ⁻¹)
              (action ∙ incoming-assoc) ∙
                comp₌-assoc outgoing action incoming-assoc))
      clear-source : (incoming ∙ incoming-assoc) =₂ (bb ∙ (h-frame ▷ ib))
      clear-source = comp₌-cong (id₌ bb)
        (inv-comp-right (h-frame ▷ ib) incoming-assoc) ∙
          comp₌-assoc bb ((h-frame ▷ ib) ∙ incoming-assoc ⁻¹) incoming-assoc

    compatibility : CompatibleOver gamma incoming outgoing chi
    compatibility = cancel-right incoming-assoc
      (clear-source ⁻¹ ∙
        (route-law ∙
          (comp₌-cong target-shift (id₌ Change.route) ∙ clear-input)))

  module InnerCorner where
    private
      gamma = Coordinates.inner
      a-frame = pair-β₂ (id P) (const {P = P} a)
      h-frame = pair-β₂ (id (P × I)) (const {P = P × I} a)
      v-frame = comp-unitˡ (pr₂ {C = P} {D = I}) ∙
        pair-β₂ (ib ∘ pr₁) (id I ∘ pr₂)
      L = comp-unitˡ (pr₂ {C = P} {D = I}) ▷ ia
      B = pair-β₂ (ib ∘ pr₁) (id I ∘ pr₂) ▷ ia
      A = (comp-assoc ia V.step gamma) ⁻¹
      projected = project-pair₂ (ib ∘ pr₁) (id I ∘ pr₂) ia
    incoming : (gamma ∘ (H.step ∘ ib)) =₁ const a
    incoming = compose-triangle gamma H.step h-frame ib (const-pre a ib)
    outgoing : (gamma ∘ (V.step ∘ ia)) =₁ const a
    outgoing = compose-triangle gamma V.step v-frame ia a-frame
    private
      target-normal : outgoing =₂ Insertion.outgoing₂
      target-normal = comp₌-cong ((post-triangle-id pr₂ ia a-frame) ⁻¹) (id₌ projected) ∙
        ((comp₌-assoc a-frame L projected) ⁻¹ ∙
          comp₌-cong (id₌ a-frame)
            (comp₌-assoc L B A ∙
              comp₌-cong (preWhisker-comp₌ (comp-unitˡ pr₂)
                (pair-β₂ (ib ∘ pr₁) (id I ∘ pr₂)) ia) (id₌ A)))
    compatibility : CompatibleOver gamma incoming outgoing chi
    compatibility = Insertion.projection₂ ∙
      comp₌-cong target-normal (id₌ (gamma ◁ chi))

  module RectangleCorner where
    private
      inner = Coordinates.inner
      outer = Coordinates.outer
      rectangle = Coordinates.rectangle
      a-frame = pair-β₂ (id P) (const {P = P} a)
      b-frame = pair-β₂ (id P) (const {P = P} b)
      module Change = InsertionSectionEvaluation a ib (pr₂ {C = P} {D = I})
      h-inner = pair-β₂ (id (P × I)) (const {P = P × I} a)
      h-outer = Change.Before.image (pr₂ {C = P} {D = I})
      v-inner = comp-unitˡ (pr₂ {C = P} {D = I}) ∙
        pair-β₂ (ib ∘ pr₁) (id I ∘ pr₂)
      v-outer = const-pre b pr₁ ∙ ((b-frame ▷ pr₁) ∙ Change.comparison)
    h-frame : (rectangle ∘ H.step) =₁ pair (const a) pr₂
    h-frame = pair⁼ h-inner h-outer ∙ pair-pre inner outer H.step
    v-frame : (rectangle ∘ V.step) =₁ pair pr₂ (const b)
    v-frame = pair⁼ v-inner v-outer ∙ pair-pre inner outer V.step
    h-point : (pair (const {P = P × I} a) pr₂ ∘ ib) =₁ pair (const a) (const b)
    h-point = pair⁼ (const-pre a ib) b-frame ∙ pair-pre (const a) pr₂ ib
    v-point : (pair pr₂ (const {P = P × I} b) ∘ ia) =₁ pair (const a) (const b)
    v-point = pair⁼ a-frame (const-pre b ia) ∙ pair-pre pr₂ (const b) ia
    incoming : (rectangle ∘ (H.step ∘ ib)) =₁ pair (const a) (const b)
    incoming = compose-triangle rectangle H.step h-frame ib h-point
    outgoing : (rectangle ∘ (V.step ∘ ia)) =₁ pair (const a) (const b)
    outgoing = compose-triangle rectangle V.step v-frame ia v-point
    private
      incoming-paired : (rectangle ∘ (H.step ∘ ib)) =₁ pair (const a) (const b)
      incoming-paired = paired-triangle inner outer (H.step ∘ ib)
        InnerCorner.incoming OuterCorner.incoming
      outgoing-paired : (rectangle ∘ (V.step ∘ ia)) =₁ pair (const a) (const b)
      outgoing-paired = paired-triangle inner outer (V.step ∘ ia)
        InnerCorner.outgoing OuterCorner.outgoing
      incoming-computation : incoming =₂ incoming-paired
      incoming-computation = pairing-compose-triangle inner outer H.step ib
        h-inner h-outer (const-pre a ib) b-frame
      outgoing-computation : outgoing =₂ outgoing-paired
      outgoing-computation = pairing-compose-triangle inner outer V.step ia
        v-inner v-outer a-frame (const-pre b ia)
      direct-compatible : (outgoing-paired ∙ (rectangle ◁ chi)) =₂ incoming-paired
      direct-compatible = comp₌-cong
        (pair⁼-cong InnerCorner.compatibility OuterCorner.compatibility)
        (id₌ (pair-pre inner outer (H.step ∘ ib))) ∙
          pair-action-image inner outer chi InnerCorner.outgoing OuterCorner.outgoing
    compatibility : CompatibleOver rectangle incoming outgoing chi
    compatibility = incoming-computation ⁻¹ ∙
      (direct-compatible ∙ comp₌-cong outgoing-computation (id₌ (rectangle ◁ chi)))

  module RectangleProjection where
    private
      J = Coordinates.permute
      betaJ = pair-β₂ Coordinates.parameter Coordinates.rectangle
      h-point = RectangleCorner.h-point
      v-point = RectangleCorner.v-point
      first = (H.comparison ▷ ib) ⁻¹
      second = comp-assoc ib H.step J
      third = J ◁ chi
      fourth = (comp-assoc ia V.step J) ⁻¹
      fifth = V.comparison ▷ ia
      stage₁ = compose-triangle pr₂ (J ∘ H.step) H.source-second ib h-point
      stage₂ = compose-triangle pr₂ J betaJ (H.step ∘ ib) RectangleCorner.incoming
      stage₃ = compose-triangle pr₂ J betaJ (V.step ∘ ia) RectangleCorner.outgoing
      stage₄ = compose-triangle pr₂ (J ∘ V.step) V.source-second ia v-point
    source : (pr₂ ∘ (H.restriction ∘ ib)) =₁ pair (const a) (const b)
    source = compose-triangle pr₂ H.restriction H.target-second ib h-point
    target : (pr₂ ∘ (V.restriction ∘ ia)) =₁ pair (const a) (const b)
    target = compose-triangle pr₂ V.restriction V.target-second ia v-point
    compatibility : CompatibleOver pr₂ source target matching
    compatibility = compatible-comp pr₂ source stage₄ target fifth _
      (compatible-pre pr₂ ia V.source-second V.target-second v-point V.comparison V.projection₂)
      (compatible-comp pr₂ source stage₃ stage₄ fourth _
        (compatible-inverse pr₂ stage₄ stage₃ (comp-assoc ia V.step J)
          (compatible-assoc pr₂ J V.step ia betaJ RectangleCorner.v-frame v-point))
        (compatible-comp pr₂ source stage₂ stage₃ third _
          (compatible-post pr₂ J betaJ RectangleCorner.incoming RectangleCorner.outgoing chi
            RectangleCorner.compatibility)
          (compatible-comp pr₂ source stage₁ stage₂ second first
            (compatible-assoc pr₂ J H.step ib betaJ RectangleCorner.h-frame h-point)
            (compatible-inverse pr₂ stage₁ source (H.comparison ▷ ib)
              (compatible-pre pr₂ ib H.source-second H.target-second h-point
                H.comparison H.projection₂)))))

  module NativeRectangleProjection where
    private
      t = terminate P
      a-frame = pair-β₂ (id P) (const {P = P} a)
      b-frame = pair-β₂ (id P) (const {P = P} b)
      pair-at-point = pair-pre a b t
      module HConstant = ConstantPointRestriction P a b
      module VConstant = ConstantPointRestriction P b a
      module HAt = Shape.At (coinsert a) b
      module VAt = Shape.At (insert {P = I} b) a
      h-middle : (coinsert a ∘ pr₂ {C = P} {D = I}) =₁ pair (const a) pr₂
      h-middle = pair⁼ (const-pre a pr₂) (comp-unitˡ pr₂) ∙
        pair-pre (const {P = I} a) (id I) pr₂
      v-middle : (insert {P = I} b ∘ pr₂ {C = P} {D = I}) =₁ pair pr₂ (const b)
      v-middle = pair⁼ (comp-unitˡ pr₂) (const-pre b pr₂) ∙
        pair-pre (id I) (const {P = I} b) pr₂
      h-vertex = pair-at-point ∙ (Native.horizontal-vertex ▷ t)
      v-vertex = pair-at-point ∙ (Native.vertical-vertex ▷ t)
      h-tail = (coinsert a ◁ b-frame) ∙ comp-assoc ib pr₂ (coinsert a)
      v-tail = (insert {P = I} b ◁ a-frame) ∙ comp-assoc ia pr₂ (insert {P = I} b)

      h-base-new : (coinsert a ∘ const {P = P} b) =₁ pair (const a) (const b)
      h-base-new = paired-triangle (const {P = I} a) (id I) (const {P = P} b)
        (const-pre a (const {P = P} b)) (comp-unitˡ (const {P = P} b))
      v-base-new : (insert {P = I} b ∘ const {P = P} a) =₁ pair (const a) (const b)
      v-base-new = paired-triangle (id I) (const {P = I} b) (const {P = P} a)
        (comp-unitˡ (const {P = P} a)) (const-pre b (const {P = P} a))
      h-base-image : (h-base-new ∙ h-tail) =₂
        (RectangleCorner.h-point ∙ (h-middle ▷ ib))
      h-base-image = pairing-base-change
        (const {P = I} a) (id I) pr₂ ib (const {P = P} b) b-frame
        {x = const {P = P × I} a} {y = pr₂ {C = P} {D = I}}
        {x′ = const {P = P} a} {y′ = const {P = P} b}
        (const-pre a pr₂) (comp-unitˡ pr₂)
        (const-pre a (const {P = P} b)) (comp-unitˡ (const {P = P} b))
        (const-pre a ib) b-frame
        (const-pre-change a pr₂ ib (const {P = P} b) b-frame)
        (post-triangle-id pr₂ ib b-frame)
      v-base-image : (v-base-new ∙ v-tail) =₂
        (RectangleCorner.v-point ∙ (v-middle ▷ ia))
      v-base-image = pairing-base-change
        (id I) (const {P = I} b) pr₂ ia (const {P = P} a) a-frame
        {x = pr₂ {C = P} {D = I}} {y = const {P = P × I} b}
        {x′ = const {P = P} a} {y′ = const {P = P} b}
        (comp-unitˡ pr₂) (const-pre b pr₂)
        (comp-unitˡ (const {P = P} a)) (const-pre b (const {P = P} a))
        a-frame (const-pre b ia)
        (post-triangle-id pr₂ ia a-frame)
        (const-pre-change b pr₂ ia (const {P = P} a) a-frame)

      horizontal-point : paired-triangle (const {P = I} a) (id I) (const {P = P} b)
        (const-pre a (const {P = P} b)) (comp-unitˡ (const {P = P} b)) =₂
          (h-vertex ∙ (comp-assoc t b (coinsert a)) ⁻¹)
      horizontal-point = pairing-point-restriction P (const {P = I} a) (id I) b
        (const-evaluate a b) (comp-unitˡ b)
        (const-pre a (const {P = P} b)) (comp-unitˡ (const {P = P} b))
        HConstant.compatibility (unit-corner t b)
      vertical-point : paired-triangle (id I) (const {P = I} b) (const {P = P} a)
        (comp-unitˡ (const {P = P} a)) (const-pre b (const {P = P} a)) =₂
          (v-vertex ∙ (comp-assoc t a (insert {P = I} b)) ⁻¹)
      vertical-point = pairing-point-restriction P (id I) (const {P = I} b) a
        (comp-unitˡ a) (const-evaluate b a)
        (comp-unitˡ (const {P = P} a)) (const-pre b (const {P = P} a))
        (unit-corner t a) VConstant.compatibility

      horizontal-normal : (RectangleCorner.h-point ∙ (h-middle ▷ ib)) =₂
        (h-vertex ∙ HAt.second)
      horizontal-normal = comp₌-assoc h-vertex
        ((comp-assoc t b (coinsert a)) ⁻¹) h-tail ∙
          (comp₌-cong horizontal-point (id₌ h-tail) ∙ h-base-image ⁻¹)
      vertical-normal : (RectangleCorner.v-point ∙ (v-middle ▷ ia)) =₂
        (v-vertex ∙ VAt.second)
      vertical-normal = comp₌-assoc v-vertex
        ((comp-assoc t a (insert {P = I} b)) ⁻¹) v-tail ∙
          (comp₌-cong vertical-point (id₌ v-tail) ∙ v-base-image ⁻¹)

      h-product = project-pair₂ Shape.q (coinsert a ∘ pr₂) ib
      v-product = project-pair₂ Shape.q (insert {P = I} b ∘ pr₂) ia
      h-assoc = (comp-assoc ib H.restriction pr₂) ⁻¹
      v-assoc = (comp-assoc ia V.restriction pr₂) ⁻¹
      h-beta = Shape.b₂ (coinsert a)
      v-beta = Shape.b₂ (insert {P = I} b)

      horizontal-source : RectangleProjection.source =₂ (h-vertex ∙ (HAt.second ∙ h-product))
      horizontal-source = comp₌-assoc h-vertex HAt.second h-product ∙
        (comp₌-cong horizontal-normal (id₌ h-product) ∙
          ((comp₌-assoc RectangleCorner.h-point (h-middle ▷ ib) h-product) ⁻¹ ∙
            comp₌-cong (id₌ RectangleCorner.h-point)
              (comp₌-assoc (h-middle ▷ ib) (h-beta ▷ ib) h-assoc ∙
                comp₌-cong (preWhisker-comp₌ h-middle h-beta ib) (id₌ h-assoc))))
      vertical-source : RectangleProjection.target =₂ (v-vertex ∙ (VAt.second ∙ v-product))
      vertical-source = comp₌-assoc v-vertex VAt.second v-product ∙
        (comp₌-cong vertical-normal (id₌ v-product) ∙
          ((comp₌-assoc RectangleCorner.v-point (v-middle ▷ ia) v-product) ⁻¹ ∙
            comp₌-cong (id₌ RectangleCorner.v-point)
              (comp₌-assoc (v-middle ▷ ia) (v-beta ▷ ia) v-assoc ∙
                comp₌-cong (preWhisker-comp₌ v-middle v-beta ia) (id₌ v-assoc))))

      h-point-frame = pair-β₂ (id P) (const {P = P} (coinsert a ∘ b))
      v-point-frame = pair-β₂ (id P) (const {P = P} (insert {P = I} b ∘ a))
      h-frame = h-vertex ∙ h-point-frame
      v-frame = v-vertex ∙ v-point-frame
      horizontal-compatible : CompatibleOver pr₂ RectangleProjection.source h-frame (Shape.χ (coinsert a) b)
      horizontal-compatible = horizontal-source ⁻¹ ∙
        (comp₌-cong (id₌ h-vertex) HAt.projection₂ ∙
          comp₌-assoc h-vertex h-point-frame (pr₂ ◁ Shape.χ (coinsert a) b))
      vertical-compatible : CompatibleOver pr₂ RectangleProjection.target v-frame (Shape.χ (insert b) a)
      vertical-compatible = vertical-source ⁻¹ ∙
        (comp₌-cong (id₌ v-vertex) VAt.projection₂ ∙
          comp₌-assoc v-vertex v-point-frame (pr₂ ◁ Shape.χ (insert b) a))

      corner-image : ((Native.vertical-vertex ▷ t) ∙ (Native.corner ▷ t)) =₂
        (Native.horizontal-vertex ▷ t)
      corner-image = (preWhisker t ◁ comp-inv-left Native.vertical-vertex Native.horizontal-vertex) ∙
        (preWhisker-comp₌ Native.vertical-vertex Native.corner t) ⁻¹
      vertex-compatible : (v-vertex ∙ (Native.corner ▷ t)) =₂ h-vertex
      vertex-compatible = comp₌-cong (id₌ pair-at-point) corner-image ∙
        comp₌-assoc pair-at-point (Native.vertical-vertex ▷ t) (Native.corner ▷ t)
      point-compatible : CompatibleOver pr₂ h-frame v-frame point-action
      point-compatible = comp₌-cong vertex-compatible (id₌ h-point-frame) ∙
        ((comp₌-assoc v-vertex (Native.corner ▷ t) h-point-frame) ⁻¹ ∙
          (comp₌-cong (id₌ v-vertex)
            (pair⁼-triangle₂-One (const (id₌ (id P))) (Native.corner ▷ t)) ∙
              comp₌-assoc v-vertex v-point-frame (pr₂ ◁ point-action)))

    compatibility : CompatibleOver pr₂ RectangleProjection.source RectangleProjection.target native
    compatibility = compatible-comp pr₂ RectangleProjection.source v-frame RectangleProjection.target
      ((Shape.χ (insert b) a) ⁻¹) (point-action ∙ Shape.χ (coinsert a) b)
      (compatible-inverse pr₂ RectangleProjection.target v-frame (Shape.χ (insert b) a)
        vertical-compatible)
      (compatible-comp pr₂ RectangleProjection.source h-frame v-frame
        point-action (Shape.χ (coinsert a) b) point-compatible horizontal-compatible)

  rectangle-agreement : (pr₂ ◁ matching) =₂ (pr₂ ◁ native)
  rectangle-agreement = cancel-left RectangleProjection.target
    (NativeRectangleProjection.compatibility ⁻¹ ∙ RectangleProjection.compatibility)

  coordinate-agreement : CoordinateAgreement
  coordinate-agreement = pair₌-extensionality parameter-agreement rectangle-agreement
```
