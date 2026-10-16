# Evaluating a constant restriction

The specified constant restriction compares with insertion of its value.
Both routes have the same parameter coordinate. The remaining coordinate
is the image of a comparison into the terminal category, where uniqueness
applies. Evaluation retains the original constant restriction triangle and
the original boundary of the identity family.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.ConstantRestrictionEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; comp₌-unitʳ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (identity-unitors)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle; restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation
  using (module SectionEvaluation; module SectionPairing)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair⁼-comp; pair⁼-cong)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert; evAt; evAt-cong)

module ConstantInsertion {Γ : Context} {I J : CAT Γ}
  (P : CAT Γ) (a : MAP One I) (z : MAP One J) where
  private
    pi : MAP (P × I) P
    pi = pr₁
    other : MAP (P × I) I
    other = pr₂
    i : MAP P (P × I)
    i = insert a
    j : MAP P (P × J)
    j = insert z
    t : MAP P One
    t = terminate P
    s : MAP I One
    s = terminate I
    b₁ = pair-β₁ (id P) (const {P = P} a)
    b₂ = pair-β₂ (id P) (const {P = P} a)
    epsilon = terminal-identification (s ∘ other) (t ∘ pi)
    epsilon-a = terminal-identification (s ∘ a) (id One)
    module E = SectionEvaluation pi i b₁
    module A = SectionEvaluation s a epsilon-a
    module Restrict = A.Restriction t z
    module Change = E.Compared t (s ∘ other) epsilon z

  point : (const {P = I} z ∘ a) =₁ z
  point = const-evaluate z a

  coordinate-comparison : (const {P = I} z ∘ other) =₁ (const {P = P} z ∘ pi)
  coordinate-comparison = (comp-assoc pi t z) ⁻¹ ∙
    ((z ◁ epsilon) ∙ comp-assoc other s z)

  comparison : productMap (id P) (const {P = I} z) =₁ (insert z ∘ pi)
  comparison = (pair-pre (id P) (const {P = P} z) pi) ⁻¹ ∙
    pair⁼ (id₌ (id P ∘ pi)) coordinate-comparison

  insertion : (productMap (id P) (const {P = I} z) ∘ insert a) =₁
    insert ((const {P = I} z) ∘ a)
  insertion = pair⁼ (comp-unitˡ (id P)) ((comp-assoc t a (const {P = I} z)) ⁻¹) ∙
    productMap-pair (id P) (const {P = I} z) (id P) (const {P = P} a)

  private
    terminal-first = terminal-identification (s ∘ a) (terminate One)
    terminal-last = terminal-identification {Γ = Γ} (terminate One) (id One)
    point-frame = comp-assoc a s z
    point-section : point =₂ A.image z
    point-section = comp₌-cong (id₌ (comp-unitʳ z))
        (comp₌-cong (postWhisker z ◁ terminal-unique₂ (terminal-last ∙ terminal-first) epsilon-a)
          (id₌ point-frame)) ∙
      (comp₌-cong (id₌ (comp-unitʳ z))
        (comp₌-cong ((postWhisker-comp₌ z terminal-last terminal-first) ⁻¹) (id₌ point-frame) ∙
          ((comp₌-assoc (z ◁ terminal-last) (z ◁ terminal-first) point-frame) ⁻¹)) ∙
        comp₌-assoc (comp-unitʳ z) (z ◁ terminal-last) ((z ◁ terminal-first) ∙ point-frame))

    terminal-source = E.image t ∙ (epsilon ▷ i)
    terminal-middle = comp-unitˡ t ∙ restrict-triangle s a epsilon-a t
    terminal-target = terminal-middle ∙ post-triangle s other i b₂
    inner-frame = comp-assoc i (s ∘ other) z
    outer-frame = comp-assoc other s z ▷ i
    point-prefix = (point ▷ t) ∙ (comp-assoc t a (z ∘ s)) ⁻¹
    restriction = post-triangle (z ∘ s) other i b₂
    left-second = E.image (z ∘ t) ∙ (coordinate-comparison ▷ i)
    right-second = (point ▷ t) ∙ (((comp-assoc t a (z ∘ s)) ⁻¹) ∙ restriction)
    left-normal : left-second =₂
      (((z ◁ terminal-source) ∙ inner-frame) ∙ outer-frame)
    left-normal = comp₌-cong Change.compatibility (id₌ outer-frame) ∙
      (((comp₌-assoc (E.image (z ∘ t)) (Change.comparison ▷ i) outer-frame) ⁻¹) ∙
        comp₌-cong (id₌ (E.image (z ∘ t)))
          (preWhisker-comp₌ Change.comparison (comp-assoc other s z) i ∙
            (preWhisker i ◁ ((comp₌-assoc ((comp-assoc pi t z) ⁻¹)
              (z ◁ epsilon) (comp-assoc other s z)) ⁻¹))))
    point-normal : point-prefix =₂ post-triangle z s (a ∘ t) terminal-middle
    point-normal = Restrict.compatibility ∙
      comp₌-cong (preWhisker t ◁ point-section) (id₌ ((comp-assoc t a (z ∘ s)) ⁻¹))
    right-normal : right-second =₂
      (((z ◁ terminal-target) ∙ inner-frame) ∙ outer-frame)
    right-normal = comp₌-cong
        (comp₌-cong ((postWhisker-comp₌ z terminal-middle (post-triangle s other i b₂)) ⁻¹)
            (id₌ inner-frame) ∙
          ((comp₌-assoc (z ◁ terminal-middle) (z ◁ post-triangle s other i b₂) inner-frame) ⁻¹))
        (id₌ outer-frame) ∙
      (((comp₌-assoc (z ◁ terminal-middle)
        (post-triangle z (s ∘ other) i (post-triangle s other i b₂)) outer-frame) ⁻¹) ∙
        (comp₌-cong (id₌ (z ◁ terminal-middle))
          ((comp₌-assoc (z ◁ post-triangle s other i b₂) inner-frame outer-frame) ⁻¹) ∙
        (comp₌-cong (id₌ (z ◁ terminal-middle)) (post-triangle-comp z s other i b₂) ∙
          (comp₌-assoc (z ◁ terminal-middle) (comp-assoc (a ∘ t) s z) restriction ∙
            (comp₌-cong point-normal (id₌ restriction) ∙
              ((comp₌-assoc (point ▷ t) ((comp-assoc t a (z ∘ s)) ⁻¹) restriction) ⁻¹))))))
    second-coordinate : left-second =₂ right-second
    second-coordinate = right-normal ⁻¹ ∙
      (comp₌-cong (comp₌-cong (postWhisker z ◁ terminal-unique₂ terminal-source terminal-target)
        (id₌ inner-frame)) (id₌ outer-frame) ∙ left-normal)
    first-coordinate :
      (E.image (id P) ∙ (id₌ (id P ∘ pi) ▷ i)) =₂
      (comp-unitˡ (id P) ∙ post-triangle (id P) pi i b₁)
    first-coordinate = comp₌-cong (identity-unitors P) (id₌ (post-triangle (id P) pi i b₁)) ∙
      (comp₌-unitʳ-One (E.image (id P)) ∙
        comp₌-cong (id₌ (E.image (id P))) (preWhisker-id₌ (id P ∘ pi) i))
    module Pair = SectionPairing pi i b₁ (id P) (const {P = P} z)
    module Compared = Pair.Compared (id₌ (id P ∘ pi)) coordinate-comparison
    first-image = post-triangle (id P) pi i b₁
    second-image = post-triangle (const {P = I} z) other i b₂
    first = comp-unitˡ (id P) ∙ first-image
    second = ((comp-assoc t a (const {P = I} z)) ⁻¹) ∙ second-image
    step = pair-pre (id P ∘ pi) (const {P = I} z ∘ other) i
    native-id : id P =₁ id P
    native-id = const {P = One} (id₌ (id P))
    vertex = pair⁼ native-id (point ▷ t)
    insertion-normal : insertion =₂ (pair⁼ first second ∙ step)
    insertion-normal = comp₌-cong
        ((pair⁼-comp (comp-unitˡ (id P)) first-image
          ((comp-assoc t a (const {P = I} z)) ⁻¹) second-image) ⁻¹) (id₌ step) ∙
      ((comp₌-assoc
        (pair⁼ (comp-unitˡ (id P)) ((comp-assoc t a (const {P = I} z)) ⁻¹))
        (pair⁼ first-image second-image) step) ⁻¹)
    native-first : (native-id ∙ first) =₂ first
    native-first = comp₌-unitˡ-One first ∙ comp₌-cong (const-One (id₌ (id P))) (id₌ first)
    right-normalization : (vertex ∙ insertion) =₂ (pair⁼ first right-second ∙ step)
    right-normalization = comp₌-cong
        (pair⁼-cong native-first (id₌ right-second) ∙
          ((pair⁼-comp native-id first (point ▷ t) second) ⁻¹)) (id₌ step) ∙
      (((comp₌-assoc vertex (pair⁼ first second) step) ⁻¹) ∙
        comp₌-cong (id₌ vertex) insertion-normal)

  compatibility :
    (E.image (insert z) ∙ (comparison ▷ insert a)) =₂
    (pair⁼ (const (id₌ (id P))) (point ▷ terminate P) ∙ insertion)
  compatibility = right-normalization ⁻¹ ∙
    (comp₌-cong (pair⁼-cong first-coordinate second-coordinate) (id₌ step) ∙ Compared.evaluation)

module ConstantEvaluation {Γ : Context} {I J C : CAT Γ}
  (a : MAP One I) (z : MAP One J) where
  private
    P : CAT Γ
    P = Fun J C
    e : MAP (P × J) C
    e = funEval
    pi : MAP (P × I) P
    pi = pr₁
    i : MAP P (P × I)
    i = insert a
    j : MAP P (P × J)
    j = insert z
    K = productMap (id P) (const {P = I} z)
    b₁ = pair-β₁ (id P) (const {P = P} a)
    module E = SectionEvaluation pi i b₁
    module Product = ConstantInsertion P a z
    module Change = E.Compared j K Product.comparison e
    vertex = pair⁼ (const (id₌ (id P))) (Product.point ▷ terminate P)

  comparison : (e ∘ K) =₁ (evAt {C = C} z ∘ pi)
  comparison = (comp-assoc pi j e) ⁻¹ ∙ (e ◁ Product.comparison)

  compatibility :
    (E.image (evAt {C = C} z) ∙ (comparison ▷ insert a)) =₂
    (evAt-cong {C = C} (const-evaluate z a) ∙
      post-triangle e K (insert a) Product.insertion)
  compatibility = comp₌-assoc (e ◁ vertex) (e ◁ Product.insertion) (comp-assoc i K e) ∙
    (comp₌-cong
      (postWhisker-comp₌ e vertex Product.insertion ∙ (postWhisker e ◁ Product.compatibility))
      (id₌ (comp-assoc i K e)) ∙ Change.compatibility)
```
