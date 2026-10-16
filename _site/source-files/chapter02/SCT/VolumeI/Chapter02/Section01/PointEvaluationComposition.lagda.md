# Point evaluation and composition of shape restrictions

The chosen comparison for restricting a diagram is compatible with composing
shape maps. Evaluation at a point carries that actual compositor to the
pasting of the two point-evaluation comparisons. Parameter change and shape
change meet in one mixed insertion square, proved from the product and
currying interfaces. The intermediate calculations are private.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition; postWhisker-id₌; preWhisker-id₌; module Boundaries; inv₌)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌; interchange-fixedInner; interchange-fixedOuter; interchange; reassociateFour; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; cancel-left; inverse-inverse; cancel-right)
open import SCT.VolumeI.Chapter01.Section02.Products
  using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌; inverse-square₌; replace-edges₌; post-square₌; identity-square₌; pre-square₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor; module ParameterSeparation)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
  using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPre; funPre-β; funPre-uncurry; funPre-comp)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate-id; evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint; evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; postWhisker-comp-One; postWhisker-id-One; whisker-mixed-One; left-unitor-comp; right-unitor-comp; triangle-whiskered; pentagon-whiskered-right; identity-unitors)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
  using (binary-pre; binary-pre-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
  using (productMap-pair; productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair₌-unique; pair⁼-comp; pair⁼-cong; pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-id; post-square-cell-comp; restrict-triangle; lies-over-comp; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; const-pre-iterated; post-iterated-restriction; post-triangle-comp; post-restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
  using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module PairInput; at-pair-input-change; at-pair-restrict)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
  using (evaluation-restriction-triangle; evaluate-restrict-inverse-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingComposition
  using (module NormalizedComposition)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module PointNaturality; module UncurryRoute; module ParameterInsertion; module UncurryParameter)

module InsertionComposition {Γ : Context} (P : CAT Γ) where
  J : {A B : CAT Γ} → MAP A B → MAP (P × A) (P × B)
  J f = product-restriction {P = P} f

  χ : {A B : CAT Γ} (f : MAP A B) (a : MAP One A)
    → (J f ∘ insert {P = P} a) =₁ insert (f ∘ a)
  χ f a = pair⁼ (comp-unitˡ (id P)) ((comp-assoc (terminate P) a f) ⁻¹) ∙
    productMap-pair (id P) f (id P) (const a)

  q : {A : CAT Γ} → MAP (P × A) P
  q = id P ∘ pr₁
  b₁ : {A B : CAT Γ} (f : MAP A B) → (pr₁ ∘ J f) =₁ q
  b₁ f = pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)
  b₂ : {A B : CAT Γ} (f : MAP A B) → (pr₂ ∘ J f) =₁ (f ∘ pr₂)
  b₂ f = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)
  N : {A B : CAT Γ} (f : MAP A B) → (q ∘ J f) =₁ q
  N f = b₁ f ∙ (comp-unitˡ pr₁ ▷ J f)
  D : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C)
    → ((g ∘ pr₂) ∘ J f) =₁ ((g ∘ f) ∘ pr₂)
  D f g = post-square-cell g pr₂ f pr₂ (J f) (b₂ f)

  module Compositor {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    corner = restriction-compositor {P = P} f g
    first = post-square-cell (id P) pr₁ (id P) pr₁ (J f) (b₁ f)
    second = D f g
    first-image : SquareCell₌ (pr₁ ◁ corner) (N f)
      (restrict-triangle pr₁ (J g) (b₁ g) (J f)) (b₁ (g ∘ f))
    first-image = replace-edges₌ (id₌ _)
      (post-square-cell-id pr₁ (id P) pr₁ (J f) (b₁ f))
      (lies-over-comp pr₁
        (pair-evaluation-over₁-One (id P ∘ pr₁) (g ∘ pr₂) (J f) first second)
        (unconst-sides₌ (productMap-cong-triangle₁ (comp-unitˡ (id P)) (id₌ (g ∘ f)))))
    second-image : SquareCell₌ (pr₂ ◁ corner) (D f g)
      (restrict-triangle pr₂ (J g) (b₂ g) (J f)) (b₂ (g ∘ f))
    second-image = replace-edges₌ (id₌ _)
      (comp₌-unitˡ-One second ∙
        comp₌-cong (preWhisker-id₌ (g ∘ f) pr₂) (id₌ second))
      (lies-over-comp pr₂
        (pair-evaluation-over₂-One (id P ∘ pr₁) (g ∘ pr₂) (J f) first second)
        (unconst-sides₌ (productMap-cong-triangle₂ (comp-unitˡ (id P)) (id₌ (g ∘ f)))))
    normalization : corner =₂ (pair⁼ (N f) (D f g) ∙ pair-pre q (g ∘ pr₂) (J f))
    normalization = pair₌-unique first-image second-image
      (pair-evaluation-over₁-One q (g ∘ pr₂) (J f) (N f) (D f g))
      (pair-evaluation-over₂-One q (g ∘ pr₂) (J f) (N f) (D f g))

  module At {A B : CAT Γ} (f : MAP A B) (a : MAP One A) where
    i = insert {P = P} a
    first : (q ∘ i) =₁ id P
    first = comp-unitˡ (id P) ∙
      ((id P ◁ pair-β₁ (id P) (const a)) ∙ comp-assoc i pr₁ (id P))
    second : ((f ∘ pr₂) ∘ i) =₁ const (f ∘ a)
    second = (comp-assoc (terminate P) a f) ⁻¹ ∙
      ((f ◁ pair-β₂ (id P) (const a)) ∙ comp-assoc i pr₂ f)
    normalized = pair⁼ first second ∙ pair-pre q (f ∘ pr₂) i
    normalization : χ f a =₂ normalized
    normalization = comp₌-cong
      ((pair⁼-comp (comp-unitˡ (id P))
        ((id P ◁ pair-β₁ (id P) (const a)) ∙ comp-assoc i pr₁ (id P))
        ((comp-assoc (terminate P) a f) ⁻¹)
        ((f ◁ pair-β₂ (id P) (const a)) ∙ comp-assoc i pr₂ f)) ⁻¹)
      (id₌ (pair-pre q (f ∘ pr₂) i)) ∙
      ((comp₌-assoc (pair⁼ (comp-unitˡ (id P)) ((comp-assoc (terminate P) a f) ⁻¹))
        _ _) ⁻¹)
    first-normalization : first =₂
      (pair-β₁ (id P) (const a) ∙ (comp-unitˡ pr₁ ▷ i))
    first-normalization = comp₌-cong (id₌ (pair-β₁ (id P) (const a)))
      (left-unitor-comp i pr₁) ∙
      (comp₌-assoc (pair-β₁ (id P) (const a)) (comp-unitˡ (pr₁ ∘ i)) (comp-assoc i pr₁ (id P)) ∙
      (comp₌-cong (postWhisker-id-One (pair-β₁ (id P) (const a))) (id₌ (comp-assoc i pr₁ (id P))) ∙
        (comp₌-assoc (comp-unitˡ (id P)) (id P ◁ pair-β₁ (id P) (const a))
          (comp-assoc i pr₁ (id P))) ⁻¹))
    projection₁ : SquareCell₌ (pr₁ ◁ χ f a) first
      (project-pair₁ q (f ∘ pr₂) i) (pair-β₁ (id P) (const (f ∘ a)))
    projection₁ = pair-evaluation-over₁-One q (f ∘ pr₂) i first second ∙
      comp₌-cong (id₌ (pair-β₁ (id P) (const (f ∘ a)))) (postWhisker pr₁ ◁ normalization)
    projection₂ : SquareCell₌ (pr₂ ◁ χ f a) second
      (project-pair₂ q (f ∘ pr₂) i) (pair-β₂ (id P) (const (f ∘ a)))
    projection₂ = pair-evaluation-over₂-One q (f ∘ pr₂) i first second ∙
      comp₌-cong (id₌ (pair-β₂ (id P) (const (f ∘ a)))) (postWhisker pr₂ ◁ normalization)

  module CoordinateComposition {V0 V1 V2 K0 K1 K2 K3 : CAT Γ}
    (π0 : MAP V0 K0) (π1 : MAP V1 K1) (π2 : MAP V2 K2)
    (a : MAP K0 K1) (b : MAP K1 K2) (c : MAP K2 K3)
    (F : MAP V0 V1) (G : MAP V1 V2) (GF : MAP V0 V2)
    (δ : (G ∘ F) =₁ GF)
    (βf : (π1 ∘ F) =₁ (a ∘ π0))
    (βg : (π2 ∘ G) =₁ (b ∘ π1))
    (βgf : (π2 ∘ GF) =₁ ((b ∘ a) ∘ π0)) where
    Dfg = post-square-cell b π0 a π1 F βf
    Dgh = post-square-cell c π1 b π2 G βg
    Dfhg = post-square-cell (c ∘ b) π0 a π1 F βf
    Dgfh = post-square-cell c π0 (b ∘ a) π2 GF βgf

    compatibility : SquareCell₌ (π2 ◁ δ) Dfg
        (restrict-triangle π2 G βg F) βgf →
      (Dgfh ∙ (((c ∘ π2) ◁ δ) ∙ comp-assoc F G (c ∘ π2))) =₂
      ((comp-assoc a b c ▷ π0) ∙ (Dfhg ∙ (Dgh ▷ F)))
    compatibility image =
      let outside = (comp-assoc π0 (b ∘ a) c) ⁻¹
          leftImage = c ◁ βgf
          inputA = comp-assoc GF π2 c
          change = (c ∘ π2) ◁ δ
          sourceA = comp-assoc F G (c ∘ π2)
          normalizeShort = comp₌-cong (id₌ outside)
            (post-triangle-change c π2 G F GF δ βg βgf Dfg image) ∙
            comp₌-assoc outside (leftImage ∙ inputA) (change ∙ sourceA)
          η = comp-assoc a b c ▷ π0
          sourceCorner = comp-assoc π1 b c
          imageBefore = (c ◁ βg) ∙ comp-assoc G π2 c
          nextCoordinate = post-square-cell c π0 (b ∘ a) (b ∘ π1) F Dfg
          outerSquare = (post-square-cell-comp π0 a π1 F βf b c) ⁻¹
          simplifyCorner = (preWhisker F ◁ comp-inv-left sourceCorner imageBefore) ∙
            (preWhisker-comp₌ sourceCorner Dgh F) ⁻¹
          normalizeLong = comp₌-cong (id₌ outside)
            (comp₌-assoc (c ◁ Dfg) (comp-assoc F (b ∘ π1) c) (imageBefore ▷ F)) ∙
            (comp₌-assoc outside
              ((c ◁ Dfg) ∙ comp-assoc F (b ∘ π1) c) (imageBefore ▷ F) ∙
            (comp₌-cong (id₌ nextCoordinate) simplifyCorner ∙
            (comp₌-assoc nextCoordinate (sourceCorner ▷ F) (Dgh ▷ F) ∙
            (comp₌-cong outerSquare (id₌ (Dgh ▷ F)) ∙
              (comp₌-assoc η Dfhg (Dgh ▷ F)) ⁻¹))))
      in normalizeLong ⁻¹ ∙ normalizeShort


  module Successive {A B C : CAT Γ} (a : MAP One A) (f : MAP A B) (g : MAP B C) where
    i = insert {P = P} a
    j = insert {P = P} (f ∘ a)
    corner = χ f a
    S = N f
    T = At.first (g ∘ f) a
    module K = Compositor f g

    first-coordinate :
      (At.first g (f ∘ a) ∙ ((q ◁ corner) ∙ comp-assoc i (J f) q)) =₂
      (id₌ (id P) ∙ (T ∙ (S ▷ i)))
    first-coordinate =
      let v = comp-unitˡ pr₁
          bst = pair-β₁ (id P) (const (f ∘ a))
          b = b₁ f
          Aq = comp-assoc i (J f) q
          Aπ = comp-assoc i (J f) pr₁
          vv = (v ▷ J f) ▷ i
          leftStart = (comp₌-assoc bst (pr₁ ◁ corner) ((v ▷ (J f ∘ i)) ∙ Aq)) ⁻¹ ∙
            (comp₌-cong (id₌ bst) (comp₌-assoc (pr₁ ◁ corner) (v ▷ (J f ∘ i)) Aq) ∙
            (comp₌-cong (id₌ bst) (comp₌-cong (interchange v corner) (id₌ Aq)) ∙
            (reassociateFour bst (v ▷ j) (q ◁ corner) Aq ∙
              comp₌-cong (At.first-normalization g (f ∘ a)) (id₌ ((q ◁ corner) ∙ Aq)))))
          middle = comp₌-cong (At.projection₁ f a) ((preWhisker-comp-One v (J f) i) ⁻¹)
          cancellation = comp₌-cong (id₌ T)
            (comp₌-cong (id₌ (b ▷ i)) (inv-comp-left Aπ vv) ∙
              comp₌-assoc (b ▷ i) (Aπ ⁻¹) (Aπ ∙ vv)) ∙
            comp₌-assoc T ((b ▷ i) ∙ Aπ ⁻¹) (Aπ ∙ vv)
          rightFinish = comp₌-cong (id₌ T) ((preWhisker-comp₌ b (v ▷ J f) i) ⁻¹)
          insertIdentity = (comp₌-unitˡ-One (T ∙ (S ▷ i))) ⁻¹
      in insertIdentity ∙ (rightFinish ∙ (cancellation ∙ (middle ∙ leftStart)))

    module Varying = CoordinateComposition (terminate P) pr₂ pr₂ a f g
      i (J f) j corner (pair-β₂ (id P) (const a)) (b₂ f)
      (pair-β₂ (id P) (const (f ∘ a)))
    second-coordinate :
      (At.second g (f ∘ a) ∙ (((g ∘ pr₂) ◁ corner) ∙ comp-assoc i (J f) (g ∘ pr₂))) =₂
      ((comp-assoc a f g ▷ terminate P) ∙ (At.second (g ∘ f) a ∙ (D f g ▷ i)))
    second-coordinate = Varying.compatibility (At.projection₂ f a)

    private
      ρ : RestrictionDiagram {E = One} {Q = P} (P × A) (P × B)
      ρ = restriction-diagram (J f) i j corner
      first-evaluation : Evaluation ρ q q (id P) (id P)
      first-evaluation = evaluation (At.first g (f ∘ a)) S T (id₌ (id P))
      second-evaluation : Evaluation ρ (g ∘ pr₂) ((g ∘ f) ∘ pr₂)
        (const ((g ∘ f) ∘ a)) (const (g ∘ (f ∘ a)))
      second-evaluation = evaluation (At.second g (f ∘ a)) (D f g)
        (At.second (g ∘ f) a) (comp-assoc a f g ▷ terminate P)
      paired = pair-compatible-One ρ first-evaluation second-evaluation
        first-coordinate second-coordinate
      finish = pair⁼ (id₌ (id P)) (comp-assoc a f g ▷ terminate P)
      native-finish = pair⁼ (const (id₌ (id P))) (comp-assoc a f g ▷ terminate P)

    law :
      (χ g (f ∘ a) ∙ ((J g ◁ χ f a) ∙ comp-assoc i (J f) (J g))) =₂
      (native-finish ∙ (χ (g ∘ f) a ∙ (K.corner ▷ i)))
    law = comp₌-cong
      ((pair⁼-cong (const-One (id₌ (id P))) (id₌ (comp-assoc a f g ▷ terminate P))) ⁻¹)
      (comp₌-cong ((At.normalization (g ∘ f) a) ⁻¹)
        (preWhisker i ◁ (K.normalization ⁻¹))) ∙
      (paired ∙ comp₌-cong (At.normalization g (f ∘ a))
        (id₌ ((J g ◁ χ f a) ∙ comp-assoc i (J f) (J g))))

private
  module MixedInsertionComposition {Γ : Context} {P Q I J : CAT Γ}
    (h : MAP P Q) (f : MAP I J) (a : MAP One I) where
    private
      module NI = ParameterInsertion a
      module NJ = ParameterInsertion (f ∘ a)
      module ShapeP = InsertionComposition P
      module ShapeQ = InsertionComposition Q
      module Separation = ParameterSeparation h f
      x = const {P = P} a
      y = const {P = P} (f ∘ a)
      constant-image = (comp-assoc (terminate P) a f) ⁻¹
      source-insertion = insert {P = P} a
      common : (productMap h f ∘ source-insertion) =₁ pair h y
      common = pair⁼ (comp-unitʳ h) constant-image ∙ productMap-pair h f (id P) x
      after-parameter : (productMap (id Q) f ∘ pair h x) =₁ pair h y
      after-parameter = pair⁼ (comp-unitˡ h) constant-image ∙ productMap-pair (id Q) f h x
      module Back = NormalizedComposition (id P) h f (id J)
        (id P) x (id P) y h y
        (comp-unitˡ (id P)) constant-image (comp-unitʳ h) (comp-unitˡ y)
        h f (comp-unitʳ h) (comp-unitˡ f) (comp-unitʳ h) constant-image
      module Front = NormalizedComposition h (id Q) (id I) f
        (id P) x h x h y
        (comp-unitʳ h) (comp-unitˡ x) (comp-unitˡ h) constant-image
        h f (comp-unitˡ h) (comp-unitʳ f) (comp-unitʳ h) constant-image

      back-first : ((comp-unitʳ h ∙ (h ◁ comp-unitˡ (id P))) ∙ comp-assoc (id P) (id P) h) =₂
        (comp-unitʳ h ∙ (comp-unitʳ h ▷ id P))
      back-first = comp₌-cong (id₌ (comp-unitʳ h)) ((triangle-whiskered (id P) h) ⁻¹) ∙
        comp₌-assoc (comp-unitʳ h) (h ◁ comp-unitˡ (id P)) (comp-assoc (id P) (id P) h)
      back-second : ((comp-unitˡ y ∙ (id J ◁ constant-image)) ∙ comp-assoc x f (id J)) =₂
        (constant-image ∙ (comp-unitˡ f ▷ x))
      back-second = comp₌-cong (id₌ constant-image) (left-unitor-comp x f) ∙
        (comp₌-assoc constant-image (comp-unitˡ (f ∘ x)) (comp-assoc x f (id J)) ∙
        comp₌-cong (postWhisker-id-One constant-image) (id₌ (comp-assoc x f (id J))))
      front-first : ((comp-unitˡ h ∙ (id Q ◁ comp-unitʳ h)) ∙ comp-assoc (id P) h (id Q)) =₂
        (comp-unitʳ h ∙ (comp-unitˡ h ▷ id P))
      front-first = comp₌-cong (id₌ (comp-unitʳ h)) (left-unitor-comp (id P) h) ∙
        (comp₌-assoc (comp-unitʳ h) (comp-unitˡ (h ∘ id P)) (comp-assoc (id P) h (id Q)) ∙
        comp₌-cong (postWhisker-id-One (comp-unitʳ h)) (id₌ (comp-assoc (id P) h (id Q))))
      front-second : ((constant-image ∙ (f ◁ comp-unitˡ x)) ∙ comp-assoc x (id I) f) =₂
        (constant-image ∙ (comp-unitʳ f ▷ x))
      front-second = comp₌-cong (id₌ constant-image) ((triangle-whiskered x f) ⁻¹) ∙
        comp₌-assoc constant-image (f ◁ comp-unitˡ x) (comp-assoc x (id I) f)

    back-normalization :
      (NJ.back h ∙ ((productMap h (id J) ◁ ShapeP.χ f a) ∙
        comp-assoc source-insertion (productMap (id P) f) (productMap h (id J)))) =₂
      (common ∙ (Separation.back ▷ source-insertion))
    back-normalization = Back.composition back-first back-second

    front-normalization :
      (after-parameter ∙ ((productMap (id Q) f ◁ NI.back h) ∙
        comp-assoc source-insertion (productMap h (id I)) (productMap (id Q) f))) =₂
      (common ∙ (Separation.front ▷ source-insertion))
    front-normalization = Front.composition front-first front-second

private
  module ShapeInsertionRestriction {Γ : Context} {P Q I J : CAT Γ}
    (h : MAP P Q) (f : MAP I J) (a : MAP One I) where
    private
      module NI = ParameterInsertion a
      module NJ = ParameterInsertion (f ∘ a)
      module ShapeQ = InsertionComposition Q
      module AtQ = ShapeQ.At f a
      x = const {P = P} a
      xQ = const {P = Q} a
      y = const {P = P} (f ∘ a)
      yQ = const {P = Q} (f ∘ a)
      iQ = insert {P = Q} a
      input-pair = pair h x
      δ = NI.front h
      H = productMap (id Q) f
      cP = (comp-assoc (terminate P) a f) ⁻¹
      cQ = (comp-assoc (terminate Q) a f) ⁻¹
      direct₁ = comp-unitˡ h ∙ post-triangle (id Q) pr₁ input-pair (pair-β₁ h x)
      direct₂ = cP ∙ post-triangle f pr₂ input-pair (pair-β₂ h x)
      old₁ = post-triangle (id Q) pr₁ iQ (pair-β₁ (id Q) xQ)
      old₂ = post-triangle f pr₂ iQ (pair-β₂ (id Q) xQ)
      change₁ = ((id Q ∘ pr₁) ◁ δ) ∙ comp-assoc h iQ (id Q ∘ pr₁)
      change₂ = ((f ∘ pr₂) ◁ δ) ∙ comp-assoc h iQ (f ∘ pr₂)
      first-raw = post-triangle-change (id Q) pr₁ iQ h input-pair δ
        (pair-β₁ (id Q) xQ) (pair-β₁ h x) (comp-unitˡ h)
        (pair-evaluation-over₁-One (id Q) xQ h (comp-unitˡ h) (const-pre a h))
      second-raw = post-triangle-change f pr₂ iQ h input-pair δ
        (pair-β₂ (id Q) xQ) (pair-β₂ h x) (const-pre a h)
        (pair-evaluation-over₂-One (id Q) xQ h (comp-unitˡ h) (const-pre a h))

      constant-image-restrict :
        (cP ∙ ((f ◁ const-pre a h) ∙ comp-assoc h xQ f)) =₂
        (const-pre (f ∘ a) h ∙ (cQ ▷ h))
      constant-image-restrict = cancel-right restricted-corner (right-normal ⁻¹ ∙ left-normal)
        where
        corner = comp-assoc (terminate P) a f
        old-corner = comp-assoc (terminate Q) a f
        restricted-corner = old-corner ▷ h
        image = f ◁ const-pre a h
        change = comp-assoc h xQ f
        constant-step = const-pre (f ∘ a) h
        terminal-step = terminal-identification (terminate Q ∘ h) (terminate P)
        left-normal = inv-comp-left corner constant-step ∙
          (comp₌-cong (id₌ cP) ((post-triangle-comp f a (terminate Q) h terminal-step) ⁻¹) ∙
          (comp₌-cong (id₌ cP) (comp₌-assoc image change restricted-corner) ∙
            comp₌-assoc cP (image ∙ change) restricted-corner))
        right-normal = inv-comp-right constant-step restricted-corner ∙
          comp₌-cong (comp₌-cong (id₌ constant-step) (preWhisker-inverse old-corner h))
            (id₌ restricted-corner)

      first-coordinate : (direct₁ ∙ change₁) =₂
        (comp-unitˡ h ∙ (AtQ.first ▷ h))
      first-coordinate = comp₌-cong (id₌ (comp-unitˡ h))
          ((preWhisker-comp₌ (comp-unitˡ (id Q)) old₁ h) ⁻¹) ∙
        (comp₌-cong (id₌ (comp-unitˡ h))
          (comp₌-cong (preWhisker h ◁ identity-unitors Q) (id₌ (old₁ ▷ h))) ∙
        (comp₌-cong (id₌ (comp-unitˡ h))
          (comp₌-cong ((triangle-whiskered h (id Q)) ⁻¹) (id₌ (old₁ ▷ h))) ∙
        (comp₌-cong (id₌ (comp-unitˡ h))
          ((comp₌-assoc (id Q ◁ comp-unitˡ h) (comp-assoc h (id Q) (id Q)) (old₁ ▷ h)) ⁻¹) ∙
        (comp₌-cong (id₌ (comp-unitˡ h)) first-raw ∙
          comp₌-assoc (comp-unitˡ h) (post-triangle (id Q) pr₁ input-pair (pair-β₁ h x)) change₁))))

      second-coordinate : (direct₂ ∙ change₂) =₂
        (const-pre (f ∘ a) h ∙ (AtQ.second ▷ h))
      second-coordinate = comp₌-cong (id₌ (const-pre (f ∘ a) h))
          ((preWhisker-comp₌ cQ old₂ h) ⁻¹) ∙
        (comp₌-assoc (const-pre (f ∘ a) h) (cQ ▷ h) (old₂ ▷ h) ∙
        (comp₌-cong constant-image-restrict (id₌ (old₂ ▷ h)) ∙
        ((comp₌-assoc cP ((f ◁ const-pre a h) ∙ comp-assoc h xQ f) (old₂ ▷ h)) ⁻¹ ∙
        (comp₌-cong (id₌ cP)
          ((comp₌-assoc (f ◁ const-pre a h) (comp-assoc h xQ f) (old₂ ▷ h)) ⁻¹) ∙
        (comp₌-cong (id₌ cP) second-raw ∙
          comp₌-assoc cP (post-triangle f pr₂ input-pair (pair-β₂ h x)) change₂)))))

      ρ : RestrictionDiagram {E = One} {Q = P} Q (Q × I)
      ρ = restriction-diagram iQ h input-pair δ
      first-evaluation : Evaluation ρ (id Q ∘ pr₁) (id Q) h h
      first-evaluation = evaluation direct₁ AtQ.first (comp-unitˡ h) (id₌ h)
      second-evaluation : Evaluation ρ (f ∘ pr₂) yQ y y
      second-evaluation = evaluation direct₂ AtQ.second (const-pre (f ∘ a) h) (id₌ y)
      paired = pair-compatible-One ρ first-evaluation second-evaluation
        ((comp₌-unitˡ-One (comp-unitˡ h ∙ (AtQ.first ▷ h))) ⁻¹ ∙ first-coordinate)
        ((comp₌-unitˡ-One (const-pre (f ∘ a) h ∙ (AtQ.second ▷ h))) ⁻¹ ∙ second-coordinate)
      after-parameter = pair⁼ (comp-unitˡ h) cP ∙ productMap-pair (id Q) f h x
      normalized-after = pair⁼ direct₁ direct₂ ∙ pair-pre (id Q ∘ pr₁) (f ∘ pr₂) input-pair
      after-normalization : after-parameter =₂ normalized-after
      after-normalization = comp₌-cong
        ((pair⁼-comp (comp-unitˡ h) (post-triangle (id Q) pr₁ input-pair (pair-β₁ h x))
          cP (post-triangle f pr₂ input-pair (pair-β₂ h x))) ⁻¹)
        (id₌ (pair-pre (id Q ∘ pr₁) (f ∘ pr₂) input-pair)) ∙
        (comp₌-assoc (pair⁼ (comp-unitˡ h) cP)
          (pair⁼ (post-triangle (id Q) pr₁ input-pair (pair-β₁ h x))
            (post-triangle f pr₂ input-pair (pair-β₂ h x)))
          (pair-pre (id Q ∘ pr₁) (f ∘ pr₂) input-pair)) ⁻¹

    compatibility :
      (after-parameter ∙ ((H ◁ NI.front h) ∙ comp-assoc h iQ H)) =₂
      (NJ.front h ∙ (ShapeQ.χ f a ▷ h))
    compatibility = comp₌-cong (id₌ (NJ.front h))
        (preWhisker h ◁ (AtQ.normalization ⁻¹)) ∙
      (comp₌-unitˡ-One (NJ.front h ∙ (AtQ.normalized ▷ h)) ∙
      (comp₌-cong (pair⁼-id-One h y) (id₌ (NJ.front h ∙ (AtQ.normalized ▷ h))) ∙
      (paired ∙ comp₌-cong after-normalization (id₌ ((H ◁ NI.front h) ∙ comp-assoc h iQ H)))))

private
  module MixedInsertion {Γ : Context} {P Q I J : CAT Γ}
    (h : MAP P Q) (f : MAP I J) (a : MAP One I) where
    private
      module NI = ParameterInsertion a
      module NJ = ParameterInsertion (f ∘ a)
      module SP = InsertionComposition P
      module SQ = InsertionComposition Q
      module Separation = ParameterSeparation h f
      module Products = MixedInsertionComposition h f a
      module Restriction = ShapeInsertionRestriction h f a
      iP = insert {P = P} a
      iQ = insert {P = Q} a
      HI = productMap h (id I)
      HJ = productMap h (id J)
      LP = productMap (id P) f
      LQ = productMap (id Q) f
      cP = (comp-assoc (terminate P) a f) ⁻¹
      x = const {P = P} a
      y = const {P = P} (f ∘ a)
      D = pair⁼ (comp-unitʳ h) cP ∙ productMap-pair h f (id P) x
      E = pair⁼ (comp-unitˡ h) cP ∙ productMap-pair (id Q) f h x
      A = comp-assoc h iQ LQ
      B = comp-assoc iP LP HJ
      C = comp-assoc iP HI LQ
      b = NJ.back h
      front-image = Separation.front ▷ iP
      back-image = Separation.back ▷ iP
      crossing = Separation.separate ▷ iP
      shape-image = HJ ◁ SP.χ f a
      old-back = LQ ◁ NI.back h
      parameter-image = LQ ◁ NI.value h
      common = E ∙ (LQ ◁ NI.front h)
      tail = C ⁻¹ ∙ parameter-image

    left : (LQ ∘ (iQ ∘ h)) =₁ (HJ ∘ insert {P = P} (f ∘ a))
    left = NJ.value h ∙ ((SQ.χ f a ▷ h) ∙ A ⁻¹)
    right : (LQ ∘ (iQ ∘ h)) =₁ (HJ ∘ insert {P = P} (f ∘ a))
    right = shape-image ∙ (B ∙ (crossing ∙ tail))

    private
      separation-cancel : (back-image ∙ crossing) =₂ front-image
      separation-cancel = (preWhisker iP ◁
          (comp-inv-left Separation.back Separation.front ∙
            comp₌-cong (id₌ Separation.back) Separation.separate-normal)) ∙
        (preWhisker-comp₌ Separation.back Separation.separate iP) ⁻¹
      parameter-cancel : (old-back ∙ parameter-image) =₂ (LQ ◁ NI.front h)
      parameter-cancel = (postWhisker LQ ◁ comp-inv-left (NI.back h) (NI.front h)) ∙
        (postWhisker-comp₌ LQ (NI.back h) (NI.value h)) ⁻¹

      left-normal : (b ∙ left) =₂ common
      left-normal = comp-inv-right common A ∙
        (comp₌-cong ((comp₌-assoc E (LQ ◁ NI.front h) A) ⁻¹) (id₌ (A ⁻¹)) ∙
        (comp₌-cong (Restriction.compatibility ⁻¹) (id₌ (A ⁻¹)) ∙
        ((comp₌-assoc (NJ.front h) (SQ.χ f a ▷ h) (A ⁻¹)) ⁻¹ ∙
        (comp₌-cong (comp-inv-left b (NJ.front h)) (id₌ ((SQ.χ f a ▷ h) ∙ A ⁻¹)) ∙
          (comp₌-assoc b (NJ.value h) ((SQ.χ f a ▷ h) ∙ A ⁻¹)) ⁻¹))))

      remove-corner : ((E ∙ (old-back ∙ C)) ∙ tail) =₂ (E ∙ (old-back ∙ parameter-image))
      remove-corner = comp₌-assoc E old-back parameter-image ∙
        (comp₌-cong (id₌ (E ∙ old-back))
          (comp-inv-left C parameter-image ∙ comp₌-assoc C (C ⁻¹) parameter-image) ∙
        (reassociateFour (E ∙ old-back) C (C ⁻¹) parameter-image ∙
          comp₌-cong ((comp₌-assoc E old-back C) ⁻¹) (id₌ tail)))

      right-normal : (b ∙ right) =₂ common
      right-normal = comp₌-cong (id₌ E) parameter-cancel ∙
        (remove-corner ∙
        (comp₌-cong (Products.front-normalization ⁻¹) (id₌ tail) ∙
        ((comp₌-assoc D front-image tail) ⁻¹ ∙
        (comp₌-cong (id₌ D) (comp₌-cong separation-cancel (id₌ tail)) ∙
        (reassociateFour D back-image crossing tail ∙
        (comp₌-cong Products.back-normalization (id₌ (crossing ∙ tail)) ∙
        ((comp₌-assoc b (shape-image ∙ B) (crossing ∙ tail)) ⁻¹ ∙
          comp₌-cong (id₌ b) ((comp₌-assoc shape-image B (crossing ∙ tail)) ⁻¹))))))))

    compatibility : left =₂ right
    compatibility = cancel-left b (right-normal ⁻¹ ∙ left-normal)

private
  module PreEvaluationRoute {Γ : Context} {I J C : CAT Γ}
    (a : MAP One I) (f : MAP I J) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      i = insert {P = F} a
      L = productMap (id F) f
      module Shape = InsertionComposition F
      unit-frame = pair⁼ (comp-unitˡ (id F)) ((comp-assoc (terminate F) a f) ⁻¹)
      pair-image = productMap-pair (id F) f (id F) (const a)
      beta = funPre-β {D = C} f
      mu = AtPoint.uncurry-image a (funPre {D = C} f)
      tail = comp-assoc i L e ∙ ((beta ▷ i) ∙ mu)
    factorization : evAt-pre {C = C} a f =₂
      ((e ◁ Shape.χ f a) ∙ tail)
    factorization =
      comp₌-cong ((postWhisker-comp₌ e unit-frame pair-image) ⁻¹) (id₌ tail) ∙
        (comp₌-assoc (e ◁ unit-frame) (e ◁ pair-image) tail) ⁻¹

private
  module PreEvaluationBeta {Γ : Context} {I J C P : CAT Γ}
    (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      i = insert {P = P} a
      t = insert {P = F} a
      H = productMap h (id I)
      L = productMap (id F) f
      u = funUncurry (funPre {D = C} f)
      v = e ∘ L
      beta = funPre-β {D = C} f
      module N = ParameterInsertion a
      nu = N.value h
      before = comp-assoc i H u
      after = comp-assoc i H v
      beta-double = (beta ▷ H) ▷ i
      beta-source = beta ▷ (t ∘ h)
      beta-target = beta ▷ (H ∘ i)
      naturality = preWhisker-comp-One beta H i
      ending = (v ◁ nu) ∙ beta-source
      source-normal = unconst-sides₌ (interchange-fixedOuter beta nu) ∙
        (comp₌-cong (id₌ beta-target)
          (comp-inv-left before (u ◁ nu) ∙ comp₌-assoc before (before ⁻¹) (u ◁ nu)) ∙
        (reassociateFour beta-target before (before ⁻¹) (u ◁ nu) ∙
        (comp₌-cong naturality (id₌ ((before ⁻¹) ∙ (u ◁ nu))) ∙
          (comp₌-assoc after beta-double ((before ⁻¹) ∙ (u ◁ nu))) ⁻¹)))
    compatibility : (beta-double ∙ ((before ⁻¹) ∙ (u ◁ nu))) =₂
      ((after ⁻¹) ∙ ((v ◁ nu) ∙ beta-source))
    compatibility = cancel-left after ((comp-inv-left after ending) ⁻¹ ∙ source-normal)

private
  module LeftEvaluationNormal {Γ : Context} {I J C P : CAT Γ}
    (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      k = funPre {D = C} f
      u = funUncurry k
      v = e ∘ productMap (id F) f
      L = productMap (id F) f
      H = productMap h (id J)
      t = insert {P = F} a
      j = insert {P = P} (f ∘ a)
      module N = ParameterInsertion (f ∘ a)
      module Shape = InsertionComposition F
      module Structural = MixedInsertion h f a
      module Route = PreEvaluationRoute {C = C} a f
      beta = funPre-β {D = C} f
      mu = AtPoint.uncurry-image a k
      mu-new = AtPoint.uncurry-image (f ∘ a) h
      output = comp-assoc j H e
      direct = e ◁ Structural.left
      corner = comp-assoc h k (evAt a)
      point = post-triangle e L t (Shape.χ f a)
      point-restricted = point ▷ h
      beta-restricted = (beta ▷ t) ▷ h
      beta-source = beta ▷ (t ∘ h)
      source-frame = comp-assoc h t u
      target-frame = comp-assoc h t v
      outer-frame = comp-assoc (t ∘ h) L e
      tail = (mu ▷ h) ∙ (corner ⁻¹)
      common-tail = beta-source ∙ (source-frame ∙ tail)
      point-factor : evAt-pre {C = C} a f =₂ (point ∙ ((beta ▷ t) ∙ mu))
      point-factor =
        (comp₌-assoc (e ◁ Shape.χ f a) (comp-assoc t L e) ((beta ▷ t) ∙ mu)) ⁻¹ ∙
        Route.factorization
      point-whiskered = comp₌-cong (id₌ point-restricted)
          (preWhisker-comp₌ (beta ▷ t) mu h) ∙
        (preWhisker-comp₌ point ((beta ▷ t) ∙ mu) h ∙
          (preWhisker h ◁ point-factor))
      prefix-normal : (mu-new ∙ point-restricted) =₂
        ((output ⁻¹) ∙ (direct ∙ (outer-frame ∙ target-frame)))
      prefix-normal = comp₌-cong (id₌ (output ⁻¹))
          ((post-restrict-triangle e L t h (Shape.χ f a) (N.value h)) ⁻¹) ∙
        (comp₌-cong (id₌ (output ⁻¹))
          (comp₌-assoc (e ◁ N.value h) (comp-assoc h (insert {P = F} (f ∘ a)) e) point-restricted) ∙
        (comp₌-assoc (output ⁻¹)
          ((e ◁ N.value h) ∙ comp-assoc h (insert {P = F} (f ∘ a)) e) point-restricted ∙
          comp₌-cong (UncurryRoute.factorization (f ∘ a) h) (id₌ point-restricted)))
      beta-tail : ((outer-frame ∙ target-frame) ∙ (beta-restricted ∙ tail)) =₂
        (outer-frame ∙ common-tail)
      beta-tail = comp₌-cong (id₌ outer-frame)
          (comp₌-assoc beta-source source-frame tail) ∙
        (comp₌-cong (id₌ outer-frame)
          (comp₌-cong (preWhisker-comp-One beta t h) (id₌ tail)) ∙
          reassociateFour outer-frame target-frame beta-restricted tail)
      input-normal :
        (mu-new ∙ ((evAt-pre {C = C} a f ▷ h) ∙ (corner ⁻¹))) =₂
        ((mu-new ∙ point-restricted) ∙ (beta-restricted ∙ tail))
      input-normal =
        (comp₌-assoc mu-new point-restricted (beta-restricted ∙ tail)) ⁻¹ ∙
        (comp₌-cong (id₌ mu-new)
          (comp₌-cong (id₌ point-restricted)
            (comp₌-assoc beta-restricted (mu ▷ h) (corner ⁻¹))) ∙
        (comp₌-cong (id₌ mu-new)
          (comp₌-assoc point-restricted (beta-restricted ∙ (mu ▷ h)) (corner ⁻¹)) ∙
          comp₌-cong (id₌ mu-new) (comp₌-cong point-whiskered (id₌ (corner ⁻¹)))))
      finish = comp₌-cong (id₌ (output ⁻¹)) (comp₌-cong (id₌ direct) beta-tail) ∙
        (comp₌-cong (id₌ (output ⁻¹))
          (comp₌-assoc direct (outer-frame ∙ target-frame) (beta-restricted ∙ tail)) ∙
          comp₌-assoc (output ⁻¹) (direct ∙ (outer-frame ∙ target-frame)) (beta-restricted ∙ tail))
    normal-form = (output ⁻¹) ∙ (direct ∙ (outer-frame ∙ common-tail))
    compatibility :
      (mu-new ∙ ((evAt-pre {C = C} a f ▷ h) ∙ (corner ⁻¹))) =₂ normal-form
    compatibility = finish ∙
      (comp₌-cong prefix-normal (id₌ (beta-restricted ∙ tail)) ∙ input-normal)

private
  module RightEvaluationFrame {Γ : Context} {I J C P : CAT Γ}
    (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      i = insert {P = P} a
      j = insert {P = P} (f ∘ a)
      t = insert {P = F} a
      HI = productMap h (id I)
      HJ = productMap h (id J)
      LP = productMap (id P) f
      LQ = productMap (id F) f
      v = funUncurry h
      module N = ParameterInsertion a
      module SP = InsertionComposition P
      module Sep = ParameterSeparation h f
      module Structural = MixedInsertion h f a
      shape-image = HJ ◁ SP.χ f a
      shape-frame = comp-assoc i LP HJ
      shape = post-triangle HJ LP i (SP.χ f a)
      point = post-triangle v LP i (SP.χ f a)
      output = comp-assoc j HJ e
      compositor = comp-assoc LP HJ e
      compositor-restricted = compositor ▷ i
      inverse-compositor = (compositor ⁻¹) ▷ i
      separation = Sep.separate ▷ i
      restriction = comp-assoc i HI LQ
      partial = shape ∙ restrict-triangle LQ HI Sep.separate i
      post-separation = post-triangle e LQ HI Sep.separate
      post-restricted = post-separation ▷ i
      before = comp-assoc i HI (e ∘ LQ)
      intermediate = comp-assoc i (HJ ∘ LP) e
      outer = comp-assoc (HI ∘ i) LQ e
      final-outer = comp-assoc (t ∘ h) LQ e
      parameter = LQ ◁ N.value h
      target-parameter = (e ∘ LQ) ◁ N.value h
      prefix-normal = comp-inv-right ((e ◁ shape) ∙ intermediate) compositor-restricted ∙
        (comp₌-cong (id₌ (((e ◁ shape) ∙ intermediate) ∙ compositor-restricted))
          (preWhisker-inverse compositor i) ∙
        (comp₌-cong ((comp₌-assoc (e ◁ shape) intermediate compositor-restricted) ⁻¹)
          (id₌ inverse-compositor) ∙
          comp₌-cong (post-triangle-comp e HJ LP i (SP.χ f a)) (id₌ inverse-compositor)))
      coefficient = point ∙ (inverse-compositor ∙ (post-restricted ∙ (before ⁻¹)))
      source-normal : (output ∙ coefficient) =₂ ((e ◁ partial) ∙ outer)
      source-normal = comp-inv-right ((e ◁ partial) ∙ outer) before ∙
        (comp₌-cong ((comp₌-assoc (e ◁ partial) outer before) ⁻¹) (id₌ (before ⁻¹)) ∙
        (comp₌-cong ((post-restrict-triangle e LQ HI i Sep.separate shape) ⁻¹)
          (id₌ (before ⁻¹)) ∙
        ((comp₌-assoc (e ◁ shape) (intermediate ∙ post-restricted) (before ⁻¹)) ⁻¹ ∙
        (comp₌-cong (id₌ (e ◁ shape))
          ((comp₌-assoc intermediate post-restricted (before ⁻¹)) ⁻¹) ∙
        (comp₌-assoc (e ◁ shape) intermediate (post-restricted ∙ (before ⁻¹)) ∙
        (comp₌-cong prefix-normal (id₌ (post-restricted ∙ (before ⁻¹))) ∙
        ((comp₌-assoc (output ∙ point) inverse-compositor (post-restricted ∙ (before ⁻¹))) ⁻¹ ∙
          (comp₌-assoc output point (inverse-compositor ∙ (post-restricted ∙ (before ⁻¹)))) ⁻¹)))))))
      coefficient-normal = cancel-left output
        ((comp-inv-left output ((e ◁ partial) ∙ outer)) ⁻¹ ∙ source-normal)
      partial-parameter : (partial ∙ parameter) =₂ Structural.right
      partial-parameter = comp₌-assoc shape-image shape-frame
          (separation ∙ ((restriction ⁻¹) ∙ parameter)) ∙
        (comp₌-cong (id₌ shape)
          (comp₌-assoc separation (restriction ⁻¹) parameter) ∙
          comp₌-assoc shape (separation ∙ (restriction ⁻¹)) parameter)
      parameter-frame : ((outer ∙ target-parameter)) =₂
        ((e ◁ parameter) ∙ final-outer)
      parameter-frame = postWhisker-comp-One (N.value h) LQ e
      paired-frame : (coefficient ∙ target-parameter) =₂
        ((output ⁻¹) ∙ ((e ◁ Structural.right) ∙ final-outer))
      paired-frame = comp₌-cong (id₌ (output ⁻¹))
          (comp₌-cong (postWhisker e ◁ partial-parameter) (id₌ final-outer)) ∙
        (comp₌-cong (id₌ (output ⁻¹))
          (comp₌-cong ((postWhisker-comp₌ e partial parameter) ⁻¹) (id₌ final-outer)) ∙
        (comp₌-cong (id₌ (output ⁻¹))
          ((comp₌-assoc (e ◁ partial) (e ◁ parameter) final-outer) ⁻¹) ∙
        (comp₌-cong (id₌ (output ⁻¹)) (comp₌-cong (id₌ (e ◁ partial)) parameter-frame) ∙
        (comp₌-cong (id₌ (output ⁻¹))
          (comp₌-assoc (e ◁ partial) outer target-parameter) ∙
        (comp₌-assoc (output ⁻¹) ((e ◁ partial) ∙ outer) target-parameter ∙
          comp₌-cong coefficient-normal (id₌ target-parameter))))))
    compatibility :
      ((post-triangle v LP i (SP.χ f a) ∙
        (((comp-assoc LP HJ e) ⁻¹ ▷ i) ∙
          ((post-triangle e LQ HI Sep.separate ▷ i) ∙
            ((comp-assoc i HI (e ∘ LQ)) ⁻¹)))) ∙ target-parameter) =₂
      ((output ⁻¹) ∙ ((e ◁ Structural.right) ∙ final-outer))
    compatibility = paired-frame

private
  module RightEvaluationInput {Γ : Context} {I J C P : CAT Γ}
    (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      eI = funEval {C = I} {D = C}
      k = funPre {D = C} f
      u = funUncurry k
      v = funUncurry h
      i = insert {P = P} a
      t = insert {P = F} a
      HI = productMap h (id I)
      HJ = productMap h (id J)
      LP = productMap (id P) f
      LQ = productMap (id F) f
      module N = ParameterInsertion a
      module SP = InsertionComposition P
      module Sep = ParameterSeparation h f
      module Parameter = UncurryParameter a k h
      module Beta = PreEvaluationBeta {C = C} a f h
      mu = AtPoint.uncurry-image a k
      mu-composite = AtPoint.uncurry-image a (k ∘ h)
      corner = comp-assoc h k (evAt a)
      tail = (mu ▷ h) ∙ (corner ⁻¹)
      source-frame = comp-assoc h t u
      last = source-frame ∙ tail
      beta = funPre-β {D = C} f
      beta-source = beta ▷ (t ∘ h)
      beta-double = (beta ▷ HI) ▷ i
      common-tail = beta-source ∙ last
      before = comp-assoc i HI u
      after = comp-assoc i HI (e ∘ LQ)
      parameter = u ◁ N.value h
      target-parameter = (e ∘ LQ) ◁ N.value h
      parameter-evaluation = evaluate-restrict eI k h
      evaluation-restricted = parameter-evaluation ▷ i
      evaluation-inverse = (parameter-evaluation ⁻¹) ▷ i
      post-separation = post-triangle e LQ HI Sep.separate
      post-restricted = post-separation ▷ i
      compositor = comp-assoc LP HJ e
      inverse-compositor = (compositor ⁻¹) ▷ i
      inner = (before ⁻¹) ∙ (parameter ∙ last)
      point = post-triangle v LP i (SP.χ f a)
      coefficient = point ∙ (inverse-compositor ∙ (post-restricted ∙ (after ⁻¹)))
      alpha = funPre-uncurry {D = C} f h
      alpha-factor : alpha =₂
        ((compositor ⁻¹) ∙ (post-separation ∙ ((beta ▷ HI) ∙ parameter-evaluation)))
      alpha-factor = comp₌-cong (id₌ (compositor ⁻¹))
        ((comp₌-assoc (e ◁ Sep.separate) (comp-assoc HI LQ e) ((beta ▷ HI) ∙ parameter-evaluation)) ⁻¹)
      alpha-whiskered = comp₌-cong (id₌ inverse-compositor)
          (comp₌-cong (id₌ post-restricted) (preWhisker-comp₌ (beta ▷ HI) parameter-evaluation i)) ∙
        (comp₌-cong (id₌ inverse-compositor)
          (preWhisker-comp₌ post-separation ((beta ▷ HI) ∙ parameter-evaluation) i) ∙
        (preWhisker-comp₌ (compositor ⁻¹) (post-separation ∙ ((beta ▷ HI) ∙ parameter-evaluation)) i ∙
          (preWhisker i ◁ alpha-factor)))
      mu-normal : mu-composite =₂ (evaluation-inverse ∙ inner)
      mu-normal = comp₌-cong (id₌ evaluation-inverse)
          (comp₌-cong (id₌ (before ⁻¹))
            (comp₌-cong (id₌ parameter) (comp₌-assoc source-frame (mu ▷ h) (corner ⁻¹)))) ∙
        (comp₌-cong (id₌ evaluation-inverse)
          (comp₌-cong (id₌ (before ⁻¹))
            (comp₌-assoc parameter (source-frame ∙ (mu ▷ h)) (corner ⁻¹))) ∙
        (comp₌-cong (id₌ evaluation-inverse)
          (comp₌-assoc (before ⁻¹) (parameter ∙ (source-frame ∙ (mu ▷ h))) (corner ⁻¹)) ∙
        (comp₌-assoc evaluation-inverse
          ((before ⁻¹) ∙ (parameter ∙ (source-frame ∙ (mu ▷ h)))) (corner ⁻¹) ∙
        (comp₌-cong Parameter.composition (id₌ (corner ⁻¹)) ∙
          (comp-inv-right mu-composite corner) ⁻¹))))
      cancel-evaluation :
        ((beta-double ∙ evaluation-restricted) ∙ (evaluation-inverse ∙ inner)) =₂
        (beta-double ∙ inner)
      cancel-evaluation = comp₌-cong (id₌ beta-double)
          (comp-inv-left evaluation-restricted inner ∙
            comp₌-assoc evaluation-restricted (evaluation-restricted ⁻¹) inner) ∙
        (reassociateFour beta-double evaluation-restricted (evaluation-restricted ⁻¹) inner ∙
          comp₌-cong (id₌ (beta-double ∙ evaluation-restricted))
            (comp₌-cong (preWhisker-inverse parameter-evaluation i) (id₌ inner)))
      beta-normal : (beta-double ∙ inner) =₂
        ((after ⁻¹) ∙ (target-parameter ∙ common-tail))
      beta-normal = comp₌-cong (id₌ (after ⁻¹))
          (comp₌-assoc target-parameter beta-source last) ∙
        (comp₌-assoc (after ⁻¹) (target-parameter ∙ beta-source) last ∙
        (comp₌-cong Beta.compatibility (id₌ last) ∙
        ((comp₌-assoc beta-double ((before ⁻¹) ∙ parameter) last) ⁻¹ ∙
          comp₌-cong (id₌ beta-double) ((comp₌-assoc (before ⁻¹) parameter last) ⁻¹))))
      cancel-block :
        ((inverse-compositor ∙ (post-restricted ∙ (beta-double ∙ evaluation-restricted))) ∙
          (evaluation-inverse ∙ inner)) =₂
        (inverse-compositor ∙ (post-restricted ∙ (beta-double ∙ inner)))
      cancel-block = comp₌-cong (id₌ inverse-compositor)
          (comp₌-cong (id₌ post-restricted) cancel-evaluation) ∙
        (comp₌-cong (id₌ inverse-compositor)
          (comp₌-assoc post-restricted (beta-double ∙ evaluation-restricted) (evaluation-inverse ∙ inner)) ∙
          comp₌-assoc inverse-compositor (post-restricted ∙ (beta-double ∙ evaluation-restricted))
            (evaluation-inverse ∙ inner))
      group-output =
        (comp₌-assoc point (inverse-compositor ∙ (post-restricted ∙ (after ⁻¹)))
          (target-parameter ∙ common-tail)) ⁻¹ ∙
        (comp₌-cong (id₌ point)
          ((comp₌-assoc inverse-compositor (post-restricted ∙ (after ⁻¹))
            (target-parameter ∙ common-tail)) ⁻¹) ∙
        comp₌-cong (id₌ point)
          (comp₌-cong (id₌ inverse-compositor)
            ((comp₌-assoc post-restricted (after ⁻¹) (target-parameter ∙ common-tail)) ⁻¹)))
    compatibility :
      (post-triangle v LP i (SP.χ f a) ∙
        ((funPre-uncurry {D = C} f h ▷ i) ∙ mu-composite)) =₂
      (coefficient ∙ (target-parameter ∙ common-tail))
    compatibility = group-output ∙
      (comp₌-cong (id₌ point)
        (comp₌-cong (id₌ inverse-compositor) (comp₌-cong (id₌ post-restricted) beta-normal)) ∙
      (comp₌-cong (id₌ point) cancel-block ∙
        comp₌-cong (id₌ point) (comp₌-cong alpha-whiskered mu-normal)))

private
  module MixedEvaluation {Γ : Context} {I J C P : CAT Γ}
    (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
    private
      F = Fun J C
      e = funEval {C = J} {D = C}
      k = funPre {D = C} f
      u = funUncurry k
      v = funUncurry h
      i = insert {P = P} a
      j = insert {P = P} (f ∘ a)
      t = insert {P = F} a
      HI = productMap h (id I)
      HJ = productMap h (id J)
      LP = productMap (id P) f
      LQ = productMap (id F) f
      module N = ParameterInsertion a
      module Shape = InsertionComposition P
      module Sep = ParameterSeparation h f
      module Structural = MixedInsertion h f a
      module Left = LeftEvaluationNormal {C = C} a f h
      module Frame = RightEvaluationFrame {C = C} a f h
      module Input = RightEvaluationInput {C = C} a f h
      mu = AtPoint.uncurry-image a k
      mu-new = AtPoint.uncurry-image (f ∘ a) h
      mu-composite = AtPoint.uncurry-image a (k ∘ h)
      corner = comp-assoc h k (evAt a)
      beta = funPre-β {D = C} f
      common-tail = (beta ▷ (t ∘ h)) ∙
        (comp-assoc h t u ∙ ((mu ▷ h) ∙ (corner ⁻¹)))
      output = comp-assoc j HJ e
      outer = comp-assoc (t ∘ h) LQ e
      target-parameter = (e ∘ LQ) ◁ N.value h
      coefficient = post-triangle v LP i (Shape.χ f a) ∙
        (((comp-assoc LP HJ e) ⁻¹ ▷ i) ∙
          ((post-triangle e LQ HI Sep.separate ▷ i) ∙
            ((comp-assoc i HI (e ∘ LQ)) ⁻¹)))
      alpha = funPre-uncurry {D = C} f h
    left : (evAt a ∘ (k ∘ h)) =₁ (v ∘ j)
    left = mu-new ∙ ((evAt-pre {C = C} a f ▷ h) ∙ (corner ⁻¹))
    right : (evAt a ∘ (k ∘ h)) =₁ (v ∘ j)
    right = (v ◁ Shape.χ f a) ∙
      (comp-assoc i LP v ∙ ((alpha ▷ i) ∙ mu-composite))
    private
      direct = e ◁ Structural.right
      right-normal : right =₂
        ((output ⁻¹) ∙ (direct ∙ (outer ∙ common-tail)))
      right-normal = comp₌-cong (id₌ (output ⁻¹))
          (comp₌-assoc direct outer common-tail) ∙
        (comp₌-assoc (output ⁻¹) (direct ∙ outer) common-tail ∙
        (comp₌-cong Frame.compatibility (id₌ common-tail) ∙
        ((comp₌-assoc coefficient target-parameter common-tail) ⁻¹ ∙
        (Input.compatibility ∙
          (comp₌-assoc (v ◁ Shape.χ f a) (comp-assoc i LP v)
            ((alpha ▷ i) ∙ mu-composite)) ⁻¹))))
      central = comp₌-cong (id₌ (output ⁻¹))
        (comp₌-cong (postWhisker e ◁ Structural.compatibility) (id₌ (outer ∙ common-tail)))
    compatibility : left =₂ right
    compatibility = right-normal ⁻¹ ∙ (central ∙ Left.compatibility)

private
  module PrecompositorAtInsertion {Γ : Context} {I J K C : CAT Γ}
    (a : MAP One I) (f : MAP I J) (g : MAP J K) where
    private
      F = Fun K C
      eI = funEval {C = I} {D = C}
      eK = funEval {C = K} {D = C}
      i = insert {P = F} a
      Jf = product-restriction {P = F} f
      Jg = product-restriction {P = F} g
      kf = funPre {D = C} f
      kg = funPre {D = C} g
      kgf = funPre {D = C} (g ∘ f)
      compositor = funPre-comp {D = C} f g
      before-beta = (funPre-β {D = C} g ▷ Jf) ∙ funPre-uncurry f kg
      after-beta = funPre-β {D = C} (g ∘ f)
      route = (eK ◁ restriction-compositor {P = F} f g) ∙ comp-assoc Jf Jg eK
      input = after-beta ⁻¹ ∙
        ((eK ◁ restriction-compositor {P = F} f g) ∙
          (comp-assoc Jf Jg eK ∙ before-beta))
      image : evaluate-cong eI compositor =₂ input
      image = reflect-β-One eI (funUniversal I C) _ _ input
      native : SquareCell₌ (evaluate-cong eI compositor) route before-beta after-beta
      native =
        (comp₌-assoc (eK ◁ restriction-compositor {P = F} f g)
          (comp-assoc Jf Jg eK) before-beta) ⁻¹ ∙
        (comp-inv-left after-beta
          ((eK ◁ restriction-compositor {P = F} f g) ∙
            (comp-assoc Jf Jg eK ∙ before-beta)) ∙
          comp₌-cong (id₌ after-beta) image)
      uncurry : SquareCell₌ (evAt a ◁ compositor)
        (evaluate-cong eI compositor ▷ i)
        (AtPoint.uncurry-image a (kf ∘ kg)) (AtPoint.uncurry-image a kgf)
      uncurry = replace-edges₌ (id₌ _)
        (preWhisker i ◁ evaluate⁼-absolute eI compositor)
        (unconst-sides₌ (AtPoint.uncurry-square a compositor))
    square : SquareCell₌ (evAt a ◁ compositor) (route ▷ i)
      ((before-beta ▷ i) ∙ AtPoint.uncurry-image a (kf ∘ kg))
      ((after-beta ▷ i) ∙ AtPoint.uncurry-image a kgf)
    square = paste-square₌ uncurry (pre-square₌ i native)

private
  module EvaluatedInsertionComposition {Γ : Context} {I J K C : CAT Γ}
    (a : MAP One I) (f : MAP I J) (g : MAP J K) where
    private
      F = Fun K C
      e = funEval {C = K} {D = C}
      i = insert {P = F} a
      j = insert {P = F} (f ∘ a)
      Jf = product-restriction {P = F} f
      Jg = product-restriction {P = F} g
      Jgf = product-restriction {P = F} (g ∘ f)
      module Shape = InsertionComposition F
      module Successive = Shape.Successive a f g
      first-shape = post-triangle Jg Jf i (Shape.χ f a)
      finish-shape = pair⁼ (const (id₌ (id F))) (comp-assoc a f g ▷ terminate F)
      restriction = restriction-compositor {P = F} f g
      input-frame = comp-assoc i (Jg ∘ Jf) e
      direct-frame = comp-assoc i Jgf e
      restricted-frame = comp-assoc Jf Jg e ▷ i
      middle = (whisker-mixed-One restriction i e) ⁻¹
      first-normal =
        comp₌-cong ((postWhisker-comp₌ e (Shape.χ g (f ∘ a)) first-shape) ⁻¹)
          (id₌ (input-frame ∙ restricted-frame)) ∙
        ((comp₌-assoc (e ◁ Shape.χ g (f ∘ a)) (e ◁ first-shape)
          (input-frame ∙ restricted-frame)) ⁻¹ ∙
        (comp₌-cong (id₌ (e ◁ Shape.χ g (f ∘ a)))
          (post-triangle-comp e Jg Jf i (Shape.χ f a)) ∙
          comp₌-assoc (e ◁ Shape.χ g (f ∘ a)) (comp-assoc j Jg e)
            (post-triangle (e ∘ Jg) Jf i (Shape.χ f a))))
      expand = comp₌-cong
        (comp₌-cong (id₌ (e ◁ finish-shape))
          (postWhisker-comp₌ e (Shape.χ (g ∘ f) a) (restriction ▷ i)) ∙
          postWhisker-comp₌ e finish-shape (Shape.χ (g ∘ f) a ∙ (restriction ▷ i)))
        (id₌ (input-frame ∙ restricted-frame))
      direct = post-triangle e Jgf i (Shape.χ (g ∘ f) a)
      route = (e ◁ restriction) ∙ comp-assoc Jf Jg e
      first-step = reassociateFour (e ◁ finish-shape)
        ((e ◁ Shape.χ (g ∘ f) a) ∙ (e ◁ (restriction ▷ i))) input-frame restricted-frame
      second-step = comp₌-cong (id₌ (e ◁ finish-shape))
        (comp₌-cong
          (comp₌-assoc (e ◁ Shape.χ (g ∘ f) a) (e ◁ (restriction ▷ i)) input-frame)
          (id₌ restricted-frame))
      third-step = comp₌-cong (id₌ (e ◁ finish-shape))
        (comp₌-cong (comp₌-cong (id₌ (e ◁ Shape.χ (g ∘ f) a)) middle)
          (id₌ restricted-frame))
      fourth-step = comp₌-cong (id₌ (e ◁ finish-shape))
        (comp₌-cong
          ((comp₌-assoc (e ◁ Shape.χ (g ∘ f) a) direct-frame ((e ◁ restriction) ▷ i)) ⁻¹)
          (id₌ restricted-frame))
      fifth-step = comp₌-cong (id₌ (e ◁ finish-shape))
        (comp₌-assoc direct ((e ◁ restriction) ▷ i) restricted-frame)
      sixth-step = comp₌-cong (id₌ (e ◁ finish-shape))
        (comp₌-cong (id₌ direct)
          ((preWhisker-comp₌ (e ◁ restriction) (comp-assoc Jf Jg e) i) ⁻¹))
      finish = sixth-step ∙ (fifth-step ∙ (fourth-step ∙ (third-step ∙ (second-step ∙ first-step))))
    composition :
      (post-triangle e Jg j (Shape.χ g (f ∘ a)) ∙
        post-triangle (e ∘ Jg) Jf i (Shape.χ f a)) =₂
      (evAt-cong {C = C} (comp-assoc a f g) ∙ (direct ∙ (route ▷ i)))
    composition = finish ∙
      (expand ∙
        (comp₌-cong (postWhisker e ◁ Successive.law)
          (id₌ (input-frame ∙ restricted-frame)) ∙ first-normal))

private
  module PrecompositorBetaShape {Γ : Context} {I J K C : CAT Γ}
    (a : MAP One I) (f : MAP I J) (g : MAP J K) where
    private
      F = Fun K C
      e = funEval {C = K} {D = C}
      i = insert {P = F} a
      j = insert {P = F} (f ∘ a)
      Jf = product-restriction {P = F} f
      Jg = product-restriction {P = F} g
      u = funUncurry (funPre {D = C} g)
      v = e ∘ Jg
      beta = funPre-β {D = C} g
      module Shape = InsertionComposition F
      chi = Shape.χ f a
      beta-target = beta ▷ (Jf ∘ i)
      beta-double = (beta ▷ Jf) ▷ i
      source-frame = comp-assoc i Jf u
      target-frame = comp-assoc i Jf v
      move = unconst-sides₌ (interchange-fixedOuter beta chi)
    compatibility :
      ((beta ▷ j) ∙ post-triangle u Jf i chi) =₂
      (post-triangle v Jf i chi ∙ beta-double)
    compatibility = (comp₌-assoc (v ◁ chi) target-frame beta-double) ⁻¹ ∙
      (comp₌-cong (id₌ (v ◁ chi)) ((preWhisker-comp-One beta Jf i) ⁻¹) ∙
      (comp₌-assoc (v ◁ chi) beta-target source-frame ∙
      (comp₌-cong move (id₌ source-frame) ∙
        (comp₌-assoc (beta ▷ j) (u ◁ chi) source-frame) ⁻¹)))

module PrecompositionPointComposition {Γ : Context} {I J K C : CAT Γ}
  (a : MAP One I) (f : MAP I J) (g : MAP J K) where
  private
    F = Fun K C
    e = funEval {C = K} {D = C}
    i = insert {P = F} a
    j = insert {P = F} (f ∘ a)
    Jf = product-restriction {P = F} f
    Jg = product-restriction {P = F} g
    Jgf = product-restriction {P = F} (g ∘ f)
    kf = funPre {D = C} f
    kg = funPre {D = C} g
    kgf = funPre {D = C} (g ∘ f)
    module Shape = InsertionComposition F
    module Native = PrecompositorAtInsertion {C = C} a f g
    module Evaluated = EvaluatedInsertionComposition {C = C} a f g
    module Beta = PrecompositorBetaShape {C = C} a f g
    module Mixed = MixedEvaluation {C = C} a f kg
    module RouteGF = PreEvaluationRoute {C = C} a (g ∘ f)
    module RouteG = PreEvaluationRoute {C = C} (f ∘ a) g
    beta-g = funPre-β {D = C} g
    beta-gf = funPre-β {D = C} (g ∘ f)
    alpha = funPre-uncurry {D = C} f kg
    mu-composite = AtPoint.uncurry-image a (kf ∘ kg)
    mu-gf = AtPoint.uncurry-image a kgf
    mu-g = AtPoint.uncurry-image (f ∘ a) kg
    point-f = post-triangle (e ∘ Jg) Jf i (Shape.χ f a)
    point-g = post-triangle e Jg j (Shape.χ g (f ∘ a))
    direct = post-triangle e Jgf i (Shape.χ (g ∘ f) a)
    top = evAt a ◁ funPre-comp {D = C} f g
    finish = evAt-cong {C = C} (comp-assoc a f g)
    route = (e ◁ restriction-compositor {P = F} f g) ∙ comp-assoc Jf Jg e
    before-beta = (beta-g ▷ Jf) ∙ alpha
    before = (before-beta ▷ i) ∙ mu-composite
    after = (beta-gf ▷ i) ∙ mu-gf
    beta-double = (beta-g ▷ Jf) ▷ i
    iteration-tail = (evAt-pre {C = C} a f ▷ kg) ∙
      ((comp-assoc kg kf (evAt a)) ⁻¹)
    evaluated-tail = (alpha ▷ i) ∙ mu-composite
    direct-factor : evAt-pre {C = C} a (g ∘ f) =₂ (direct ∙ after)
    direct-factor =
      (comp₌-assoc (e ◁ Shape.χ (g ∘ f) a) (comp-assoc i Jgf e) after) ⁻¹ ∙
      RouteGF.factorization
    g-factor : evAt-pre {C = C} (f ∘ a) g =₂
      (point-g ∙ ((beta-g ▷ j) ∙ mu-g))
    g-factor =
      (comp₌-assoc (e ◁ Shape.χ g (f ∘ a)) (comp-assoc j Jg e)
        ((beta-g ▷ j) ∙ mu-g)) ⁻¹ ∙ RouteG.factorization
  left : (evAt a ∘ (kf ∘ kg)) =₁ evAt (g ∘ (f ∘ a))
  left = finish ∙ (evAt-pre {C = C} a (g ∘ f) ∙ top)
  right : (evAt a ∘ (kf ∘ kg)) =₁ evAt (g ∘ (f ∘ a))
  right = evAt-pre {C = C} (f ∘ a) g ∙ iteration-tail
  private
    left-step₁ = comp₌-cong (id₌ finish) (comp₌-cong direct-factor (id₌ top))
    left-step₂ = comp₌-cong (id₌ finish) (comp₌-assoc direct after top)
    left-step₃ = comp₌-cong (id₌ finish) (comp₌-cong (id₌ direct) Native.square)
    left-step₄ = comp₌-cong (id₌ finish)
      ((comp₌-assoc direct (route ▷ i) before) ⁻¹)
    left-step₅ = (comp₌-assoc finish (direct ∙ (route ▷ i)) before) ⁻¹
    left-step₆ = comp₌-cong (Evaluated.composition ⁻¹) (id₌ before)
    left-normal : left =₂ ((point-g ∙ point-f) ∙ before)
    left-normal = left-step₆ ∙ (left-step₅ ∙ (left-step₄ ∙
      (left-step₃ ∙ (left-step₂ ∙ left-step₁))))
    right-start = comp₌-cong (id₌ point-g)
        (comp₌-assoc (beta-g ▷ j) mu-g iteration-tail) ∙
      (comp₌-assoc point-g ((beta-g ▷ j) ∙ mu-g) iteration-tail ∙
        comp₌-cong g-factor (id₌ iteration-tail))
    mixed-normal =
      (comp₌-assoc (funUncurry kg ◁ Shape.χ f a)
        (comp-assoc i Jf (funUncurry kg)) evaluated-tail) ⁻¹ ∙ Mixed.compatibility
    right-mixed = comp₌-cong (id₌ point-g)
      (comp₌-cong (id₌ (beta-g ▷ j)) mixed-normal)
    right-beta = comp₌-cong (id₌ point-g)
        (comp₌-assoc point-f beta-double evaluated-tail) ∙
      (comp₌-cong (id₌ point-g) (comp₌-cong Beta.compatibility (id₌ evaluated-tail)) ∙
        comp₌-cong (id₌ point-g)
          ((comp₌-assoc (beta-g ▷ j)
            (post-triangle (funUncurry kg) Jf i (Shape.χ f a)) evaluated-tail) ⁻¹))
    right-finish = comp₌-cong (id₌ (point-g ∙ point-f))
        (comp₌-cong
          ((preWhisker-comp₌ (beta-g ▷ Jf) alpha i) ⁻¹) (id₌ mu-composite)) ∙
      (comp₌-cong (id₌ (point-g ∙ point-f))
        ((comp₌-assoc beta-double (alpha ▷ i) mu-composite) ⁻¹) ∙
        (comp₌-assoc point-g point-f (beta-double ∙ evaluated-tail)) ⁻¹)
    right-normal : right =₂ ((point-g ∙ point-f) ∙ before)
    right-normal = right-finish ∙ (right-beta ∙ (right-mixed ∙ right-start))
  composition : left =₂ right
  composition = right-normal ⁻¹ ∙ left-normal


  -- The same calculation before reflecting the compositor. This is the
  -- literal image used by UniversalEdges.Degeneracy.edge-image.
  diagram-image : funUncurry (kf ∘ kg) =₁ (e ∘ Jgf)
  diagram-image = (e ◁ restriction-compositor {P = F} f g) ∙
    (comp-assoc Jf Jg e ∙ before-beta)

  private
    image-factor : diagram-image =₂ (route ∙ before-beta)
    image-factor = (comp₌-assoc (e ◁ restriction-compositor {P = F} f g)
      (comp-assoc Jf Jg e) before-beta) ⁻¹
    image-at-point : ((diagram-image ▷ i) ∙ mu-composite) =₂
      ((route ▷ i) ∙ before)
    image-at-point = comp₌-assoc (route ▷ i) (before-beta ▷ i) mu-composite ∙
      (comp₌-cong (preWhisker-comp₌ route before-beta i) (id₌ mu-composite) ∙
        comp₌-cong (preWhisker i ◁ image-factor) (id₌ mu-composite))
    diagram-normal : right =₂
      (finish ∙ (direct ∙ ((diagram-image ▷ i) ∙ mu-composite)))
    diagram-normal = comp₌-cong (id₌ finish)
        (comp₌-cong (id₌ direct) (image-at-point ⁻¹)) ∙
      (comp₌-cong (id₌ finish) (comp₌-assoc direct (route ▷ i) before) ∙
        (comp₌-assoc finish (direct ∙ (route ▷ i)) before ∙
          (comp₌-cong Evaluated.composition (id₌ before) ∙ right-normal)))

  diagram-composition :
    (evAt-cong {C = C} (comp-assoc a f g) ∙
      (post-triangle e Jgf i (Shape.χ (g ∘ f) a) ∙
        ((diagram-image ▷ i) ∙ AtPoint.uncurry-image a (kf ∘ kg)))) =₂
    (evAt-pre {C = C} (f ∘ a) g ∙
      ((evAt-pre {C = C} a f ▷ kg) ∙ ((comp-assoc kg kf (evAt a)) ⁻¹)))
  diagram-composition = diagram-normal ⁻¹
```


## Evaluating an arbitrary restricted diagram family

The shape and parameter calculation above also applies to an arbitrary
family of diagrams. This public interface retains the native precomposition
comparison; the compositor specialization remains unchanged.

```agda
module PrecompositionPointEvaluation {Γ : Context} {I J C P : CAT Γ}
  (a : MAP One I) (f : MAP I J) (h : MAP P (Fun J C)) where
  open MixedEvaluation a f h public using (left; right; compatibility)
```
