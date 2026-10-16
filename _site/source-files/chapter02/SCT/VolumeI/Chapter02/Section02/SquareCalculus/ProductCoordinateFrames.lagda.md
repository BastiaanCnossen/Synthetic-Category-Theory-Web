# Product coordinate frames

Product composition, insertion and separation retain their specified coordinate frames. Pairing compatible coordinate squares and normalizing their composite frames are generic constructions used by endpoint reassociation, named precomposition and terminal-axis calculations.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCalculus.ProductCoordinateFrames where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (c; a)
open Operations
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open Calculus using (pair⁼; pair-pre; pair-β₁; pair-β₂)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-pre)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (insert)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitʳ)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (preWhisker-id₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell-outer)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (restriction-compositor)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (unconst-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp-inv-left)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp-inv-right; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-right)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters
  using (module ParameterInsertion)
open Calculus using (project-pair₁; project-pair₂)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-triangle₁-One; pair⁼-triangle₂-One; pair⁼-cong)
open import SCT.VolumeI.Chapter01.Section03.Products.PairedVertexFrames using (module PairedBaseImage; pair-action-image)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; compatible-quotient; compatible-comp; compatible-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compose-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (postcompose-compose)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell-id; post-triangle-id)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (triangle-whiskered)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell; post-square-cell-inner)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (const-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (postWhisker-id₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (const-pre-change; const-pre-iterated)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (preWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-square-cell-outer)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)

module PastedCoordinateNormalization {Γ : Context} {R X K C L Z P : CAT Γ}
  (rho : MAP R X) (f : MAP X C) (pmid : MAP K C) (F : MAP R K)
  (b : (pmid ∘ F) =₁ (f ∘ rho))
  (pout : MAP L Z) (H : MAP K L) (h : MAP C Z)
  (d : (pout ∘ H) =₁ (h ∘ pmid)) (pi : MAP Z P) where
  private
    c = post-square-cell h rho f pmid F b
    frame = c ∙ restrict-triangle pout H d F
    A = comp-assoc f h pi ▷ rho
    B = post-square-cell (pi ∘ h) rho f pmid F b
    U = comp-assoc pmid h pi ▷ F
    V = post-square-cell pi rho (h ∘ f) (h ∘ pmid) F c
    before = post-square-cell pi rho (h ∘ f) pout (H ∘ F) frame
    Hpost = post-square-cell pi pmid h pout H d
    S = comp-assoc F H (pi ∘ pout)
    M = post-triangle pi pout H d ▷ F
    tail = M ∙ (S ⁻¹)
    out = (comp-assoc rho (h ∘ f) pi) ⁻¹
    inner = comp-assoc F (h ∘ pmid) pi
    input = comp-assoc (H ∘ F) pout pi
    image = pi ◁ frame

    split : (Hpost ▷ F) =₂ ((U ⁻¹) ∙ M)
    split = comp₌-cong (preWhisker-inverse (comp-assoc pmid h pi) F) (id₌ M) ∙
      preWhisker-comp₌ ((comp-assoc pmid h pi) ⁻¹) (post-triangle pi pout H d) F
    cancel : ((A ∙ B) ∙ (U ⁻¹)) =₂ V
    cancel = comp-inv-right V U ∙
      comp₌-cong ((post-square-cell-comp rho f pmid F b h pi) ⁻¹) (id₌ (U ⁻¹))
    restriction : (before ∙ S) =₂ (V ∙ M)
    restriction = (comp₌-assoc out ((pi ◁ c) ∙ inner) M) ⁻¹ ∙
      (comp₌-cong (id₌ out)
        ((comp₌-assoc (pi ◁ c) inner M) ⁻¹ ∙
          (post-restrict-triangle pi pout H F d c ∙ comp₌-assoc image input S)) ∙
        comp₌-assoc out (image ∙ input) S)

  composite : ((pi ∘ pout) ∘ (H ∘ F)) =₁ (((pi ∘ h) ∘ f) ∘ rho)
  composite = B ∙ restrict-triangle (pi ∘ pout) H Hpost F
  direct : ((pi ∘ pout) ∘ (H ∘ F)) =₁ ((pi ∘ (h ∘ f)) ∘ rho)
  direct = before
  compatibility : (A ∙ composite) =₂ direct
  compatibility = comp-inv-right before S ∙
    (comp₌-cong (restriction ⁻¹) (id₌ (S ⁻¹)) ∙
      ((comp₌-assoc V M (S ⁻¹)) ⁻¹ ∙
        (comp₌-cong cancel (id₌ tail) ∙
          (comp₌-cong ((comp₌-assoc A B (U ⁻¹)) ⁻¹) (id₌ tail) ∙
            ((comp₌-assoc A (B ∙ (U ⁻¹)) tail) ⁻¹ ∙
              (comp₌-cong (id₌ A) ((comp₌-assoc B (U ⁻¹) tail) ⁻¹) ∙
                (comp₌-cong (id₌ A)
                  (comp₌-cong (id₌ B) (comp₌-assoc (U ⁻¹) M (S ⁻¹))) ∙
                    comp₌-cong (id₌ A) (comp₌-cong (id₌ B) (comp₌-cong split (id₌ (S ⁻¹)))))))))))

module ProductLiftCompatible {Γ : Context} {X Y U V P : CAT Γ}
  (s : MAP U V) (pi : MAP Y P) {h k : MAP X Y} {q : MAP X P}
  (bh : (pi ∘ h) =₁ q) (bk : (pi ∘ k) =₁ q) (delta : h =₁ k)
  (given : CompatibleOver pi bh bk delta) where
  private
    H = productMap h s
    K = productMap k s
    dh = pair-β₁ (h ∘ pr₁) (s ∘ pr₂)
    dk = pair-β₁ (k ∘ pr₁) (s ∘ pr₂)
    lift = productMap-cong delta (id₌ s)
    sh = post-square-cell pi pr₁ h pr₁ H dh
    sk = post-square-cell pi pr₁ k pr₁ K dk
    square : (sk ∙ ((pi ∘ pr₁) ◁ lift)) =₂ (((pi ◁ delta) ▷ pr₁) ∙ sh)
    square = unconst-sides₌
      (post-square-cell-inner pr₁ pr₁ pi dh dk delta lift
        (productMap-cong-triangle₁ delta (id₌ s)))
    restricted : ((bk ▷ (pr₁ {C = X} {D = U})) ∙ ((pi ◁ delta) ▷ (pr₁ {C = X} {D = U}))) =₂ (bh ▷ (pr₁ {C = X} {D = U}))
    restricted = (preWhisker (pr₁ {C = X} {D = U}) ◁ given) ∙ (preWhisker-comp₌ bk (pi ◁ delta) (pr₁ {C = X} {D = U})) ⁻¹

  source-frame : ((pi ∘ pr₁) ∘ H) =₁ (q ∘ pr₁)
  source-frame = (bh ▷ pr₁) ∙ sh
  target-frame : ((pi ∘ pr₁) ∘ K) =₁ (q ∘ pr₁)
  target-frame = (bk ▷ pr₁) ∙ sk
  compatible : CompatibleOver (pi ∘ pr₁) source-frame target-frame lift
  compatible = comp₌-cong restricted (id₌ sh) ∙
    ((comp₌-assoc (bk ▷ (pr₁ {C = X} {D = U})) ((pi ◁ delta) ▷ (pr₁ {C = X} {D = U})) sh) ⁻¹ ∙
      (comp₌-cong (id₌ (bk ▷ (pr₁ {C = X} {D = U}))) square ∙
        comp₌-assoc (bk ▷ (pr₁ {C = X} {D = U})) sk ((pi ∘ pr₁) ◁ lift)))

module IdentityCoordinatePostcomposition {Γ : Context} {R Q K L P : CAT Γ}
  (rho : MAP R Q) (H : MAP Q K) (pi : MAP K Q)
  (b : (pi ∘ H) =₁ id Q) (projection : MAP L K) (step : MAP R L)
  (beta : (projection ∘ step) =₁ (H ∘ rho)) (g : MAP Q P) where
  private
    c = post-square-cell pi rho H projection step beta
    parameter = comp-unitˡ rho ∙ ((b ▷ rho) ∙ c)
    represented-g = comp-unitʳ g ∙ post-triangle g pi H b
    S = post-square-cell (g ∘ pi) rho H projection step beta
    A = comp-assoc projection pi g ▷ step
    D = comp-assoc H pi g ▷ rho
    B = comp-assoc rho (pi ∘ H) g
    C = comp-assoc rho (id Q) g
    N = comp-assoc step (pi ∘ projection) g
    E = g ◁ c
    u = comp-unitʳ g ▷ rho
    x = (g ◁ b) ▷ rho
    y = g ◁ (b ▷ rho)
    l = g ◁ comp-unitˡ rho
    v = post-square-cell g rho (pi ∘ H) (pi ∘ projection) step c
    beta-rho = comp-unitˡ rho ∙ (b ▷ rho)
    factor-normal : (represented-g ▷ rho) =₂ (u ∙ (x ∙ D))
    factor-normal = comp₌-cong (id₌ u)
      (preWhisker-comp₌ (g ◁ b) (comp-assoc H pi g) rho) ∙
        preWhisker-comp₌ (comp-unitʳ g) (post-triangle g pi H b) rho
    corner : ((u ∙ x) ∙ (B ⁻¹)) =₂ (g ◁ beta-rho)
    corner = (postWhisker-comp₌ g (comp-unitˡ rho) (b ▷ rho)) ⁻¹ ∙
      (comp-inv-right (l ∙ y) B ∙
        (comp₌-cong ((comp₌-assoc l y B) ⁻¹) (id₌ (B ⁻¹)) ∙
          (comp₌-cong (comp₌-cong (id₌ l) (whisker-mixed-One b rho g)) (id₌ (B ⁻¹)) ∙
            (comp₌-cong (comp₌-assoc l C x) (id₌ (B ⁻¹)) ∙
              comp₌-cong (comp₌-cong (triangle-whiskered rho g) (id₌ x)) (id₌ (B ⁻¹))))))
    middle : ((u ∙ x) ∙ v) =₂ ((g ◁ parameter) ∙ N)
    middle = comp₌-cong
        ((postWhisker g ◁ comp₌-assoc (comp-unitˡ rho) (b ▷ rho) c) ∙
          (postWhisker-comp₌ g beta-rho c) ⁻¹) (id₌ N) ∙
      ((comp₌-assoc (g ◁ beta-rho) E N) ⁻¹ ∙
        (comp₌-cong corner (id₌ (E ∙ N)) ∙ (comp₌-assoc (u ∙ x) (B ⁻¹) (E ∙ N)) ⁻¹))

  compatibility : ((represented-g ▷ rho) ∙ S) =₂ (((g ◁ parameter) ∙ N) ∙ A)
  compatibility = comp₌-cong middle (id₌ A) ∙
    ((comp₌-assoc (u ∙ x) v A) ⁻¹ ∙
      ((comp₌-assoc u x (v ∙ A)) ⁻¹ ∙
        (comp₌-cong (id₌ u)
          (comp₌-cong (id₌ x) ((post-square-cell-comp rho H projection step beta pi g) ⁻¹) ∙
            comp₌-assoc x D S) ∙
          (comp₌-assoc u (x ∙ D) S ∙ comp₌-cong factor-normal (id₌ S)))))

module PostcomposedTrianglePasting {Γ : Context} {X Y Z A B : CAT Γ}
  (g : MAP A B) (pi : MAP Z A) (h : MAP Y Z) (f : MAP X Y)
  {q : MAP Y A} {r : MAP X A} (bh : (pi ∘ h) =₁ q) (bf : (q ∘ f) =₁ r) where
  direct : ((g ∘ pi) ∘ (h ∘ f)) =₁ (g ∘ r)
  direct = post-triangle g pi (h ∘ f) (compose-triangle pi h bh f bf)
  composite : ((g ∘ pi) ∘ (h ∘ f)) =₁ (g ∘ r)
  composite = compose-triangle (g ∘ pi) h (post-triangle g pi h bh) f (post-triangle g q f bf)
  normalization : direct =₂ composite
  normalization = (postcompose-compose g pi h f bh bf) ⁻¹

module ProductPairCoordinates {Γ : Context} {T X Y Z W : CAT Γ}
  (f : MAP X Y) (g : MAP Z W) (u : MAP T X) (v : MAP T Z) where
  private
    first = post-triangle f pr₁ (pair u v) (pair-β₁ u v)
    last = post-triangle g pr₂ (pair u v) (pair-β₂ u v)
  source-first : (pr₁ ∘ (productMap f g ∘ pair u v)) =₁ (f ∘ u)
  source-first = first ∙ project-pair₁ (f ∘ pr₁) (g ∘ pr₂) (pair u v)
  target-first : (pr₁ ∘ pair (f ∘ u) (g ∘ v)) =₁ (f ∘ u)
  target-first = pair-β₁ (f ∘ u) (g ∘ v)
  first-compatible : CompatibleOver pr₁ source-first target-first (productMap-pair f g u v)
  first-compatible = pair-evaluation-over₁-One (f ∘ pr₁) (g ∘ pr₂) (pair u v) first last
  source-last : (pr₂ ∘ (productMap f g ∘ pair u v)) =₁ (g ∘ v)
  source-last = last ∙ project-pair₂ (f ∘ pr₁) (g ∘ pr₂) (pair u v)
  target-last : (pr₂ ∘ pair (f ∘ u) (g ∘ v)) =₁ (g ∘ v)
  target-last = pair-β₂ (f ∘ u) (g ∘ v)
  last-compatible : CompatibleOver pr₂ source-last target-last (productMap-pair f g u v)
  last-compatible = pair-evaluation-over₂-One (f ∘ pr₁) (g ∘ pr₂) (pair u v) first last

module ProductCompositionCoordinates {Γ : Context} {X Y Z U V W : CAT Γ}
  (f : MAP X Y) (h : MAP Y Z) (g : MAP U V) (k : MAP V W) where
  private
    change = productMap f g
  first : ((h ∘ pr₁) ∘ change) =₁ ((h ∘ f) ∘ pr₁)
  first = (comp-assoc pr₁ f h) ⁻¹ ∙
    ((h ◁ pair-β₁ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc change pr₁ h)
  last : ((k ∘ pr₂) ∘ change) =₁ ((k ∘ g) ∘ pr₂)
  last = (comp-assoc pr₂ g k) ⁻¹ ∙
    ((k ◁ pair-β₂ (f ∘ pr₁) (g ∘ pr₂)) ∙ comp-assoc change pr₂ k)
  source-first : (pr₁ ∘ (productMap h k ∘ change)) =₁ ((h ∘ f) ∘ pr₁)
  source-first = first ∙ project-pair₁ (h ∘ pr₁) (k ∘ pr₂) change
  target-first : (pr₁ ∘ productMap (h ∘ f) (k ∘ g)) =₁ ((h ∘ f) ∘ pr₁)
  target-first = pair-β₁ ((h ∘ f) ∘ pr₁) ((k ∘ g) ∘ pr₂)
  source-last : (pr₂ ∘ (productMap h k ∘ change)) =₁ ((k ∘ g) ∘ pr₂)
  source-last = last ∙ project-pair₂ (h ∘ pr₁) (k ∘ pr₂) change
  target-last : (pr₂ ∘ productMap (h ∘ f) (k ∘ g)) =₁ ((k ∘ g) ∘ pr₂)
  target-last = pair-β₂ ((h ∘ f) ∘ pr₁) ((k ∘ g) ∘ pr₂)

  first-compatible : CompatibleOver pr₁ source-first target-first (productMap-comp f h g k)
  first-compatible = pair-evaluation-over₁-One (h ∘ pr₁) (k ∘ pr₂) change first last
  last-compatible : CompatibleOver pr₂ source-last target-last (productMap-comp f h g k)
  last-compatible = pair-evaluation-over₂-One (h ∘ pr₁) (k ∘ pr₂) change first last

  module _ {P : CAT Γ} (pi : MAP Z P) where
    source-post : ((pi ∘ pr₁) ∘ (productMap h k ∘ change)) =₁ ((pi ∘ (h ∘ f)) ∘ pr₁)
    source-post = post-square-cell pi pr₁ (h ∘ f) pr₁ (productMap h k ∘ change) source-first
    target-post : ((pi ∘ pr₁) ∘ productMap (h ∘ f) (k ∘ g)) =₁ ((pi ∘ (h ∘ f)) ∘ pr₁)
    target-post = post-square-cell pi pr₁ (h ∘ f) pr₁ (productMap (h ∘ f) (k ∘ g)) target-first
    post-compatible : CompatibleOver (pi ∘ pr₁) source-post target-post (productMap-comp f h g k)
    post-compatible = comp₌-unitˡ-One source-post ∙
      (comp₌-cong bottom-normal (id₌ source-post) ∙
        unconst-sides₌
          (post-square-cell-inner pr₁ pr₁ pi source-first target-first (id₌ (h ∘ f))
            (productMap-comp f h g k) (const-sides₌ original-square)))
      where
        original-square : (target-first ∙ (pr₁ ◁ productMap-comp f h g k)) =₂
          ((id₌ (h ∘ f) ▷ pr₁) ∙ source-first)
        original-square = (comp₌-unitˡ-One source-first ∙
          comp₌-cong (preWhisker-id₌ (h ∘ f) pr₁) (id₌ source-first)) ⁻¹ ∙ first-compatible
        bottom-normal : ((pi ◁ id₌ (h ∘ f)) ▷ pr₁) =₂ id₌ ((pi ∘ (h ∘ f)) ∘ pr₁)
        bottom-normal = preWhisker-id₌ (pi ∘ (h ∘ f)) pr₁ ∙
          (preWhisker pr₁ ◁ postWhisker-id₌ pi (h ∘ f))

module FixedFirstProductComposition {Γ : Context} (P : CAT Γ) {X Y Z : CAT Γ}
  (k : MAP X Y) (h : MAP Y Z) where
  private
    module C = ProductCompositionCoordinates (id P) (id P) k h
    F = productMap (id P) k
    H = productMap (id P) h
    unit = productMap-cong (comp-unitˡ (id P)) (id₌ (h ∘ k))
    full = productMap-comp (id P) (id P) k h
    projected-full = pair-β₂ ((id P ∘ id P) ∘ pr₁) ((h ∘ k) ∘ pr₂)
  projection : (pr₂ ∘ productMap (id P) (h ∘ k)) =₁ ((h ∘ k) ∘ pr₂)
  projection = pair-β₂ (id P ∘ pr₁) ((h ∘ k) ∘ pr₂)
  source = C.source-last
  private
    unit-compatible : (projection ∙ (pr₂ ◁ unit)) =₂ projected-full
    unit-compatible = comp₌-unitˡ-One projected-full ∙
      (comp₌-cong (preWhisker-id₌ (h ∘ k) pr₂) (id₌ projected-full) ∙
        unconst-sides₌ (productMap-cong-triangle₂ (comp-unitˡ (id P)) (id₌ (h ∘ k))))
  compatibility : (projection ∙ (pr₂ ◁ restriction-compositor {P = P} k h)) =₂ source
  compatibility = compatible-comp pr₂ source projected-full projection unit full unit-compatible C.last-compatible

module ProductSecondUnitComposition {Γ : Context} {X Y Z B : CAT Γ}
  (f : MAP X Y) (h : MAP Y Z) where
  private
    module C = ProductCompositionCoordinates f h (id B) (id B)
      using (last; source-last; target-last; last-compatible)
    F = productMap f (id B)
    H = productMap h (id B)
    b = pair-β₂ (f ∘ pr₁) (id B ∘ pr₂)
    u = comp-unitˡ (pr₂ {C = Y} {D = B})
    t = pair-β₂ (h ∘ pr₁) (id B ∘ pr₂)
    closing = (comp-assoc F H pr₂) ⁻¹
    pre = project-pair₂ (h ∘ pr₁) (id B ∘ pr₂) F
    coefficient = comp-unitˡ (pr₂ {C = X} {D = B}) ∙ (comp-unitˡ (id B) ▷ pr₂)
    intermediate : ((comp-unitˡ (id B) ▷ pr₂) ∙ C.source-last) =₂
      (b ∙ restrict-triangle pr₂ H (u ∙ t) F)
    intermediate = comp₌-cong (id₌ b)
        (comp₌-cong ((preWhisker-comp₌ u t F) ⁻¹) (id₌ closing) ∙
          (comp₌-assoc (u ▷ F) (t ▷ F) closing) ⁻¹) ∙
      (comp₌-assoc b (u ▷ F) pre ∙
        (comp₌-cong (post-square-cell-id pr₂ (id B) pr₂ F b) (id₌ pre) ∙
          (comp₌-assoc (comp-unitˡ (id B) ▷ pr₂) C.last pre) ⁻¹))
  source-cell : (pr₂ ∘ (H ∘ F)) =₁ pr₂
  source-cell = compose-triangle pr₂ H (u ∙ t) F (comp-unitˡ pr₂ ∙ b)
  target-cell : (pr₂ ∘ productMap (h ∘ f) (id B ∘ id B)) =₁ pr₂
  target-cell = coefficient ∙ C.target-last
  private
    source-normal : (coefficient ∙ C.source-last) =₂ source-cell
    source-normal = (comp₌-assoc (comp-unitˡ pr₂) b (restrict-triangle pr₂ H (u ∙ t) F)) ⁻¹ ∙
      (comp₌-cong (id₌ (comp-unitˡ pr₂)) intermediate ∙
        comp₌-assoc (comp-unitˡ pr₂) (comp-unitˡ (id B) ▷ pr₂) C.source-last)
  compatible : CompatibleOver pr₂ source-cell target-cell (productMap-comp f h (id B) (id B))
  compatible = source-normal ∙
    (comp₌-cong (id₌ coefficient) C.last-compatible ∙
      comp₌-assoc coefficient C.target-last (pr₂ ◁ productMap-comp f h (id B) (id B)))

module ParameterProductComposition {Γ : Context} {X Y Z U V W P : CAT Γ}
  (f : MAP X Y) (h : MAP Y Z) (g : MAP U V) (k : MAP V W)
  (pi : MAP Z P) (r : MAP Y P) (q : MAP X P)
  (bh : (pi ∘ h) =₁ r) (bf : (r ∘ f) =₁ q) where
  private
    module C = ProductCompositionCoordinates f h g k using (source-post; target-post; post-compatible)
    F = productMap f g
    H = productMap h k
    betaF = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
    betaH = pair-β₁ (h ∘ pr₁) (k ∘ pr₂)
    A = comp-assoc f h pi ▷ (pr₁ {C = X} {D = U})
    B = post-square-cell (pi ∘ h) pr₁ f pr₁ F betaF
    parameter-square = post-square-cell r pr₁ f pr₁ F betaF
    J = post-square-cell pi pr₁ h pr₁ H betaH
    T = comp-assoc F H (pi ∘ pr₁)
    tail = (J ▷ F) ∙ (T ⁻¹)
    base-composite = compose-triangle pi h bh f bf
    c = base-composite ▷ (pr₁ {C = X} {D = U})
    t = (bh ▷ f) ▷ (pr₁ {C = X} {D = U})
    delta = (bh ▷ pr₁) ▷ F
    post-h = (bh ▷ pr₁) ∙ J
    post-f = (bf ▷ (pr₁ {C = X} {D = U})) ∙ parameter-square
    pasted = PastedCoordinateNormalization.compatibility
      pr₁ f pr₁ F betaF pr₁ H h betaH pi
    outer-square : (parameter-square ∙ delta) =₂ (t ∙ B)
    outer-square = unconst-sides₌ (post-square-cell-outer pr₁ f pr₁ F betaF bh)
    coefficient-normal : c =₂ (((bf ▷ (pr₁ {C = X} {D = U})) ∙ t) ∙ (A ⁻¹))
    coefficient-normal = (comp₌-assoc (bf ▷ (pr₁ {C = X} {D = U})) t (A ⁻¹)) ⁻¹ ∙
      (comp₌-cong (id₌ (bf ▷ (pr₁ {C = X} {D = U})))
        (comp₌-cong (id₌ t) (preWhisker-inverse (comp-assoc f h pi) pr₁) ∙
          preWhisker-comp₌ (bh ▷ f) ((comp-assoc f h pi) ⁻¹) pr₁) ∙
        preWhisker-comp₌ bf (restrict-triangle pi h bh f) pr₁)
    coefficient : (c ∙ A) =₂ ((bf ▷ (pr₁ {C = X} {D = U})) ∙ t)
    coefficient = inv-comp-right ((bf ▷ (pr₁ {C = X} {D = U})) ∙ t) A ∙ comp₌-cong coefficient-normal (id₌ A)

  source-cell : ((pi ∘ pr₁) ∘ (H ∘ F)) =₁ (q ∘ pr₁)
  source-cell = compose-triangle (pi ∘ pr₁) H post-h F post-f
  target-cell : ((pi ∘ pr₁) ∘ productMap (h ∘ f) (k ∘ g)) =₁ (q ∘ pr₁)
  target-cell = c ∙ C.target-post pi
  private
    source-normal : source-cell =₂ (post-f ∙ (delta ∙ tail))
    source-normal = comp₌-cong (id₌ post-f)
      (comp₌-assoc delta (J ▷ F) (T ⁻¹) ∙
        comp₌-cong (preWhisker-comp₌ (bh ▷ pr₁) J F) (id₌ (T ⁻¹)))

  compatible : CompatibleOver (pi ∘ pr₁) source-cell target-cell (productMap-comp f h g k)
  compatible = source-normal ⁻¹ ∙
    ((comp₌-assoc (bf ▷ (pr₁ {C = X} {D = U})) parameter-square (delta ∙ tail)) ⁻¹ ∙
      (comp₌-cong (id₌ (bf ▷ (pr₁ {C = X} {D = U})))
        (comp₌-assoc parameter-square delta tail ∙
          (comp₌-cong (outer-square ⁻¹) (id₌ tail) ∙ (comp₌-assoc t B tail) ⁻¹)) ∙
        (comp₌-assoc (bf ▷ (pr₁ {C = X} {D = U})) t (B ∙ tail) ∙
          (comp₌-cong coefficient (id₌ (B ∙ tail)) ∙
            ((comp₌-assoc c A (B ∙ tail)) ⁻¹ ∙
              (comp₌-cong (id₌ c) (pasted ⁻¹) ∙
                (comp₌-cong (id₌ c) (C.post-compatible pi) ∙
                  comp₌-assoc c (C.target-post pi) ((pi ∘ pr₁) ◁ productMap-comp f h g k))))))))

module ParameterInsertionFirstCoordinate {Γ : Context} {P Q J : CAT Γ}
  (a : MAP One J) (g : MAP Q P) where
  private
    module Native = ParameterInsertion a using (front; back; value)
    x = const {P = Q} a
    module Pair = ProductPairCoordinates g (id J) (id Q) x
      using (source-first; target-first; first-compatible)
    close = pair⁼ (comp-unitʳ g) (comp-unitˡ x)
    mid = comp-unitʳ g ∙ Pair.target-first
    normal = pair-β₁ g x
  source-first : (pr₁ ∘ (insert {P = P} a ∘ g)) =₁ g
  source-first = comp-unitˡ g ∙ project-pair₁ (id P) (const a) g
  target-first : (pr₁ ∘ (productMap g (id J) ∘ insert {P = Q} a)) =₁ g
  target-first = comp-unitʳ g ∙ Pair.source-first
  private
    front-compatible : CompatibleOver pr₁ source-first normal (Native.front g)
    front-compatible = pair-evaluation-over₁-One (id P) (const a) g (comp-unitˡ g) (const-pre a g)
    back-compatible : CompatibleOver pr₁ target-first normal (Native.back g)
    back-compatible = compatible-comp pr₁ target-first mid normal close
      (productMap-pair g (id J) (id Q) x)
      (pair⁼-triangle₁-One (comp-unitʳ g) (comp-unitˡ x))
      (comp₌-cong (id₌ (comp-unitʳ g)) Pair.first-compatible ∙
        comp₌-assoc (comp-unitʳ g) Pair.target-first (pr₁ ◁ productMap-pair g (id J) (id Q) x))
  compatible : CompatibleOver pr₁ source-first target-first (Native.value g)
  compatible = compatible-quotient pr₁ source-first target-first normal
    (Native.front g) (Native.back g) front-compatible back-compatible

  target-composite : (pr₁ ∘ (productMap g (id J) ∘ insert {P = Q} a)) =₁ g
  target-composite = compose-triangle pr₁ (productMap g (id J))
    (pair-β₁ (g ∘ pr₁) (id J ∘ pr₂)) (insert {P = Q} a)
    (comp-unitʳ g ∙ post-triangle g pr₁ (insert {P = Q} a) (pair-β₁ (id Q) x))
  target-normalization : target-composite =₂ target-first
  target-normalization = comp₌-assoc (comp-unitʳ g)
    (post-triangle g pr₁ (insert {P = Q} a) (pair-β₁ (id Q) x))
    (project-pair₁ (g ∘ pr₁) (id J ∘ pr₂) (insert {P = Q} a))
  composite-compatible : CompatibleOver pr₁ source-first target-composite (Native.value g)
  composite-compatible = compatible ∙ comp₌-cong target-normalization (id₌ (pr₁ ◁ Native.value g))

module ParameterInsertionSecondCoordinate {Γ : Context} {P Q J : CAT Γ}
  (a : MAP One J) (g : MAP Q P) where
  private
    module Native = ParameterInsertion a using (front; back; value)
    x = const {P = Q} a
    module Pair = ProductPairCoordinates g (id J) (id Q) x
      using (source-last; target-last; last-compatible)
    close = pair⁼ (comp-unitʳ g) (comp-unitˡ x)
    mid = comp-unitˡ x ∙ Pair.target-last
    normal = pair-β₂ g x
  source-last : (pr₂ ∘ (insert {P = P} a ∘ g)) =₁ x
  source-last = const-pre a g ∙ project-pair₂ (id P) (const a) g
  target-last : (pr₂ ∘ (productMap g (id J) ∘ insert {P = Q} a)) =₁ x
  target-last = comp-unitˡ x ∙ Pair.source-last
  private
    front-compatible : CompatibleOver pr₂ source-last normal (Native.front g)
    front-compatible = pair-evaluation-over₂-One (id P) (const a) g (comp-unitˡ g) (const-pre a g)
    back-compatible : CompatibleOver pr₂ target-last normal (Native.back g)
    back-compatible = compatible-comp pr₂ target-last mid normal close (productMap-pair g (id J) (id Q) x)
      (pair⁼-triangle₂-One (comp-unitʳ g) (comp-unitˡ x))
      (comp₌-cong (id₌ (comp-unitˡ x)) Pair.last-compatible ∙
        comp₌-assoc (comp-unitˡ x) Pair.target-last (pr₂ ◁ productMap-pair g (id J) (id Q) x))
  compatible : CompatibleOver pr₂ source-last target-last (Native.value g)
  compatible = compatible-quotient pr₂ source-last target-last normal
    (Native.front g) (Native.back g) front-compatible back-compatible
  target-composite : (pr₂ ∘ (productMap g (id J) ∘ insert {P = Q} a)) =₁ x
  target-composite = compose-triangle pr₂ (productMap g (id J))
    (comp-unitˡ pr₂ ∙ pair-β₂ (g ∘ pr₁) (id J ∘ pr₂)) (insert {P = Q} a) (pair-β₂ (id Q) x)
  target-normalization : target-last =₂ target-composite
  target-normalization = comp₌-cong (id₌ b)
      (comp₌-cong ((preWhisker-comp₌ u t insertion) ⁻¹) (id₌ closing) ∙
        (comp₌-assoc (u ▷ insertion) (t ▷ insertion) closing) ⁻¹) ∙
    (comp₌-assoc b (u ▷ insertion) pre ∙
      (comp₌-cong (post-triangle-id pr₂ insertion b) (id₌ pre) ∙
        (comp₌-assoc (comp-unitˡ x) (post-triangle (id J) pr₂ insertion b) pre) ⁻¹))
    where
      insertion = insert {P = Q} a
      b = pair-β₂ (id Q) x
      u = comp-unitˡ (pr₂ {C = Q} {D = J})
      t = pair-β₂ (g ∘ pr₁) (id J ∘ pr₂)
      closing = (comp-assoc insertion (productMap g (id J)) pr₂) ⁻¹
      pre = project-pair₂ (g ∘ pr₁) (id J ∘ pr₂) insertion
  composite-compatible : CompatibleOver pr₂ source-last target-composite (Native.value g)
  composite-compatible = compatible ∙ comp₌-cong (target-normalization ⁻¹) (id₌ (pr₂ ◁ Native.value g))

module ConstantCoordinateSquare {Γ : Context} {R X K Y J : CAT Γ}
  (a : MAP One J) (rho : MAP R X) (g : MAP X Y) (pi : MAP K Y)
  (F : MAP R K) (b : (pi ∘ F) =₁ (g ∘ rho)) where
  private
    A = comp-assoc rho g (const {P = Y} a)
    tail = post-triangle (const {P = Y} a) pi F b
    coefficient = const-pre a rho ∙ (const-pre a g ▷ rho)
  compatibility : (coefficient ∙ post-square-cell (const {P = Y} a) rho g pi F b) =₂
    (const-pre a F ∙ (const-pre a pi ▷ F))
  compatibility = const-pre-change a pi F (g ∘ rho) b ∙
    (comp₌-cong (id₌ (const-pre a (g ∘ rho))) (comp-inv-left A tail) ∙
      (comp₌-assoc (const-pre a (g ∘ rho)) A ((A ⁻¹) ∙ tail) ∙
        comp₌-cong ((const-pre-iterated a g rho) ⁻¹) (id₌ ((A ⁻¹) ∙ tail))))

module ProductSeparationFirstCoordinate {Γ : Context} {A B C D : CAT Γ}
  (f : MAP A C) (g : MAP B D) where
  private
    module L = ProductCompositionCoordinates f (id C) (id B) g
      using (first; source-first; target-first; first-compatible)
    module R = ProductCompositionCoordinates (id A) f g (id D)
      using (first; source-first; target-first; first-compatible)
    lp = productMap-comp f (id C) (id B) g
    lq = productMap-cong (comp-unitˡ f) (comp-unitʳ g)
    rp = productMap-comp (id A) f g (id D)
    rq = productMap-cong (comp-unitʳ f) (comp-unitˡ g)
    lu = comp-unitˡ f ▷ (pr₁ {C = A} {D = B})
    ru = comp-unitʳ f ▷ (pr₁ {C = A} {D = B})
    midL = lu ∙ L.target-first
    midR = ru ∙ R.target-first
    normal = pair-β₁ (f ∘ pr₁) (g ∘ pr₂)
  source-first : (pr₁ ∘ (productMap (id C) g ∘ productMap f (id B))) =₁ (f ∘ pr₁)
  source-first = lu ∙ L.source-first
  target-first : (pr₁ ∘ (productMap f (id D) ∘ productMap (id A) g)) =₁ (f ∘ pr₁)
  target-first = ru ∙ R.source-first
  private
    lp-compatible : CompatibleOver pr₁ source-first midL lp
    lp-compatible = comp₌-cong (id₌ lu) L.first-compatible ∙ comp₌-assoc lu L.target-first (pr₁ ◁ lp)
    rp-compatible : CompatibleOver pr₁ target-first midR rp
    rp-compatible = comp₌-cong (id₌ ru) R.first-compatible ∙ comp₌-assoc ru R.target-first (pr₁ ◁ rp)
    lq-compatible : CompatibleOver pr₁ midL normal lq
    lq-compatible = unconst-sides₌ (productMap-cong-triangle₁ (comp-unitˡ f) (comp-unitʳ g))
    rq-compatible : CompatibleOver pr₁ midR normal rq
    rq-compatible = unconst-sides₌ (productMap-cong-triangle₁ (comp-unitʳ f) (comp-unitˡ g))
  compatible : CompatibleOver pr₁ source-first target-first (productMap-separate f g)
  compatible = compatible-comp pr₁ source-first midR target-first (rp ⁻¹) ((rq ⁻¹) ∙ (lq ∙ lp))
    (compatible-inverse pr₁ target-first midR rp rp-compatible)
    (compatible-comp pr₁ source-first normal midR (rq ⁻¹) (lq ∙ lp)
      (compatible-inverse pr₁ midR normal rq rq-compatible)
      (compatible-comp pr₁ source-first midL normal lq lp lq-compatible lp-compatible))

  source-composite : (pr₁ ∘ (productMap (id C) g ∘ productMap f (id B))) =₁ (f ∘ pr₁)
  source-composite = compose-triangle pr₁ (productMap (id C) g)
    (comp-unitˡ pr₁ ∙ pair-β₁ (id C ∘ pr₁) (g ∘ pr₂)) (productMap f (id B))
    (pair-β₁ (f ∘ pr₁) (id B ∘ pr₂))
  source-normalization : source-first =₂ source-composite
  source-normalization = comp₌-cong (id₌ b)
      (comp₌-cong ((preWhisker-comp₌ u t change) ⁻¹) (id₌ closing) ∙
        (comp₌-assoc (u ▷ change) (t ▷ change) closing) ⁻¹) ∙
    (comp₌-assoc b (u ▷ change) pre ∙
      (comp₌-cong (post-square-cell-id pr₁ f pr₁ change b) (id₌ pre) ∙
        (comp₌-assoc lu L.first pre) ⁻¹))
    where
      change = productMap f (id B)
      b = pair-β₁ (f ∘ pr₁) (id B ∘ pr₂)
      u = comp-unitˡ (pr₁ {C = C} {D = B})
      t = pair-β₁ (id C ∘ pr₁) (g ∘ pr₂)
      closing = (comp-assoc change (productMap (id C) g) pr₁) ⁻¹
      pre = project-pair₁ (id C ∘ pr₁) (g ∘ pr₂) change

  target-composite : (pr₁ ∘ (productMap f (id D) ∘ productMap (id A) g)) =₁ (f ∘ pr₁)
  target-composite = compose-triangle pr₁ (productMap f (id D))
    (pair-β₁ (f ∘ pr₁) (id D ∘ pr₂)) (productMap (id A) g)
    (post-triangle f pr₁ (productMap (id A) g)
      (comp-unitˡ pr₁ ∙ pair-β₁ (id A ∘ pr₁) (g ∘ pr₂)))
  target-normalization : target-first =₂ target-composite
  target-normalization = comp₌-cong normalized (id₌ pre) ∙ (comp₌-assoc ru R.first pre) ⁻¹
    where
      change = productMap (id A) g
      u = comp-unitˡ (pr₁ {C = A} {D = B})
      b = pair-β₁ (id A ∘ pr₁) (g ∘ pr₂)
      assoc = comp-assoc pr₁ (id A) f
      after = comp-assoc change pr₁ f
      pre = project-pair₁ (f ∘ pr₁) (id D ∘ pr₂) change
      corner : (ru ∙ assoc ⁻¹) =₂ (f ◁ u)
      corner = comp-inv-right (f ◁ u) assoc ∙ comp₌-cong (triangle-whiskered pr₁ f) (id₌ (assoc ⁻¹))
      normalized : (ru ∙ R.first) =₂ post-triangle f pr₁ change (u ∙ b)
      normalized = comp₌-cong ((postWhisker-comp₌ f u b) ⁻¹) (id₌ after) ∙
        ((comp₌-assoc (f ◁ u) (f ◁ b) after) ⁻¹ ∙
          (comp₌-cong corner (id₌ ((f ◁ b) ∙ after)) ∙
            (comp₌-assoc ru (assoc ⁻¹) ((f ◁ b) ∙ after)) ⁻¹))

  composite-compatible : CompatibleOver pr₁ source-composite target-composite (productMap-separate f g)
  composite-compatible = source-normalization ∙
    (compatible ∙ comp₌-cong (target-normalization ⁻¹) (id₌ (pr₁ ◁ productMap-separate f g)))
module ProductSeparationSecondCoordinate {Γ : Context} {A B C D : CAT Γ}
  (f : MAP A C) (g : MAP B D) where
  private
    module L = ProductCompositionCoordinates f (id C) (id B) g
      using (last; source-last; target-last; last-compatible)
    module R = ProductCompositionCoordinates (id A) f g (id D)
      using (last; source-last; target-last; last-compatible)
    lp = productMap-comp f (id C) (id B) g
    lq = productMap-cong (comp-unitˡ f) (comp-unitʳ g)
    rp = productMap-comp (id A) f g (id D)
    rq = productMap-cong (comp-unitʳ f) (comp-unitˡ g)
    lu = comp-unitʳ g ▷ (pr₂ {C = A} {D = B})
    ru = comp-unitˡ g ▷ (pr₂ {C = A} {D = B})
    midL = lu ∙ L.target-last
    midR = ru ∙ R.target-last
    normal = pair-β₂ (f ∘ pr₁) (g ∘ pr₂)
  source-last : (pr₂ ∘ (productMap (id C) g ∘ productMap f (id B))) =₁ (g ∘ pr₂)
  source-last = lu ∙ L.source-last
  target-last : (pr₂ ∘ (productMap f (id D) ∘ productMap (id A) g)) =₁ (g ∘ pr₂)
  target-last = ru ∙ R.source-last
  private
    lp-compatible = comp₌-cong (id₌ lu) L.last-compatible ∙ comp₌-assoc lu L.target-last (pr₂ ◁ lp)
    rp-compatible = comp₌-cong (id₌ ru) R.last-compatible ∙ comp₌-assoc ru R.target-last (pr₂ ◁ rp)
    lq-compatible = unconst-sides₌ (productMap-cong-triangle₂ (comp-unitˡ f) (comp-unitʳ g))
    rq-compatible = unconst-sides₌ (productMap-cong-triangle₂ (comp-unitʳ f) (comp-unitˡ g))
  compatible : CompatibleOver pr₂ source-last target-last (productMap-separate f g)
  compatible = compatible-comp pr₂ source-last midR target-last (rp ⁻¹) ((rq ⁻¹) ∙ (lq ∙ lp))
    (compatible-inverse pr₂ target-last midR rp rp-compatible)
    (compatible-comp pr₂ source-last normal midR (rq ⁻¹) (lq ∙ lp)
      (compatible-inverse pr₂ midR normal rq rq-compatible)
      (compatible-comp pr₂ source-last midL normal lq lp lq-compatible lp-compatible))

  source-composite : (pr₂ ∘ (productMap (id C) g ∘ productMap f (id B))) =₁ (g ∘ pr₂)
  source-composite = compose-triangle pr₂ (productMap (id C) g)
    (pair-β₂ (id C ∘ pr₁) (g ∘ pr₂)) (productMap f (id B))
    (post-triangle g pr₂ (productMap f (id B))
      (comp-unitˡ pr₂ ∙ pair-β₂ (f ∘ pr₁) (id B ∘ pr₂)))
  source-normalization : source-last =₂ source-composite
  source-normalization = comp₌-cong normalized (id₌ pre) ∙ (comp₌-assoc lu L.last pre) ⁻¹
    where
      change = productMap f (id B)
      u = comp-unitˡ (pr₂ {C = A} {D = B})
      b = pair-β₂ (f ∘ pr₁) (id B ∘ pr₂)
      assoc = comp-assoc pr₂ (id B) g
      after = comp-assoc change pr₂ g
      pre = project-pair₂ (id C ∘ pr₁) (g ∘ pr₂) change
      corner = comp-inv-right (g ◁ u) assoc ∙ comp₌-cong (triangle-whiskered pr₂ g) (id₌ (assoc ⁻¹))
      normalized = comp₌-cong ((postWhisker-comp₌ g u b) ⁻¹) (id₌ after) ∙
        ((comp₌-assoc (g ◁ u) (g ◁ b) after) ⁻¹ ∙
          (comp₌-cong corner (id₌ ((g ◁ b) ∙ after)) ∙
            (comp₌-assoc lu (assoc ⁻¹) ((g ◁ b) ∙ after)) ⁻¹))
  target-composite : (pr₂ ∘ (productMap f (id D) ∘ productMap (id A) g)) =₁ (g ∘ pr₂)
  target-composite = compose-triangle pr₂ (productMap f (id D))
    (comp-unitˡ pr₂ ∙ pair-β₂ (f ∘ pr₁) (id D ∘ pr₂)) (productMap (id A) g)
    (pair-β₂ (id A ∘ pr₁) (g ∘ pr₂))
  target-normalization : target-last =₂ target-composite
  target-normalization = comp₌-cong (id₌ b)
      (comp₌-cong ((preWhisker-comp₌ u t change) ⁻¹) (id₌ closing) ∙
        (comp₌-assoc (u ▷ change) (t ▷ change) closing) ⁻¹) ∙
    (comp₌-assoc b (u ▷ change) pre ∙
      (comp₌-cong (post-square-cell-id pr₂ g pr₂ change b) (id₌ pre) ∙ (comp₌-assoc ru R.last pre) ⁻¹))
    where
      change = productMap (id A) g
      b = pair-β₂ (id A ∘ pr₁) (g ∘ pr₂)
      u = comp-unitˡ (pr₂ {C = A} {D = D})
      t = pair-β₂ (f ∘ pr₁) (id D ∘ pr₂)
      closing = (comp-assoc change (productMap f (id D)) pr₂) ⁻¹
      pre = project-pair₂ (f ∘ pr₁) (id D ∘ pr₂) change
  composite-compatible : CompatibleOver pr₂ source-composite target-composite (productMap-separate f g)
  composite-compatible = source-normalization ∙
    (compatible ∙ comp₌-cong (target-normalization ⁻¹) (id₌ (pr₂ ◁ productMap-separate f g)))

module PairedCoordinateComposition {Γ : Context} {K L T C D : CAT Γ}
  (pi : MAP K C) (tau : MAP K D) (h : MAP L K) (f : MAP T L)
  {x : MAP L C} {y : MAP L D} {u : MAP T C} {v : MAP T D}
  (bh : (pi ∘ h) =₁ x) (ch : (tau ∘ h) =₁ y)
  (bf : (x ∘ f) =₁ u) (cf : (y ∘ f) =₁ v) where
  private
    p = pair pi tau
    old = pair⁼ bh ch ∙ pair-pre pi tau h
    finish = pair⁼ bf cf ∙ pair-pre x y f
    left = compose-triangle pi h bh f bf
    right = compose-triangle tau h ch f cf
    A = comp-assoc f h p
    scalar : {E : CAT Γ} (e : MAP K E) {z : MAP L E} {w : MAP T E}
      (b : (e ∘ h) =₁ z) (c : (z ∘ f) =₁ w)
      → (compose-triangle e h b f c ∙ ((e ◁ id₌ (h ∘ f)) ∙ comp-assoc f h e)) =₂ (c ∙ (b ▷ f))
    scalar e b c = inv-comp-right (c ∙ (b ▷ f)) a ∙
      (comp₌-cong ((comp₌-assoc c (b ▷ f) (a ⁻¹)) ⁻¹) (id₌ a) ∙
        comp₌-cong (id₌ (compose-triangle e h b f c))
          (comp₌-unitˡ-One a ∙ comp₌-cong (postWhisker-id₌ e (h ∘ f)) (id₌ a)))
      where a = comp-assoc f h e
    module Image = PairedBaseImage pi tau h f (h ∘ f) (id₌ (h ∘ f)) bh ch left right bf cf
      (scalar pi bh bf) (scalar tau ch cf) using (image)
  direct : (p ∘ (h ∘ f)) =₁ pair u v
  direct = pair⁼ left right ∙ pair-pre pi tau (h ∘ f)
  composite : (p ∘ (h ∘ f)) =₁ pair u v
  composite = compose-triangle p h old f finish
  normalization : composite =₂ direct
  normalization = comp-inv-right direct A ∙
    (comp₌-cong (normalized ⁻¹) (id₌ (A ⁻¹)) ∙ (comp₌-assoc finish (old ▷ f) (A ⁻¹)) ⁻¹)
    where
      normalized : (direct ∙ A) =₂ (finish ∙ (old ▷ f))
      normalized = Image.image ∙ comp₌-cong (id₌ direct)
        ((comp₌-unitˡ-One A ∙ comp₌-cong (postWhisker-id₌ p (h ∘ f)) (id₌ A)) ⁻¹)

module PairedCompatibleCoordinates {Γ : Context} {T K C D : CAT Γ}
  (pi : MAP K C) (tau : MAP K D) {h k : MAP T K} (delta : h =₁ k)
  {u : MAP T C} {v : MAP T D}
  (bh : (pi ∘ h) =₁ u) (bk : (pi ∘ k) =₁ u)
  (ch : (tau ∘ h) =₁ v) (ck : (tau ∘ k) =₁ v)
  (left : CompatibleOver pi bh bk delta) (right : CompatibleOver tau ch ck delta) where
  source-frame : (pair pi tau ∘ h) =₁ pair u v
  source-frame = pair⁼ bh ch ∙ pair-pre pi tau h
  target-frame : (pair pi tau ∘ k) =₁ pair u v
  target-frame = pair⁼ bk ck ∙ pair-pre pi tau k
  compatible : CompatibleOver (pair pi tau) source-frame target-frame delta
  compatible = comp₌-cong (pair⁼-cong left right) (id₌ (pair-pre pi tau h)) ∙
    pair-action-image pi tau delta bk ck

```
