# Terminal section coordinates

The terminal-product section and decoding maps retain their chosen contraction and first/second image computations. These computations are used by actual endpoint decoding in the geometric naturality square.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.SquareCalculus.TerminalSectionCoordinates where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (c; a)
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; module Composition)
open Composition
open Calculus using (pair⁼; pair-β₁; pair-β₂)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-pre)
open Constructions using (terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitʳ)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-One)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (product-unitˡ-inverse)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp₌-cong; comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compatible-unitʳ)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.SectionEvaluation using (module SectionEvaluation)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (product-unitˡ-inverse-pr₂; product-unitˡ-pr₂-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (right-unitor-comp; preWhisker-id-One)
open Calculus using (pair₌-β₂)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp-inv-left)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport using (identification-restriction)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares using (replace-sides₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (preWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (comp-inv-right; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-right)
open Calculus using (project-pair₁; project-pair₂)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-triangle₁-One; pair⁼-triangle₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase
  using (CompatibleOver; compatible-postcompose; compatible-comp; compatible-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compose-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (compatible-assoc; compatible-pre; compatible-post)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle-id)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (triangle-whiskered)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (const-pre-iterated)
open import SCT.VolumeI.Chapter01.Section02.Specialization using (inv-comp-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (whisker-mixed-One)
open import SCT.VolumeI.Chapter02.Section02.SquareCalculus.ProductCoordinateFrames using (module ProductPairCoordinates)

module TerminalPostTriangle {Γ : Context} {R X I : CAT Γ}
  (x : MAP One I) (pi : MAP X One) (r : MAP R X) (b : (pi ∘ r) =₁ terminate R) where
  private
    u = terminal-identification pi (terminate X)
    v = terminal-identification (terminate X ∘ r) (terminate R)
    A = comp-assoc r pi x
  compatibility : (const-pre x r ∙ ((x ◁ u) ▷ r)) =₂ post-triangle x pi r b
  compatibility = comp₌-cong (postWhisker x ◁ terminal-unique₂ (v ∙ (u ▷ r)) b) (id₌ A) ∙
    (comp₌-cong ((postWhisker-comp₌ x v (u ▷ r)) ⁻¹) (id₌ A) ∙
      ((comp₌-assoc (x ◁ v) (x ◁ (u ▷ r)) A) ⁻¹ ∙
        (comp₌-cong (id₌ (x ◁ v)) (whisker-mixed-One u r x) ∙
          comp₌-assoc (x ◁ v) (comp-assoc r (terminate X) x) ((x ◁ u) ▷ r))))

module ConstantSectionContraction {Γ : Context} {K X I : CAT Γ}
  (x : MAP One I) (t : MAP X K) (q : MAP K X) (c : (t ∘ q) =₁ id K) where
  private
    k = const {P = K} x
    source = terminal-identification (terminate K ∘ (t ∘ q)) (terminate K)
    target = comp-unitʳ (terminate K)
    A = comp-assoc q t k
    lower = compose-triangle k t (const-pre x t) q (const-pre x q)
    lower-normalization : lower =₂ const-pre x (t ∘ q)
    lower-normalization = comp-inv-right (const-pre x (t ∘ q)) A ∙
      (comp₌-cong ((const-pre-iterated x t q) ⁻¹) (id₌ (A ⁻¹)) ∙
        (comp₌-assoc (const-pre x q) (const-pre x t ▷ q) (A ⁻¹)) ⁻¹)
  compatibility : (comp-unitʳ k ∙ (k ◁ c)) =₂
    compose-triangle k t (const-pre x t) q (const-pre x q)
  compatibility = (lower-normalization ⁻¹) ∙
    (compatible-postcompose x (terminate K) source target c
      (terminal-unique₂ (target ∙ (terminate K ◁ c)) source) ∙
      comp₌-cong (right-unitor-comp (terminate K) x) (id₌ (k ◁ c)))

module SectionDecodeOverBase {Γ : Context} {K X Y Z : CAT Γ}
  (pi : MAP Y Z) (F : MAP K Y) (axis : MAP X Y)
  (t : MAP X K) (q : MAP K X) (c : (t ∘ q) =₁ id K)
  (k : MAP K Z) (u : MAP X Z)
  (bf : (pi ∘ F) =₁ k) (bt : (k ∘ t) =₁ u) (bq : (u ∘ q) =₁ k)
  (ba : (pi ∘ axis) =₁ u) (eta : (F ∘ t) =₁ axis)
  (eta-compatible : CompatibleOver pi (compose-triangle pi F bf t bt) ba eta)
  (c-compatible : CompatibleOver k (compose-triangle k t bt q bq) (comp-unitʳ k) c) where
  private
    at = compose-triangle pi F bf t bt
    s0 = compose-triangle pi axis ba q bq
    s1 = compose-triangle pi (F ∘ t) at q bq
    s2 = compose-triangle pi F bf (t ∘ q) (compose-triangle k t bt q bq)
    s3 = compose-triangle pi F bf (id K) (comp-unitʳ k)
  decode = comp-unitʳ F ∙ ((F ◁ c) ∙ (comp-assoc q t F ∙ ((eta ⁻¹) ▷ q)))
  compatibility : (bf ∙ (pi ◁ decode)) =₂ s0
  compatibility = compatible-comp pi s0 s3 bf (comp-unitʳ F)
    ((F ◁ c) ∙ (comp-assoc q t F ∙ ((eta ⁻¹) ▷ q))) (compatible-unitʳ pi F bf)
    (compatible-comp pi s0 s2 s3 (F ◁ c)
      (comp-assoc q t F ∙ ((eta ⁻¹) ▷ q))
      (compatible-post pi F bf (compose-triangle k t bt q bq) (comp-unitʳ k) c c-compatible)
      (compatible-comp pi s0 s1 s2 (comp-assoc q t F) ((eta ⁻¹) ▷ q)
        (compatible-assoc pi F t q bf bt bq)
        (compatible-pre pi q ba at bq (eta ⁻¹)
          (compatible-inverse pi at ba eta eta-compatible))))

module ConstantTerminalRestriction {Γ : Context} {R I : CAT Γ}
  (x : MAP One I) (r : MAP R One) where
  private
    u = terminal-identification {Γ = Γ} (terminate One) (id One)
    v = terminal-identification r (terminate R)
    inner = comp-unitˡ r ∙ (u ▷ r)
    A = comp-assoc r (terminate One) x
    unit-restriction : (const-One x ▷ r) =₂ ((x ◁ inner) ∙ A)
    unit-restriction = comp₌-cong ((postWhisker-comp₌ x (comp-unitˡ r) (u ▷ r)) ⁻¹) (id₌ A) ∙
      ((comp₌-assoc (x ◁ comp-unitˡ r) (x ◁ (u ▷ r)) A) ⁻¹ ∙
        (comp₌-cong (id₌ (x ◁ comp-unitˡ r)) (whisker-mixed-One u r x) ∙
          (comp₌-assoc (x ◁ comp-unitˡ r) (comp-assoc r (id One) x) ((x ◁ u) ▷ r) ∙
            (comp₌-cong (triangle-whiskered r x) (id₌ ((x ◁ u) ▷ r)) ∙
              preWhisker-comp₌ (comp-unitʳ x) (x ◁ u) r))))
  compatibility : ((x ◁ v) ∙ (const-One x ▷ r)) =₂ const-pre x r
  compatibility = comp₌-cong
    (postWhisker x ◁ terminal-unique₂ (v ∙ inner)
      (terminal-identification (terminate One ∘ r) (terminate R))) (id₌ A) ∙
      (comp₌-cong ((postWhisker-comp₌ x v inner) ⁻¹) (id₌ A) ∙
        ((comp₌-assoc (x ◁ v) (x ◁ inner) A) ⁻¹ ∙
          comp₌-cong (id₌ (x ◁ v)) unit-restriction))

module TerminalProductSection {Γ : Context} (B : CAT Γ) where
  q = pr₂ {C = One} {D = B}
  t = product-unitˡ-inverse B
  contraction = product-unitˡ-inverse-pr₂ B
  private
    b = product-unitˡ-pr₂-inverse B
    module Section = SectionEvaluation q t b
    source = compose-triangle q t b q (comp-unitˡ q)
    contraction-compatible : (comp-unitʳ q ∙ (q ◁ contraction)) =₂ source
    contraction-compatible = comp-inv-left (comp-unitʳ q) source ∙
      comp₌-cong (id₌ (comp-unitʳ q))
        (pair₌-β₂ (terminal-identification _ _) ((comp-unitʳ q) ⁻¹ ∙ source))
  image : {C : CAT Γ} (w : MAP B C) → ((w ∘ q) ∘ t) =₁ w
  image = Section.image
  projection-compatibility : (comp-unitʳ q ∙ (q ◁ contraction)) =₂
    compose-triangle q t b q (comp-unitˡ q)
  projection-compatibility = contraction-compatible
  roundtrip : {C : CAT Γ} (w : MAP B C) → (image w ▷ q) =₂
    (comp-unitʳ (w ∘ q) ∙ (((w ∘ q) ◁ contraction) ∙ comp-assoc q t (w ∘ q)))
  roundtrip w = comp₌-assoc (comp-unitʳ (w ∘ q)) ((w ∘ q) ◁ contraction) (comp-assoc q t (w ∘ q)) ∙
    (comp₌-cong
      (comp₌-cong ((right-unitor-comp q w) ⁻¹) (id₌ ((w ∘ q) ◁ contraction)) ∙
        (compatible-postcompose w q source (comp-unitʳ q) contraction contraction-compatible) ⁻¹)
      (id₌ (comp-assoc q t (w ∘ q))) ∙
      (comp₌-cong (Section.Restriction.compatibility q w) (id₌ (comp-assoc q t (w ∘ q))) ∙
        (inv-comp-right (image w ▷ q) (comp-assoc q t (w ∘ q))) ⁻¹))
  module Frame {C : CAT Γ} (w : MAP B C) (h : MAP (One × B) C) (alpha : h =₁ (w ∘ q)) where
    private
      left = (h ◁ contraction) ∙ comp-assoc q t h
      right = ((w ∘ q) ◁ contraction) ∙ comp-assoc q t (w ∘ q)
      restriction : (right ∙ ((alpha ▷ t) ▷ q)) =₂ ((alpha ▷ id (One × B)) ∙ left)
      restriction = replace-sides₌
        (comp₌-cong (id₌ (h ◁ contraction)) (const-One (comp-assoc q t h)))
        (comp₌-cong (id₌ ((w ∘ q) ◁ contraction)) (const-One (comp-assoc q t (w ∘ q))))
        (identification-restriction alpha t q (id (One × B)) contraction)
    compatibility : ((image w ▷ q) ∙ ((alpha ▷ t) ▷ q)) =₂
      (alpha ∙ (comp-unitʳ h ∙ ((h ◁ contraction) ∙ comp-assoc q t h)))
    compatibility = comp₌-assoc alpha (comp-unitʳ h) left ∙
      (comp₌-cong (preWhisker-id-One alpha) (id₌ left) ∙
        ((comp₌-assoc (comp-unitʳ (w ∘ q)) (alpha ▷ id (One × B)) left) ⁻¹ ∙
          (comp₌-cong (id₌ (comp-unitʳ (w ∘ q))) restriction ∙
            (comp₌-assoc (comp-unitʳ (w ∘ q)) right ((alpha ▷ t) ▷ q) ∙
              comp₌-cong (roundtrip w) (id₌ ((alpha ▷ t) ▷ q))))))

module AxisSectionCoordinates {Γ : Context} {I B : CAT Γ} (a : MAP One I) where
  private
    module Section = TerminalProductSection B
    module Pair = ProductPairCoordinates a (id B) (terminate B) (id B)
    A = productMap a (id B)
    axis = pair (const {P = B} a) (id B)
    t = Section.t
    q = Section.q
    p1 = pair-β₁ (a ∘ pr₁) (id B ∘ q)
    p2 = pair-β₂ (a ∘ pr₁) (id B ∘ q)
    kappa = a ◁ terminal-identification (pr₁ {C = One} {D = B}) (terminate (One × B))
    bt1 = const-pre a t
    bt2 = product-unitˡ-pr₂-inverse B
    bq1 = const-pre a q
    bq2 = comp-unitˡ q
    ba1 = pair-β₁ (const {P = B} a) (id B)
    ba2 = pair-β₂ (const {P = B} a) (id B)
    close = pair⁼ (id₌ (const {P = B} a)) (comp-unitˡ (id B))
    prodPair = productMap-pair a (id B) (terminate B) (id B)
  first = kappa ∙ p1
  second = comp-unitˡ q ∙ p2
  eta = close ∙ prodPair
  private
    module Terminal = TerminalPostTriangle a (pr₁ {C = One} {D = B}) t
      (pair-β₁ (terminate B) (id B))
    pre1 = project-pair₁ (a ∘ pr₁) (id B ∘ q) t
    pre2 = project-pair₂ (a ∘ pr₁) (id B ∘ q) t
    as1 = (comp-assoc t A pr₁) ⁻¹
    as2 = (comp-assoc t A pr₂) ⁻¹
    source-first-normalization : compose-triangle pr₁ A first t bt1 =₂ Pair.source-first
    source-first-normalization = comp₌-cong Terminal.compatibility (id₌ pre1) ∙
      ((comp₌-assoc bt1 (kappa ▷ t) pre1) ⁻¹ ∙
        comp₌-cong (id₌ bt1)
          (comp₌-assoc (kappa ▷ t) (p1 ▷ t) as1 ∙
            comp₌-cong (preWhisker-comp₌ kappa p1 t) (id₌ as1)))
    source-second-normalization : compose-triangle pr₂ A second t bt2 =₂
      (comp-unitˡ (id B) ∙ Pair.source-last)
    source-second-normalization = comp₌-assoc (comp-unitˡ (id B))
      (post-triangle (id B) q t bt2) pre2 ∙
      (comp₌-cong ((post-triangle-id q t bt2) ⁻¹) (id₌ pre2) ∙
        ((comp₌-assoc bt2 (comp-unitˡ q ▷ t) pre2) ⁻¹ ∙
          comp₌-cong (id₌ bt2)
            (comp₌-assoc (comp-unitˡ q ▷ t) (p2 ▷ t) as2 ∙
              comp₌-cong (preWhisker-comp₌ (comp-unitˡ q) p2 t) (id₌ as2))))
    closing-first : (ba1 ∙ (pr₁ ◁ close)) =₂ Pair.target-first
    closing-first = comp₌-unitˡ-One Pair.target-first ∙
      pair⁼-triangle₁-One (id₌ (const {P = B} a)) (comp-unitˡ (id B))
    eta-first : (ba1 ∙ (pr₁ ◁ eta)) =₂ compose-triangle pr₁ A first t bt1
    eta-first = (source-first-normalization ⁻¹) ∙
      compatible-comp pr₁ Pair.source-first Pair.target-first ba1 close prodPair closing-first Pair.first-compatible
    scaled-second : ((comp-unitˡ (id B) ∙ Pair.target-last) ∙ (pr₂ ◁ prodPair)) =₂
      (comp-unitˡ (id B) ∙ Pair.source-last)
    scaled-second = comp₌-cong (id₌ (comp-unitˡ (id B))) Pair.last-compatible ∙
      comp₌-assoc (comp-unitˡ (id B)) Pair.target-last (pr₂ ◁ prodPair)
    eta-second : (ba2 ∙ (pr₂ ◁ eta)) =₂ compose-triangle pr₂ A second t bt2
    eta-second = (source-second-normalization ⁻¹) ∙
      compatible-comp pr₂ (comp-unitˡ (id B) ∙ Pair.source-last)
        (comp-unitˡ (id B) ∙ Pair.target-last) ba2 close prodPair
        (pair⁼-triangle₂-One (id₌ (const {P = B} a)) (comp-unitˡ (id B))) scaled-second
    module First = SectionDecodeOverBase pr₁ A axis t q Section.contraction
      (const {P = One × B} a) (const {P = B} a) first bt1 bq1 ba1 eta eta-first
      (ConstantSectionContraction.compatibility a t q Section.contraction)
    module Second = SectionDecodeOverBase pr₂ A axis t q Section.contraction
      q (id B) second bt2 bq2 ba2 eta eta-second Section.projection-compatibility
  decode = comp-unitʳ A ∙ ((A ◁ Section.contraction) ∙
    (comp-assoc q t A ∙ ((eta ⁻¹) ▷ q)))
  first-image : (first ∙ (pr₁ ◁ decode)) =₂
    compose-triangle pr₁ axis ba1 q bq1
  first-image = First.compatibility
  second-image : (second ∙ (pr₂ ◁ decode)) =₂
    compose-triangle pr₂ axis ba2 q bq2
  second-image = Second.compatibility

```
