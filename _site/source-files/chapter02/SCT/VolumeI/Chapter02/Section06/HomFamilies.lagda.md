# Framed families in Hom categories

The reader is the original `hom-family` used by the existing Hom
composition functor. Normalize the terminal leg of its actual endpoint
cone, retaining both matching coordinates. This supplies introduction,
the full beta and reconstruction laws, and reflection of comparisons.

Native product-coordinate triangles are used throughout. No identity
factorization is substituted for a chosen projection triangle.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section06.HomFamilies where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const; terminal-identification)
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-assoc; postWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair₌-extensionality; pair-pre-triangle₁; pair-pre-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (terminal-unique₂)
open import SCT.VolumeI.Chapter01.Section06.Cones using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-compose; cone-inverse; cone-action-One)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (pullback-factor; pullback-factor-β)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (pullback-reflect; pullback-factor-cong; pullback-factor-restrict)
open import SCT.VolumeI.Chapter01.Section06.ProductPullbacks using (module NativeCoordinate)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (family-comparison; restrict-family; retarget-family; restrict-family-comparison;
    retarget-family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices using (Hom; endpointMap; module EndpointFiber)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open MC public using (hom-family)

private
  module _ {Γ : Context} {P E C : CAT Γ} where
    encoded-coordinate : (pi : MAP E C) {u v w : MAP P E} {s t : MAP P C}
      (A : (pi ∘ u) =₁ s) (B : (pi ∘ v) =₁ t) (V : (pi ∘ w) =₁ t)
      (R : v =₁ w) (K : u =₁ w) (alpha : s =₁ t) →
      (V ∙ (pi ◁ R)) =₂ B → (V ∙ (pi ◁ K)) =₂ (alpha ∙ A) →
      (B ∙ ((pi ◁ (R ⁻¹ ∙ K)) ∙ A ⁻¹)) =₂ alpha
    encoded-coordinate pi A B V R K alpha projection-image paired-image =
      comp-inv-right alpha A ∙
        (comp₌-cong triangle (id₌ (A ⁻¹)) ∙ (comp₌-assoc B (pi ◁ delta) (A ⁻¹)) ⁻¹)
      where
      delta = R ⁻¹ ∙ K
      projected : ((pi ◁ R) ∙ (pi ◁ delta)) =₂ (pi ◁ K)
      projected = (postWhisker pi ◁ comp-inv-left R K) ∙ (postWhisker-comp₌ pi R delta) ⁻¹
      triangle : (B ∙ (pi ◁ delta)) =₂ (alpha ∙ A)
      triangle = paired-image ∙
        (comp₌-cong (id₌ V) projected ∙
          (comp₌-assoc V (pi ◁ R) (pi ◁ delta) ∙
            comp₌-cong (projection-image ⁻¹) (id₌ (pi ◁ delta))))

  module Coordinates {Γ : Context} {C : CAT Γ} (x y : MAP One C) where
    F : MAP (Ar C) (C × C)
    F = endpointMap C
    G : MAP One (C × C)
    G = pair x y
    module First = NativeCoordinate F G ev₀ x pr₁ (pair-β₁ ev₀ ev₁) (pair-β₁ x y)
      using (edge; edge-identification; edge-reflect; edge-restrict)
    module Second = NativeCoordinate F G ev₁ y pr₂ (pair-β₂ ev₀ ev₁) (pair-β₂ x y)
      using (edge; edge-identification; edge-reflect; edge-restrict)
    encode : {P : CAT Γ} (b : MAP P One) → MorphismFamily (x ∘ b) (y ∘ b) → Cone F G P
    encode b alpha = EndpointFiber.boundary-cone x y b alpha
    encode-first : {P : CAT Γ} (b : MAP P One) (alpha : MorphismFamily (x ∘ b) (y ∘ b)) →
      First.edge (encode b alpha) =₂ MorphismFamily.source-frame alpha
    encode-first b alpha = encoded-coordinate pr₁
      (project-pair₁ ev₀ ev₁ A.arrow) (project-pair₁ x y b) (pair-β₁ (x ∘ b) (y ∘ b))
      (pair-pre x y b) (pair⁼ A.source-frame A.target-frame ∙ pair-pre ev₀ ev₁ A.arrow) A.source-frame
      (pair-pre-triangle₁ x y b) (pair-evaluation-over₁-One ev₀ ev₁ A.arrow A.source-frame A.target-frame)
      where module A = MorphismFamily alpha
    encode-second : {P : CAT Γ} (b : MAP P One) (alpha : MorphismFamily (x ∘ b) (y ∘ b)) →
      Second.edge (encode b alpha) =₂ MorphismFamily.target-frame alpha
    encode-second b alpha = encoded-coordinate pr₂
      (project-pair₂ ev₀ ev₁ A.arrow) (project-pair₂ x y b) (pair-β₂ (x ∘ b) (y ∘ b))
      (pair-pre x y b) (pair⁼ A.source-frame A.target-frame ∙ pair-pre ev₀ ev₁ A.arrow) A.target-frame
      (pair-pre-triangle₂ x y b) (pair-evaluation-over₂-One ev₀ ev₁ A.arrow A.source-frame A.target-frame)
      where module A = MorphismFamily alpha
    cone-from-coordinates : {P : CAT Γ} (s t : Cone F G P)
      (L : Cone.left s =₁ Cone.left t) (R : Cone.right s =₁ Cone.right t) →
      (First.edge t ∙ (ev₀ ◁ L)) =₂ ((x ◁ R) ∙ First.edge s) →
      (Second.edge t ∙ (ev₁ ◁ L)) =₂ ((y ◁ R) ∙ Second.edge s) → ConeIdentification₁ s t
    cone-from-coordinates s t L R first second = record
      { left = L; right = R
      ; compatible = pair₌-extensionality
          (First.edge-reflect s t L R first) (Second.edge-reflect s t L R second) }

  module Decode {Γ : Context} {P C : CAT Γ} (x y : MAP One C) (b : MAP P One)
    (alpha beta : MorphismFamily (x ∘ b) (y ∘ b))
    (Phi : ConeIdentification₁ (EndpointFiber.boundary-cone x y b alpha) (EndpointFiber.boundary-cone x y b beta)) where
    private
      module A = MorphismFamily alpha
      module B = MorphismFamily beta
      module K = Coordinates x y
      delta = ConeIdentification₁.left Phi
      base-identity : ConeIdentification₁.right Phi =₂ id₌ b
      base-identity = terminal-unique₂ _ _
      source : (B.source-frame ∙ (ev₀ ◁ delta)) =₂ A.source-frame
      source = comp₌-unitˡ-One A.source-frame ∙
        (comp₌-cong (postWhisker-id₌ x b ∙ (postWhisker x ◁ base-identity)) (K.encode-first b alpha) ∙
          (K.First.edge-identification Phi ∙
            comp₌-cong ((K.encode-first b beta) ⁻¹) (id₌ (ev₀ ◁ delta))))
      target : (B.target-frame ∙ (ev₁ ◁ delta)) =₂ A.target-frame
      target = comp₌-unitˡ-One A.target-frame ∙
        (comp₌-cong (postWhisker-id₌ y b ∙ (postWhisker y ◁ base-identity)) (K.encode-second b alpha) ∙
          (K.Second.edge-identification Phi ∙
            comp₌-cong ((K.encode-second b beta) ⁻¹) (id₌ (ev₁ ◁ delta))))
    value : MorphismFamilyIdentification One alpha beta
    value = family-comparison alpha beta delta source target

  module Encode {Γ : Context} {P C : CAT Γ} (x y : MAP One C) (b : MAP P One)
    {alpha beta : MorphismFamily (x ∘ b) (y ∘ b)} (Phi : MorphismFamilyIdentification One alpha beta) where
    private
      module A = MorphismFamily alpha
      module B = MorphismFamily beta
      module Q = FamilyComparison Phi
      module K = Coordinates x y
      endpoint : (e : MAP (Ar C) C) (z : MAP One C)
        (a old : (e ∘ A.arrow) =₁ (z ∘ b)) (a′ new : (e ∘ B.arrow) =₁ (z ∘ b)) →
        old =₂ a → new =₂ a′ → (a′ ∙ (e ◁ Q.identification)) =₂ a →
        (new ∙ (e ◁ Q.identification)) =₂ ((z ◁ id₌ b) ∙ old)
      endpoint e z a old a′ new old-image new-image square =
        (comp₌-unitˡ-One old ∙ comp₌-cong (postWhisker-id₌ z b) (id₌ old)) ⁻¹ ∙
          (old-image ⁻¹ ∙ (square ∙ comp₌-cong new-image (id₌ (e ◁ Q.identification))))
    value : ConeIdentification₁ (EndpointFiber.boundary-cone x y b alpha) (EndpointFiber.boundary-cone x y b beta)
    value = K.cone-from-coordinates (K.encode b alpha) (K.encode b beta) Q.identification (id₌ b)
      (endpoint ev₀ x A.source-frame (K.First.edge (K.encode b alpha))
        B.source-frame (K.First.edge (K.encode b beta)) (K.encode-first b alpha) (K.encode-first b beta) Q.source)
      (endpoint ev₁ y A.target-frame (K.Second.edge (K.encode b alpha))
        B.target-frame (K.Second.edge (K.encode b beta)) (K.encode-second b alpha) (K.encode-second b beta) Q.target)
```

Normalize only the terminal base of the actual restricted Hom cone.
Its two decoded coordinates are exactly the two frames of the existing
reader. Pullback reflection gives reconstruction, and the complete
pullback beta gives the framed introduction law.

```agda
module Normalize {Γ : Context} {P C : CAT Γ} (x y : MAP One C) (h : MAP P (Hom C x y)) where
  private
    module K = Coordinates x y
    module H = EndpointFiber x y using (universal; arrow; base; boundary-cone)
    raw : Cone (endpointMap C) (pair x y) P
    raw = cone-restrict h H.universal
    family = hom-family x y h
    normalized : Cone (endpointMap C) (pair x y) P
    normalized = H.boundary-cone (terminate P) family
    tau : (H.base ∘ h) =₁ terminate P
    tau = terminal-identification (H.base ∘ h) (terminate P)
    source-equation : (K.First.edge normalized ∙ (ev₀ ◁ id₌ (H.arrow ∘ h))) =₂
      ((x ◁ tau) ∙ K.First.edge raw)
    source-equation = K.encode-first (terminate P) family ∙
      (comp₌-unitʳ-One (K.First.edge normalized) ∙
        comp₌-cong (id₌ (K.First.edge normalized)) (postWhisker-id₌ ev₀ (H.arrow ∘ h)))
    target-equation : (K.Second.edge normalized ∙ (ev₁ ◁ id₌ (H.arrow ∘ h))) =₂
      ((y ◁ tau) ∙ K.Second.edge raw)
    target-equation = K.encode-second (terminate P) family ∙
      (comp₌-unitʳ-One (K.Second.edge normalized) ∙
        comp₌-cong (id₌ (K.Second.edge normalized)) (postWhisker-id₌ ev₁ (H.arrow ∘ h)))
  comparison : ConeIdentification₁ raw normalized
  comparison = K.cone-from-coordinates raw normalized (id₌ (H.arrow ∘ h)) tau source-equation target-equation

module _ {Γ : Context} {P C : CAT Γ} (x y : MAP One C) where
  hom-intro : MorphismFamily (const {P = P} x) (const y) → MAP P (Hom C x y)
  hom-intro alpha = EndpointFiber.extension x y (terminate P) alpha
  hom-cong : {alpha beta : MorphismFamily (const {P = P} x) (const y)} →
    MorphismFamilyIdentification One alpha beta → hom-intro alpha =₁ hom-intro beta
  hom-cong Phi = pullback-factor-cong (Encode.value x y (terminate P) Phi)
  hom-eta : (h : MAP P (Hom C x y)) → hom-intro (hom-family x y h) =₁ h
  hom-eta h = pullback-reflect _ _
    (cone-compose (cone-inverse (Normalize.comparison x y h))
      (EndpointFiber.extension-image x y (terminate P) (hom-family x y h)))
  hom-beta : (alpha : MorphismFamily (const {P = P} x) (const y)) →
    MorphismFamilyIdentification One (hom-family x y (hom-intro alpha)) alpha
  hom-beta alpha = Decode.value x y (terminate P) (hom-family x y (hom-intro alpha)) alpha
    (cone-compose (EndpointFiber.extension-image x y (terminate P) alpha)
      (cone-inverse (Normalize.comparison x y (hom-intro alpha))))
  hom-family-cong : {h k : MAP P (Hom C x y)} → h =₁ k →
    MorphismFamilyIdentification One (hom-family x y h) (hom-family x y k)
  hom-family-cong {h} {k} delta = Decode.value x y (terminate P) (hom-family x y h) (hom-family x y k)
    (cone-compose (Normalize.comparison x y k)
      (cone-compose (cone-action-One (EndpointFiber.universal x y) delta)
        (cone-inverse (Normalize.comparison x y h))))
  hom-reflect : {h k : MAP P (Hom C x y)} →
    MorphismFamilyIdentification One (hom-family x y h) (hom-family x y k) → h =₁ k
  hom-reflect {h} {k} Phi = hom-eta k ∙ (hom-cong Phi ∙ (hom-eta h) ⁻¹)
  hom-intro-reflect : {alpha beta : MorphismFamily (const {P = P} x) (const y)} →
    hom-intro alpha =₁ hom-intro beta → MorphismFamilyIdentification One alpha beta
  hom-intro-reflect {alpha} {beta} delta = compose-family-comparisons (hom-beta beta)
    (compose-family-comparisons (hom-family-cong delta) (inverse-family-comparison (hom-beta alpha)))
```

Restriction retains both endpoint frames. The comparison of the two
boundary cones uses the specified terminal identification and the native
coordinate restriction law. Introduction and reconstruction then give
the restriction law for the original Hom reader.

```agda
module _ {Γ : Context} {P Q C : CAT Γ} {x y : MAP One C} where
  hom-restrict : MorphismFamily (const {P = P} x) (const y) → (r : MAP Q P) →
    MorphismFamily (const x) (const y)
  hom-restrict alpha r = retarget-family (restrict-family alpha r) (const-pre x r) (const-pre y r)
  hom-restrict-cong : {alpha beta : MorphismFamily (const {P = P} x) (const y)} →
    MorphismFamilyIdentification One alpha beta → (r : MAP Q P) →
    MorphismFamilyIdentification One (hom-restrict alpha r) (hom-restrict beta r)
  hom-restrict-cong Phi r = retarget-family-comparison (const-pre x r) (const-pre y r)
    (restrict-family-comparison r Phi)

private
  module RestrictedCone {Γ : Context} {P Q C : CAT Γ} {x y : MAP One C}
    (alpha : MorphismFamily (const {P = P} x) (const y)) (r : MAP Q P) where
    module A = MorphismFamily alpha using (arrow; source-frame; target-frame)
    module K = Coordinates x y
    before : Cone (endpointMap C) (pair x y) P
    before = K.encode (terminate P) alpha
    restricted : Cone (endpointMap C) (pair x y) Q
    restricted = cone-restrict r before
    after : Cone (endpointMap C) (pair x y) Q
    after = K.encode (terminate Q) (hom-restrict alpha r)
    tau : (terminate P ∘ r) =₁ terminate Q
    tau = terminal-identification (terminate P ∘ r) (terminate Q)
    coordinate : (pi : MAP (Ar C) C) (z : MAP One C)
      (p : (pi ∘ A.arrow) =₁ const z)
      (old : (pi ∘ (A.arrow ∘ r)) =₁ (z ∘ (terminate P ∘ r)))
      (new : (pi ∘ (A.arrow ∘ r)) =₁ const z) →
      old =₂ (comp-assoc r (terminate P) z ∙ ((p ▷ r) ∙ (comp-assoc r A.arrow pi) ⁻¹)) →
      new =₂ (const-pre z r ∙ ((p ▷ r) ∙ (comp-assoc r A.arrow pi) ⁻¹)) →
      (new ∙ (pi ◁ id₌ (A.arrow ∘ r))) =₂ ((z ◁ tau) ∙ old)
    coordinate pi z p old new old-value new-value =
      (comp₌-cong (id₌ (z ◁ tau)) old-value) ⁻¹ ∙
        (comp₌-assoc (z ◁ tau) (comp-assoc r (terminate P) z)
          ((p ▷ r) ∙ (comp-assoc r A.arrow pi) ⁻¹) ∙
          (new-value ∙ (comp₌-unitʳ-One new ∙
            comp₌-cong (id₌ new) (postWhisker-id₌ pi (A.arrow ∘ r)))))
    comparison : ConeIdentification₁ restricted after
    comparison = K.cone-from-coordinates restricted after (id₌ (A.arrow ∘ r)) tau
      (coordinate ev₀ x A.source-frame _ _
        (comp₌-cong (id₌ (comp-assoc r (terminate P) x))
          (comp₌-cong (preWhisker r ◁ K.encode-first (terminate P) alpha)
            (id₌ ((comp-assoc r A.arrow ev₀) ⁻¹))) ∙ K.First.edge-restrict r before)
        (K.encode-first (terminate Q) (hom-restrict alpha r)))
      (coordinate ev₁ y A.target-frame _ _
        (comp₌-cong (id₌ (comp-assoc r (terminate P) y))
          (comp₌-cong (preWhisker r ◁ K.encode-second (terminate P) alpha)
            (id₌ ((comp-assoc r A.arrow ev₁) ⁻¹))) ∙ K.Second.edge-restrict r before)
        (K.encode-second (terminate Q) (hom-restrict alpha r)))

module _ {Γ : Context} {P Q C : CAT Γ} {x y : MAP One C} where
  hom-intro-restrict : (alpha : MorphismFamily (const {P = P} x) (const y)) (r : MAP Q P) →
    (hom-intro x y alpha ∘ r) =₁ hom-intro x y (hom-restrict alpha r)
  hom-intro-restrict alpha r = pullback-factor-cong (RestrictedCone.comparison alpha r) ∙
    (pullback-factor-restrict r (RestrictedCone.before alpha r)) ⁻¹
  hom-family-restrict : (h : MAP P (Hom C x y)) (r : MAP Q P) →
    MorphismFamilyIdentification One (hom-family x y (h ∘ r)) (hom-restrict (hom-family x y h) r)
  hom-family-restrict h r = compose-family-comparisons (hom-beta x y (hom-restrict (hom-family x y h) r))
    (hom-family-cong x y (hom-intro-restrict (hom-family x y h) r ∙ ((hom-eta x y h ▷ r) ⁻¹)))

module _ {Γ : Context} {P C : CAT Γ} (x y : MAP One C) where
  hom-universal-restrict : (r : MAP P (Hom C x y)) →
    MorphismFamilyIdentification One (hom-restrict (hom-family x y (id (Hom C x y))) r) (hom-family x y r)
  hom-universal-restrict r = compose-family-comparisons (hom-family-cong x y (comp-unitˡ r))
    (inverse-family-comparison (hom-family-restrict (id (Hom C x y)) r))
```

A family operation realizes to a functor between Hom categories when
it preserves full comparisons and has a specified restriction law.
The computation is a full family comparison, including both frames.

```agda
module Realize {Γ : Context} {C D : CAT Γ} (x y : MAP One C) (u v : MAP One D)
  (act : {P : CAT Γ} → MorphismFamily (const {P = P} x) (const y) →
    MorphismFamily (const u) (const v))
  (compare : {P : CAT Γ} {alpha beta : MorphismFamily (const {P = P} x) (const y)} →
    MorphismFamilyIdentification One alpha beta → MorphismFamilyIdentification One (act alpha) (act beta))
  (restriction : {P Q : CAT Γ} (alpha : MorphismFamily (const {P = P} x) (const y)) (r : MAP Q P) →
    MorphismFamilyIdentification One (hom-restrict (act alpha) r) (act (hom-restrict alpha r))) where
  private
    universal : MorphismFamily (const {P = Hom C x y} x) (const y)
    universal = hom-family x y (id (Hom C x y))
  value : MAP (Hom C x y) (Hom D u v)
  value = hom-intro u v (act universal)
  computation : {P : CAT Γ} (r : MAP P (Hom C x y)) →
    MorphismFamilyIdentification One (hom-family u v (value ∘ r)) (act (hom-family x y r))
  computation r = compose-family-comparisons (compare (hom-universal-restrict x y r))
    (compose-family-comparisons (restriction universal r)
      (compose-family-comparisons (hom-restrict-cong (hom-beta u v (act universal)) r)
        (hom-family-restrict value r)))
```
