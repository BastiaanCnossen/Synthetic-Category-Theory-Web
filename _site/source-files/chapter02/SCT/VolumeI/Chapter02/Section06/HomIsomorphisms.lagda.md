# Hom composition and detection of isomorphisms

The unary composition functors are restrictions of the specified binary
Hom composition. Their computations retain the original Hom-family
reader and its two endpoint frames. The fixed input is a chosen Hom point.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section06.HomIsomorphisms where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions using (const)
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-assoc; comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization using (const-pre; const-One)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (restrict-triangle)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-reflect; section-retraction-isEquiv)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Morphism; DiagramFamily; MorphismFamily; MorphismFamilyIdentification; identity-family; insert; encode)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (restrict-family; retarget-family; retarget-family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; inverse-family-comparison; id-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices using (Hom)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyRestriction using (module IdentityFamilyRestriction)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyTransport using (module IdentityFamilyChange)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport using (module CompositionTransport)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits using (module MorphismCompositionUnits)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionAssociativity using (associativity)
open import SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies using (InverseFamily)
open import SCT.VolumeI.Chapter02.Section03.InvertibleMorphismFamilies
  using (IsoLift; inverse-family-lift; lift-inverse-family)
open import SCT.VolumeI.Chapter02.Section06.HomFamilies
  using (hom-family; hom-intro; hom-beta; hom-family-cong; hom-restrict; hom-restrict-cong; hom-family-restrict;
    hom-reflect; hom-intro-reflect)

module CompositionOnHom {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
  private
    module Chosen = MC.Composition C segal using (compose)
    module Compare = CompositionComparisons C segal using (composition-comparison)
    module Transport = CompositionTransport C segal using (restrict-composition; retarget-composition)

  composition-restrict : {P Q : CAT Γ} {x y z : MAP One C}
    (beta : MorphismFamily (const {P = P} y) (const z))
    (alpha : MorphismFamily (const {P = P} x) (const y)) (r : MAP Q P) →
    MorphismFamilyIdentification One (hom-restrict (Chosen.compose beta alpha) r)
      (Chosen.compose (hom-restrict beta r) (hom-restrict alpha r))
  composition-restrict {x = x} {y} {z} beta alpha r =
    compose-family-comparisons
      (Transport.retarget-composition (restrict-family beta r) (restrict-family alpha r)
        (const-pre x r) (const-pre y r) (const-pre z r))
      (retarget-family-comparison (const-pre x r) (const-pre z r)
        (Transport.restrict-composition beta alpha r))

  module Binary (x y z : MAP One C) where
    private
      module H = MC.HomComposition C segal x y z using (value; composite; first; second)
    value : MAP (Hom C y z × Hom C x y) (Hom C x z)
    value = H.value
    computation : {P : CAT Γ} (r : MAP P (Hom C y z × Hom C x y)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ r))
        (Chosen.compose (hom-family y z (pr₁ ∘ r)) (hom-family x y (pr₂ ∘ r)))
    computation r = compose-family-comparisons
      (Compare.composition-comparison
        (inverse-family-comparison (hom-family-restrict pr₁ r))
        (inverse-family-comparison (hom-family-restrict pr₂ r)))
      (compose-family-comparisons (composition-restrict H.second H.first r)
        (compose-family-comparisons (hom-restrict-cong (hom-beta x z H.composite) r)
          (hom-family-restrict value r)))

  module Post (x y z : MAP One C) (f : MAP One (Hom C y z)) where
    private
      module B = Binary x y z using (value; computation)
      selected : MAP (Hom C x y) (Hom C y z × Hom C x y)
      selected = pair (const f) (id (Hom C x y))
    value : MAP (Hom C x y) (Hom C x z)
    value = B.value ∘ selected
    computation : {P : CAT Γ} (h : MAP P (Hom C x y)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ h))
        (Chosen.compose (hom-family y z (const f)) (hom-family x y h))
    computation h = compose-family-comparisons
      (Compare.composition-comparison
        (hom-family-cong y z (const-pre f h ∙
          restrict-triangle pr₁ selected (pair-β₁ (const f) (id (Hom C x y))) h))
        (hom-family-cong x y (comp-unitˡ h ∙
          restrict-triangle pr₂ selected (pair-β₂ (const f) (id (Hom C x y))) h)))
      (compose-family-comparisons (B.computation (selected ∘ h))
        (hom-family-cong x z (comp-assoc h selected B.value)))
    at-family : (alpha : MorphismFamily (const {P = One} x) (const y)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ hom-intro x y alpha))
        (Chosen.compose (hom-family y z f) alpha)
    at-family alpha = compose-family-comparisons
      (Compare.composition-comparison (hom-family-cong y z (const-One f)) (hom-beta x y alpha))
      (computation (hom-intro x y alpha))
    at-point : (h : MAP One (Hom C x y)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ h))
        (Chosen.compose (hom-family y z f) (hom-family x y h))
    at-point h = compose-family-comparisons
      (Compare.composition-comparison (hom-family-cong y z (const-One f))
        (id-family-comparison (hom-family x y h))) (computation h)
    universal-computation : MorphismFamilyIdentification One (hom-family x z value)
      (Chosen.compose (hom-family y z (const f)) (hom-family x y (id (Hom C x y))))
    universal-computation = compose-family-comparisons (computation (id (Hom C x y)))
      (hom-family-cong x z ((comp-unitʳ value) ⁻¹))

  module Pre (x y z : MAP One C) (f : MAP One (Hom C x y)) where
    private
      module B = Binary x y z using (value; computation)
      selected : MAP (Hom C y z) (Hom C y z × Hom C x y)
      selected = pair (id (Hom C y z)) (const f)
    value : MAP (Hom C y z) (Hom C x z)
    value = B.value ∘ selected
    computation : {P : CAT Γ} (h : MAP P (Hom C y z)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ h))
        (Chosen.compose (hom-family y z h) (hom-family x y (const f)))
    computation h = compose-family-comparisons
      (Compare.composition-comparison
        (hom-family-cong y z (comp-unitˡ h ∙
          restrict-triangle pr₁ selected (pair-β₁ (id (Hom C y z)) (const f)) h))
        (hom-family-cong x y (const-pre f h ∙
          restrict-triangle pr₂ selected (pair-β₂ (id (Hom C y z)) (const f)) h)))
      (compose-family-comparisons (B.computation (selected ∘ h))
        (hom-family-cong x z (comp-assoc h selected B.value)))
    at-family : (alpha : MorphismFamily (const {P = One} y) (const z)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ hom-intro y z alpha))
        (Chosen.compose alpha (hom-family x y f))
    at-family alpha = compose-family-comparisons
      (Compare.composition-comparison (hom-beta y z alpha) (hom-family-cong x y (const-One f)))
      (computation (hom-intro y z alpha))
    at-point : (h : MAP One (Hom C y z)) →
      MorphismFamilyIdentification One (hom-family x z (value ∘ h))
        (Chosen.compose (hom-family y z h) (hom-family x y f))
    at-point h = compose-family-comparisons
      (Compare.composition-comparison (id-family-comparison (hom-family y z h))
        (hom-family-cong x y (const-One f))) (computation h)
    universal-computation : MorphismFamilyIdentification One (hom-family x z value)
      (Chosen.compose (hom-family y z (id (Hom C y z))) (hom-family x y (const f)))
    universal-computation = compose-family-comparisons (computation (id (Hom C y z)))
      (hom-family-cong x z ((comp-unitʳ value) ⁻¹))
```

For either converse only the two Hom tests at the endpoints are needed.
Postcomposition first lifts the target identity to a right inverse.
Reflection through the source test gives the left inverse law.
Precomposition starts with the source identity and argues dually.
Both proofs use the already specified composition and its associativity.

```agda
module Detection {Γ : Context} (C : CAT Γ) (x y : MAP One C) (f : MAP One (Hom C x y)) where
  private
    segal : IsEquiv (short-edges C)
    segal = segal-isEquiv C
    module H = CompositionOnHom C segal
    module Chosen = MC.Composition C segal using (compose)
    module Compare = CompositionComparisons C segal using (composition-comparison)
    module Unit = MorphismCompositionUnits C segal using (source-unit; target-unit)
    family : MorphismFamily (const {P = One} x) (const y)
    family = hom-family x y f
    source-identity : MorphismFamily (const {P = One} x) (const x)
    source-identity = identity-family (const x)
    target-identity : MorphismFamily (const {P = One} y) (const y)
    target-identity = identity-family (const y)

  module Post (at-source : IsEquiv (H.Post.value x x y f))
    (at-target : IsEquiv (H.Post.value y x y f)) where
    private
      module Source = H.Post x x y f using (value; at-family)
      module Target = H.Post y x y f using (value; at-point)
      target-point : MAP One (Hom C y y)
      target-point = hom-intro y y target-identity
      lifted : Fact.Factorization Target.value target-point
      lifted = Fact.factor-through-equiv at-target target-point
      inverse-point : MAP One (Hom C y x)
      inverse-point = Fact.factor lifted
      inverse : MorphismFamily (const {P = One} y) (const x)
      inverse = hom-family y x inverse-point
      right-law : MorphismFamilyIdentification One (Chosen.compose family inverse) target-identity
      right-law = compose-family-comparisons (hom-beta y y target-identity)
        (compose-family-comparisons (hom-family-cong y y (Fact.triangle lifted))
          (inverse-family-comparison (Target.at-point inverse-point)))
      candidate : MorphismFamily (const {P = One} x) (const x)
      candidate = Chosen.compose inverse family
      candidate-image : MorphismFamilyIdentification One
        (hom-family x y (Source.value ∘ hom-intro x x candidate)) family
      candidate-image = compose-family-comparisons (Unit.target-unit family)
        (compose-family-comparisons
          (Compare.composition-comparison right-law (id-family-comparison family))
          (compose-family-comparisons (associativity family inverse family) (Source.at-family candidate)))
      identity-image : MorphismFamilyIdentification One
        (hom-family x y (Source.value ∘ hom-intro x x source-identity)) family
      identity-image = compose-family-comparisons (Unit.source-unit family) (Source.at-family source-identity)
      left-law : MorphismFamilyIdentification One candidate source-identity
      left-law = hom-intro-reflect x x
        (equiv-reflect at-source (hom-intro x x candidate) (hom-intro x x source-identity)
          (hom-reflect x y (compose-family-comparisons (inverse-family-comparison identity-image) candidate-image)))
    inverse-family : InverseFamily segal family
    inverse-family = record
      { left-inverse = inverse; right-inverse = inverse; left-law = left-law; right-law = right-law }
    lift : IsoLift (MorphismFamily.arrow family)
    lift = inverse-family-lift segal family inverse-family

  module Pre (at-source : IsEquiv (H.Pre.value x y x f))
    (at-target : IsEquiv (H.Pre.value x y y f)) where
    private
      module Source = H.Pre x y x f using (value; at-point)
      module Target = H.Pre x y y f using (value; at-family)
      source-point : MAP One (Hom C x x)
      source-point = hom-intro x x source-identity
      lifted : Fact.Factorization Source.value source-point
      lifted = Fact.factor-through-equiv at-source source-point
      inverse-point : MAP One (Hom C y x)
      inverse-point = Fact.factor lifted
      inverse : MorphismFamily (const {P = One} y) (const x)
      inverse = hom-family y x inverse-point
      left-law : MorphismFamilyIdentification One (Chosen.compose inverse family) source-identity
      left-law = compose-family-comparisons (hom-beta x x source-identity)
        (compose-family-comparisons (hom-family-cong x x (Fact.triangle lifted))
          (inverse-family-comparison (Source.at-point inverse-point)))
      candidate : MorphismFamily (const {P = One} y) (const y)
      candidate = Chosen.compose family inverse
      candidate-image : MorphismFamilyIdentification One
        (hom-family x y (Target.value ∘ hom-intro y y candidate)) family
      candidate-image = compose-family-comparisons (Unit.source-unit family)
        (compose-family-comparisons
          (Compare.composition-comparison (id-family-comparison family) left-law)
          (compose-family-comparisons (inverse-family-comparison (associativity family inverse family))
            (Target.at-family candidate)))
      identity-image : MorphismFamilyIdentification One
        (hom-family x y (Target.value ∘ hom-intro y y target-identity)) family
      identity-image = compose-family-comparisons (Unit.target-unit family) (Target.at-family target-identity)
      right-law : MorphismFamilyIdentification One candidate target-identity
      right-law = hom-intro-reflect y y
        (equiv-reflect at-target (hom-intro y y candidate) (hom-intro y y target-identity)
          (hom-reflect x y (compose-family-comparisons (inverse-family-comparison identity-image) candidate-image)))
    inverse-family : InverseFamily segal family
    inverse-family = record
      { left-inverse = inverse; right-inverse = inverse; left-law = left-law; right-law = right-law }
    lift : IsoLift (MorphismFamily.arrow family)
    lift = inverse-family-lift segal family inverse-family
```

For the forward implication, restrict a full inverse equation from the
terminal parameter to an arbitrary categorical parameter. Its original
frames are normalized using the specified constant restriction paths.
Associativity then cancels the two unary Hom actions. A left and a right
inverse may be different; they supply a retraction and a section.

```agda
private
  module HomCancellation {Γ : Context} (C : CAT Γ) where
    segal : IsEquiv (short-edges C)
    segal = segal-isEquiv C
    module H = CompositionOnHom C segal
    module Chosen = MC.Composition C segal using (compose)
    module Compare = CompositionComparisons C segal using (composition-comparison)
    module Unit = MorphismCompositionUnits C segal using (source-unit; target-unit)

    identity-restrict : {P : CAT Γ} (s : MAP One C) →
      MorphismFamilyIdentification One (hom-restrict (identity-family (const {P = One} s)) (terminate P))
        (identity-family (const {P = P} s))
    identity-restrict {P} s = compose-family-comparisons (IdentityFamilyChange.value (const-pre s (terminate P)))
      (retarget-family-comparison (const-pre s (terminate P)) (const-pre s (terminate P))
        (IdentityFamilyRestriction.value (const {P = One} s) (terminate P)))

    constant-law : {P : CAT Γ} {s t : MAP One C}
      (a : MAP One (Hom C t s)) (b : MAP One (Hom C s t)) →
      MorphismFamilyIdentification One (Chosen.compose (hom-family t s a) (hom-family s t b))
        (identity-family (const {P = One} s)) →
      MorphismFamilyIdentification One
        (Chosen.compose (hom-family t s (const {P = P} a)) (hom-family s t (const {P = P} b)))
        (identity-family (const {P = P} s))
    constant-law {P} {s} a b law = compose-family-comparisons (identity-restrict s)
      (compose-family-comparisons (hom-restrict-cong law (terminate P))
        (compose-family-comparisons
          (inverse-family-comparison (H.composition-restrict (hom-family _ _ a) (hom-family _ _ b) (terminate P)))
          (Compare.composition-comparison (hom-family-restrict a (terminate P)) (hom-family-restrict b (terminate P)))))

    post-cancel : {s t : MAP One C} (a : MAP One (Hom C t s)) (b : MAP One (Hom C s t))
      (z : MAP One C) →
      MorphismFamilyIdentification One (Chosen.compose (hom-family t s a) (hom-family s t b))
        (identity-family (const {P = One} s)) →
      (H.Post.value z t s a ∘ H.Post.value z s t b) =₁ id (Hom C z s)
    post-cancel {s} {t} a b z law = hom-reflect z s
      (compose-family-comparisons (Unit.target-unit alpha)
        (compose-family-comparisons
          (Compare.composition-comparison (constant-law a b law) (id-family-comparison alpha))
          (compose-family-comparisons (associativity alpha fixed-b fixed-a)
            (compose-family-comparisons
              (Compare.composition-comparison (id-family-comparison fixed-a) B.universal-computation)
              (A.computation B.value)))))
      where
      module A = H.Post z t s a using (value; computation)
      module B = H.Post z s t b using (value; universal-computation)
      alpha = hom-family z s (id (Hom C z s))
      fixed-a = hom-family t s (const {P = Hom C z s} a)
      fixed-b = hom-family s t (const {P = Hom C z s} b)

    pre-cancel : {s t : MAP One C} (a : MAP One (Hom C t s)) (b : MAP One (Hom C s t))
      (z : MAP One C) →
      MorphismFamilyIdentification One (Chosen.compose (hom-family t s a) (hom-family s t b))
        (identity-family (const {P = One} s)) →
      (H.Pre.value s t z b ∘ H.Pre.value t s z a) =₁ id (Hom C s z)
    pre-cancel {s} {t} a b z law = hom-reflect s z
      (compose-family-comparisons (Unit.source-unit alpha)
        (compose-family-comparisons
          (Compare.composition-comparison (id-family-comparison alpha) (constant-law a b law))
          (compose-family-comparisons (inverse-family-comparison (associativity fixed-b fixed-a alpha))
            (compose-family-comparisons
              (Compare.composition-comparison A.universal-computation (id-family-comparison fixed-b))
              (B.computation A.value)))))
      where
      module A = H.Pre t s z a using (value; universal-computation)
      module B = H.Pre s t z b using (value; computation)
      alpha = hom-family s z (id (Hom C s z))
      fixed-a = hom-family t s (const {P = Hom C s z} a)
      fixed-b = hom-family s t (const {P = Hom C s z} b)

module InvertibleHom {Γ : Context} (C : CAT Γ) (x y : MAP One C)
  (f : MAP One (Hom C x y)) (given : IsoLift (MorphismFamily.arrow (hom-family x y f))) where
  private
    segal : IsEquiv (short-edges C)
    segal = segal-isEquiv C
    module H = CompositionOnHom C segal
    module Chosen = MC.Composition C segal using (compose)
    module Compare = CompositionComparisons C segal using (composition-comparison)
    module Cancel = HomCancellation C using (post-cancel; pre-cancel)
    witness : InverseFamily segal (hom-family x y f)
    witness = lift-inverse-family segal (hom-family x y f) given
    module W = InverseFamily witness using (left-inverse; right-inverse; left-law; right-law)
    left-point right-point : MAP One (Hom C y x)
    left-point = hom-intro y x W.left-inverse
    right-point = hom-intro y x W.right-inverse
    left-law : MorphismFamilyIdentification One
      (Chosen.compose (hom-family y x left-point) (hom-family x y f)) (identity-family (const {P = One} x))
    left-law = compose-family-comparisons W.left-law
      (Compare.composition-comparison (hom-beta y x W.left-inverse) (id-family-comparison (hom-family x y f)))
    right-law : MorphismFamilyIdentification One
      (Chosen.compose (hom-family x y f) (hom-family y x right-point)) (identity-family (const {P = One} y))
    right-law = compose-family-comparisons W.right-law
      (Compare.composition-comparison (id-family-comparison (hom-family x y f)) (hom-beta y x W.right-inverse))
  postcomposition-isEquiv : (z : MAP One C) → IsEquiv (H.Post.value z x y f)
  postcomposition-isEquiv z = section-retraction-isEquiv
    (record { section = H.Post.value z y x right-point; section-law = (Cancel.post-cancel f right-point z right-law) ⁻¹ })
    (record { retraction = H.Post.value z y x left-point; retraction-law = (Cancel.post-cancel left-point f z left-law) ⁻¹ })
  precomposition-isEquiv : (z : MAP One C) → IsEquiv (H.Pre.value x y z f)
  precomposition-isEquiv z = section-retraction-isEquiv
    (record { section = H.Pre.value y x z left-point; section-law = (Cancel.pre-cancel left-point f z left-law) ⁻¹ })
    (record { retraction = H.Pre.value y x z right-point; retraction-law = (Cancel.pre-cancel f right-point z right-law) ⁻¹ })

module _ {Γ : Context} (C : CAT Γ) (x y : MAP One C) (f : MAP One (Hom C x y)) where
  postcomposition-detects-isomorphism :
    ((z : MAP One C) → IsEquiv (CompositionOnHom.Post.value C (segal-isEquiv C) z x y f)) →
    IsoLift (MorphismFamily.arrow (hom-family x y f))
  postcomposition-detects-isomorphism tests = Detection.Post.lift C x y f (tests x) (tests y)
  precomposition-detects-isomorphism :
    ((z : MAP One C) → IsEquiv (CompositionOnHom.Pre.value C (segal-isEquiv C) x y z f)) →
    IsoLift (MorphismFamily.arrow (hom-family x y f))
  precomposition-detects-isomorphism tests = Detection.Pre.lift C x y f (tests x) (tests y)
```

For an ordinary morphism, use its literal interval diagram, constant
in the terminal parameter. Restrict both original endpoint frames along
that terminal map before encoding the diagram family. This specifies
the Hom point and the arrow whose lift to Iso expresses invertibility.
The full Hom beta comparison transports lifts in both directions.

```agda
module Criterion {Γ : Context} {C : CAT Γ} {x y : MAP One C} (f : Morphism x y) where
  private
    module F = Morphism f using (diagram; source-frame; target-frame)
    frame : (a : MAP One ([1] {Γ = Γ})) (z : MAP One C)
      (given : (F.diagram ∘ a) =₁ z) →
      ((F.diagram ∘ pr₂) ∘ insert {P = One} a) =₁ const {P = One} z
    frame a z given = (given ▷ terminate One) ∙
      ((comp-assoc (terminate One) a F.diagram) ⁻¹ ∙
        ((F.diagram ◁ pair-β₂ (id One) (const a)) ∙ comp-assoc (insert {P = One} a) pr₂ F.diagram))

  diagram-family : DiagramFamily (const {P = One} x) (const y)
  diagram-family = record
    { diagram = F.diagram ∘ pr₂
    ; source-frame = frame zero x F.source-frame
    ; target-frame = frame one y F.target-frame }
  family : MorphismFamily (const {P = One} x) (const y)
  family = encode diagram-family
  point : MAP One (Hom C x y)
  point = hom-intro x y family
  point-comparison : MorphismFamilyIdentification One (hom-family x y point) family
  point-comparison = hom-beta x y family

  IsIsomorphism : Set m
  IsIsomorphism = IsoLift (MorphismFamily.arrow family)

  postcompose : (z : MAP One C) → MAP (Hom C z x) (Hom C z y)
  postcompose z = CompositionOnHom.Post.value C (segal-isEquiv C) z x y point
  precompose : (z : MAP One C) → MAP (Hom C y z) (Hom C x z)
  precompose z = CompositionOnHom.Pre.value C (segal-isEquiv C) x y z point
  PostcompositionEquivalences PrecompositionEquivalences : Set m
  PostcompositionEquivalences = (z : MAP One C) → IsEquiv (postcompose z)
  PrecompositionEquivalences = (z : MAP One C) → IsEquiv (precompose z)

  private
    point-lift : IsIsomorphism → IsoLift (MorphismFamily.arrow (hom-family x y point))
    point-lift = Fact.factorization-retarget ((FamilyComparison.identification point-comparison) ⁻¹)
    read-lift : IsoLift (MorphismFamily.arrow (hom-family x y point)) → IsIsomorphism
    read-lift = Fact.factorization-retarget (FamilyComparison.identification point-comparison)

  isomorphism-postcompose : IsIsomorphism → PostcompositionEquivalences
  isomorphism-postcompose given = InvertibleHom.postcomposition-isEquiv C x y point (point-lift given)
  isomorphism-precompose : IsIsomorphism → PrecompositionEquivalences
  isomorphism-precompose given = InvertibleHom.precomposition-isEquiv C x y point (point-lift given)
  postcompose-detects-isomorphism : IsEquiv (postcompose x) → IsEquiv (postcompose y) → IsIsomorphism
  postcompose-detects-isomorphism at-source at-target =
    read-lift (Detection.Post.lift C x y point at-source at-target)
  precompose-detects-isomorphism : IsEquiv (precompose x) → IsEquiv (precompose y) → IsIsomorphism
  precompose-detects-isomorphism at-source at-target =
    read-lift (Detection.Pre.lift C x y point at-source at-target)
  postcompose-isomorphism : PostcompositionEquivalences → IsIsomorphism
  postcompose-isomorphism tests = postcompose-detects-isomorphism (tests x) (tests y)
  precompose-isomorphism : PrecompositionEquivalences → IsIsomorphism
  precompose-isomorphism tests = precompose-detects-isomorphism (tests x) (tests y)
```
