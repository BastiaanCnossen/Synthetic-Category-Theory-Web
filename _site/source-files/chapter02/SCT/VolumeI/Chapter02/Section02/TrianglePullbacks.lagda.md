# Triangles as squares with a constant side

The two square-retraction pullbacks combine with the Segal pullback to
identify triangles with squares whose lower or upper side is constant.
For each side, a second cancellation gives the constant-edge pullback;
pasting with the corresponding square-retraction pullback gives the result.
The proof retains the actual native square and Segal cone matchings.

The constant-precomposition calculation below directly adapts the finite
constant-insertion/evaluation argument in the historical DirectUnitTriangles.
It uses the literal identityArrow and its existing beta. It does not assume
agreement with a separately chosen unit comparison. The final vertex cone
is obtained by changing the legs along the chosen named-vertex equation,
with the complete cone identification recording that matching transport.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.TrianglePullbacks where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-transport)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
  using (cone-swap; cone-swap-twice; cone-change-left; cone-change-legs; cone-change-legs-β)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
  using (isPullback-cone-identification; isPullback-change-left; module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (isPullback-from-left-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma using (module Pasting)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Functoriality
  using (funPre; funPre-β; funPre-comp; funPre⁼; funPre-id)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; reflect)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; s₀; s₁; d₀; d₁; d₂; s₀-d₀; s₀-d₂; s₁-d₀; s₁-d₂;
    vertex₀; vertex₂; d₁-zero; d₁-one)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; evAt-pre; evAt-cong; insert;
    identityArrow; constantArrow-image; identity-source; identity-target)
open import SCT.VolumeI.Chapter02.Section01.Triangles
  using (Triangles; edge₀; edge₁; edge₂; triangle-cone)
open import SCT.VolumeI.Chapter02.Section01.SquareGluing
  using (Squares; j₀; j₁; j₀-d₀; j₁-d₂; p₀; p₂; module RetractionPullbacks)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)

private
  module _ {Γ : Context} where
    horizontal-equivalences : {A B Z T : CAT Γ} {f : MAP A Z} {g : MAP B Z}
      (s : Cone f g T) → IsEquiv f → IsEquiv (Cone.right s) → IsPullback s
    horizontal-equivalences s ef eq = isPullback-cone-identification (cone-swap-twice s)
      (SwappedCone.isPullback (cone-swap s)
        (isPullback-from-left-isEquiv ef (cone-swap s) eq))

  module ConstantRestriction {Γ : Context} (C : CAT Γ) where
    private
      X = Ar C
      e = funEval {C = [1]} {D = C}

    insertion : (x : MAP One ([1] {Γ = Γ}))
      → productMap (id X) (const {P = [1]} x) =₁ (insert x ∘ pr₁)
    insertion x = (pair-pre (id X) (const {P = X} x) pr₁) ⁻¹ ∙
      pair⁼ (id₌ (id X ∘ pr₁))
        ((comp-assoc pr₁ (terminate X) x) ⁻¹ ∙
          ((x ◁ terminal-identification (terminate [1] ∘ pr₂) (terminate X ∘ pr₁)) ∙
            comp-assoc pr₂ (terminate [1]) x))

    constant-evaluation : (x : MAP One ([1] {Γ = Γ}))
      → (e ∘ productMap (id X) (const {P = [1]} x)) =₁ (evAt x ∘ pr₁)
    constant-evaluation x = (comp-assoc pr₁ (insert x) e) ⁻¹ ∙ (e ◁ insertion x)

    identity-evaluation : (x : MAP One ([1] {Γ = Γ}))
      → funUncurry (identityArrow ∘ evAt {C = C} x) =₁ (evAt x ∘ pr₁)
    identity-evaluation x = pair-β₁ (evAt x ∘ pr₁) (id [1] ∘ pr₂) ∙
      ((constantArrow-image [1] C ▷ productMap (evAt x) (id [1])) ∙
        evaluate-restrict e identityArrow (evAt x))

    comparison : (x : MAP One ([1] {Γ = Γ}))
      → funPre {D = C} (const {P = [1]} x) =₁ (identityArrow ∘ evAt x)
    comparison x = reflect e (funUniversal [1] C) _ _
      ((identity-evaluation x) ⁻¹ ∙
        (constant-evaluation x ∙ funPre-β {D = C} (const {P = [1]} x)))
```

The two constant-edge cones are universal by cancellation against the actual
Segal cone. After pasting, both outer horizontal maps are equivalences.
No replacement of their pasted matching is needed for that argument.

```agda
module At {Γ : Context} (C : CAT Γ) where
  private
    module Retractions = RetractionPullbacks C
    module Constant = ConstantRestriction C
    module LowerLeft = Pasting (identityArrow {C = C}) ev₁ ev₀
      (triangle-cone C) (segal-isEquiv C)
    module LowerRight = Pasting (identityArrow {C = C}) ev₀ ev₁
      (cone-swap (triangle-cone C))
      (SwappedCone.isPullback (triangle-cone C) (segal-isEquiv C))

  left-constant-cone : Cone (identityArrow {C = C}) edge₂ (Ar C)
  left-constant-cone = record
    { left = ev₀; right = funPre s₀
    ; match = (funPre-comp d₂ s₀) ⁻¹ ∙
        ((funPre⁼ s₀-d₂) ⁻¹ ∙ (Constant.comparison zero) ⁻¹) }
  left-constant-isPullback : IsPullback left-constant-cone
  left-constant-isPullback = LowerLeft.unpaste-isPullback left-constant-cone
    (horizontal-equivalences (LowerLeft.Paste.paste left-constant-cone)
      (equiv-transport (identity-target ⁻¹) (id-isEquiv C))
      (equiv-transport
        ((funPre-id [1] C ∙ (funPre⁼ s₀-d₀ ∙ funPre-comp d₀ s₀)) ⁻¹)
        (id-isEquiv (Ar C))))

  right-constant-cone : Cone (identityArrow {C = C}) edge₀ (Ar C)
  right-constant-cone = record
    { left = ev₁; right = funPre s₁
    ; match = (funPre-comp d₀ s₁) ⁻¹ ∙
        ((funPre⁼ s₁-d₀) ⁻¹ ∙ (Constant.comparison one) ⁻¹) }
  right-constant-isPullback : IsPullback right-constant-cone
  right-constant-isPullback = LowerRight.unpaste-isPullback right-constant-cone
    (horizontal-equivalences (LowerRight.Paste.paste right-constant-cone)
      (equiv-transport (identity-source ⁻¹) (id-isEquiv C))
      (equiv-transport
        ((funPre-id [1] C ∙ (funPre⁼ s₁-d₂ ∙ funPre-comp d₂ s₁)) ⁻¹)
        (id-isEquiv (Ar C))))

  module Left where
    private
      module Whole = Pasting (funPre {D = C} j₁) edge₂ identityArrow
        (cone-swap left-constant-cone)
        (SwappedCone.isPullback left-constant-cone left-constant-isPullback)
      pasted = Whole.Paste.paste (cone-swap Retractions.lower-cone)
      pasted-isPullback = Whole.paste-isPullback (cone-swap Retractions.lower-cone)
        (SwappedCone.isPullback Retractions.lower-cone Retractions.lower-isPullback)

    side-comparison : (edge₂ ∘ funPre {D = C} j₁) =₁ funPre (insert zero)
    side-comparison = funPre⁼ j₁-d₂ ∙ funPre-comp d₂ j₁
    square : Cone (funPre {D = C} (insert zero)) identityArrow (Triangles C)
    square = cone-change-left side-comparison pasted
    square-isPullback : IsPullback square
    square-isPullback = isPullback-change-left side-comparison pasted pasted-isPullback

    vertex-comparison : Cone.right square =₁ evAt {C = C} vertex₀
    vertex-comparison = evAt-cong d₁-zero ∙ evAt-pre zero d₁
    vertex-square : Cone (funPre {D = C} (insert zero)) identityArrow (Triangles C)
    vertex-square = cone-change-legs square (funPre p₀) (evAt vertex₀)
      (id₌ (funPre p₀)) vertex-comparison
    vertex-image : ConeIdentification₁ square vertex-square
    vertex-image = cone-change-legs-β square (funPre p₀) (evAt vertex₀)
      (id₌ (funPre p₀)) vertex-comparison
    vertex-square-isPullback : IsPullback vertex-square
    vertex-square-isPullback = isPullback-cone-identification vertex-image square-isPullback

  module Right where
    private
      module Whole = Pasting (funPre {D = C} j₀) edge₀ identityArrow
        (cone-swap right-constant-cone)
        (SwappedCone.isPullback right-constant-cone right-constant-isPullback)
      pasted = Whole.Paste.paste (cone-swap Retractions.upper-cone)
      pasted-isPullback = Whole.paste-isPullback (cone-swap Retractions.upper-cone)
        (SwappedCone.isPullback Retractions.upper-cone Retractions.upper-isPullback)

    side-comparison : (edge₀ ∘ funPre {D = C} j₀) =₁ funPre (insert one)
    side-comparison = funPre⁼ j₀-d₀ ∙ funPre-comp d₀ j₀
    square : Cone (funPre {D = C} (insert one)) identityArrow (Triangles C)
    square = cone-change-left side-comparison pasted
    square-isPullback : IsPullback square
    square-isPullback = isPullback-change-left side-comparison pasted pasted-isPullback

    vertex-comparison : Cone.right square =₁ evAt {C = C} vertex₂
    vertex-comparison = evAt-cong d₁-one ∙ evAt-pre one d₁
    vertex-square : Cone (funPre {D = C} (insert one)) identityArrow (Triangles C)
    vertex-square = cone-change-legs square (funPre p₂) (evAt vertex₂)
      (id₌ (funPre p₂)) vertex-comparison
    vertex-image : ConeIdentification₁ square vertex-square
    vertex-image = cone-change-legs-β square (funPre p₂) (evAt vertex₂)
      (id₌ (funPre p₂)) vertex-comparison
    vertex-square-isPullback : IsPullback vertex-square
    vertex-square-isPullback = isPullback-cone-identification vertex-image square-isPullback
```
