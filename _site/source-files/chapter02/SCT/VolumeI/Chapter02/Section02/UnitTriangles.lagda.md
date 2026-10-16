# The specified degenerate unit triangles

The two simplicial degeneracies compare with the identity pairs as whole
cocones. Their actual reflected edge comparisons retain the native
point-evaluation images, including the original identity-family frames.
These concrete shapes feed the two universal unit presentations; the
generic evaluation and reflection arguments have shared owners.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section02.UnitTriangles where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition; postWhisker-id₌; preWhisker-id₌; module Boundaries; inv₌)
open Composition
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle)
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌; interchange-fixedInner; interchange-fixedOuter; interchange; reassociateFour; postWhisker-comp₌; const-evaluate)
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
open import SCT.VolumeI.Chapter01.Section08.Cocones
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint; evAt-cong; evAt-pre)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism
  using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₀; d₁; d₂; s₀; s₁; s₀-d₀; s₀-d₁; s₀-d₂; s₁-d₀; s₁-d₁; s₁-d₂; face-middle; face-bottom; face-top; module MiddleVertex; module BottomVertex; module TopVertex)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; postWhisker-comp-One; postWhisker-id-One; whisker-mixed-One; left-unitor-comp; right-unitor-comp; triangle-whiskered; pentagon-whiskered-right; identity-unitors; triangle-with-identity)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
  using (binary-pre; binary-pre-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
  using (productMap-pair; productMap-pair-inner-One; productMap-pair-outer-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair₌-unique; pair⁼-comp; pair⁼-cong; pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)
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
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairingIdentity
  using (module ProductPairingIdentity)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationIdentity
  using (module PointEvaluationIdentity)
open import SCT.VolumeI.Chapter02.Section02.ConstantRestrictionEvaluation
  using (module ConstantEvaluation)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyReflection using (module ReflectedEndpoint)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationComposition using (module InsertionComposition)
open import SCT.VolumeI.Chapter02.Section01.PointEvaluationShapes using (module ShapeEvaluationNaturality; module IdentityShapeEvaluation)

private
  module _ {Γ : Context} where
    constant-boundary : (x z : MAP One ([1] {Γ = Γ}))
      → (const {P = [1]} z ∘ x) =₁ z
    constant-boundary x z = const-One z ∙ const-pre z x

    regroup-compatible : {X C : CAT Γ} {u u′ v v′ l′ r′ z : MAP X C}
      (A : u =₁ u′) (B : v =₁ v′) (l : u =₁ l′) (r : v =₁ r′)
      (nl : l′ =₁ z) (nr : r′ =₁ z) (δ : v′ =₁ u′)
      → ((nl ∙ (l ∙ A ⁻¹)) ∙ δ) =₂ (nr ∙ (r ∙ B ⁻¹))
      → (((nl ∙ l) ∙ A ⁻¹) ∙ δ) =₂ ((nr ∙ r) ∙ B ⁻¹)
    regroup-compatible A B l r nl nr δ given =
      (comp₌-assoc nr r (B ⁻¹)) ⁻¹ ∙
        (given ∙ comp₌-cong (comp₌-assoc nl l (A ⁻¹)) (id₌ δ))

    framed-junction : {X C : CAT Γ} {u u′ v v′ l′ r′ z : MAP X C}
      (A : u =₁ u′) (B : v =₁ v′) (l : u =₁ l′) (r : v =₁ r′)
      (nl : l′ =₁ z) (nr : r′ =₁ z) (δ : v′ =₁ u′)
      → (((nl ∙ l) ∙ A ⁻¹) ∙ δ) =₂ ((nr ∙ r) ∙ B ⁻¹)
      → ((nr ⁻¹ ∙ nl) ∙ l) =₂ (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A)))
    framed-junction A B l r nl nr δ given =
      inv-comp-left nr (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A))) ∙
        (comp₌-cong (id₌ (nr ⁻¹)) (normalized ⁻¹) ∙ comp₌-assoc (nr ⁻¹) nl l)
      where
        inverse-compatible : (((nr ∙ r) ∙ B ⁻¹) ∙ δ ⁻¹) =₂ ((nl ∙ l) ∙ A ⁻¹)
        inverse-compatible = comp-inv-right ((nl ∙ l) ∙ A ⁻¹) δ ∙
          comp₌-cong (given ⁻¹) (id₌ (δ ⁻¹))
        normalized : (nr ∙ (r ∙ (B ⁻¹ ∙ (δ ⁻¹ ∙ A)))) =₂ (nl ∙ l)
        normalized = inv-comp-right (nl ∙ l) A ∙
          (comp₌-cong inverse-compatible (id₌ A) ∙
            ((comp₌-assoc ((nr ∙ r) ∙ B ⁻¹) (δ ⁻¹) A) ⁻¹ ∙
              ((comp₌-assoc (nr ∙ r) (B ⁻¹) (δ ⁻¹ ∙ A)) ⁻¹ ∙
                (comp₌-assoc nr r (B ⁻¹ ∙ (δ ⁻¹ ∙ A))) ⁻¹)))

    forward-junction : {X C : CAT Γ} {u u′ v v′ l′ r′ z : MAP X C}
      (A : u =₁ u′) (B : v =₁ v′) (l : u =₁ l′) (r : v =₁ r′)
      (nl : l′ =₁ z) (nr : r′ =₁ z) (δ : u′ =₁ v′)
      → (((nr ∙ r) ∙ B ⁻¹) ∙ δ) =₂ ((nl ∙ l) ∙ A ⁻¹)
      → ((nr ⁻¹ ∙ nl) ∙ l) =₂ (r ∙ (B ⁻¹ ∙ (δ ∙ A)))
    forward-junction A B l r nl nr δ given =
      inv-comp-left nr (r ∙ (B ⁻¹ ∙ (δ ∙ A))) ∙
        (comp₌-cong (id₌ (nr ⁻¹)) (normalized ⁻¹) ∙ comp₌-assoc (nr ⁻¹) nl l)
      where
        normalized : (nr ∙ (r ∙ (B ⁻¹ ∙ (δ ∙ A)))) =₂ (nl ∙ l)
        normalized = inv-comp-right (nl ∙ l) A ∙
          (comp₌-cong given (id₌ A) ∙
            ((comp₌-assoc ((nr ∙ r) ∙ B ⁻¹) δ A) ⁻¹ ∙
              ((comp₌-assoc (nr ∙ r) (B ⁻¹) (δ ∙ A)) ⁻¹ ∙
                (comp₌-assoc nr r (B ⁻¹ ∙ (δ ∙ A))) ⁻¹)))

module _ {Γ : Context} where
  triangle-edges : Cocone (one {Γ = Γ}) zero [2]
  triangle-edges = record { left = d₂; right = d₀; match = face-middle ⁻¹ }
  triangle-source : Cocone (zero {Γ = Γ}) zero [2]
  triangle-source = record { left = d₁; right = d₂; match = face-bottom }
  triangle-target : Cocone (one {Γ = Γ}) one [2]
  triangle-target = record { left = d₀; right = d₁; match = face-top }

  source-identity-pair target-identity-pair : Cocone (one {Γ = Γ}) zero [1]
  source-identity-pair = record
    { left = const zero; right = id [1]
    ; match = (comp-unitˡ zero) ⁻¹ ∙ constant-boundary one zero }
  target-identity-pair = record
    { left = id [1]; right = const one
    ; match = (constant-boundary zero one) ⁻¹ ∙ comp-unitˡ one }

  source-unit-matching : CoconeIdentification₁
    (cocone-postcompose s₀ triangle-edges) source-identity-pair
  source-unit-matching = record
    { left = s₀-d₂; right = s₀-d₀
    ; compatible = comp₌-cong (id₌ (s₀-d₀ ▷ zero))
        (comp₌-cong (id₌ ((comp-assoc zero d₀ s₀) ⁻¹))
          (comp₌-cong ((postWhisker-inverse s₀ face-middle) ⁻¹)
            (id₌ (comp-assoc one d₂ s₀)))) ∙
        framed-junction (comp-assoc one d₂ s₀) (comp-assoc zero d₀ s₀)
          (s₀-d₂ ▷ one) (s₀-d₀ ▷ zero) (constant-boundary one zero) (comp-unitˡ zero)
          (s₀ ◁ face-middle)
          (regroup-compatible (comp-assoc one d₂ s₀) (comp-assoc zero d₀ s₀)
            (s₀-d₂ ▷ one) (s₀-d₀ ▷ zero) (constant-boundary one zero) (comp-unitˡ zero)
            (s₀ ◁ face-middle) MiddleVertex.source-compatible) }

  target-unit-matching : CoconeIdentification₁
    (cocone-postcompose s₁ triangle-edges) target-identity-pair
  target-unit-matching = record
    { left = s₁-d₂; right = s₁-d₀
    ; compatible = comp₌-cong (id₌ (s₁-d₀ ▷ zero))
        (comp₌-cong (id₌ ((comp-assoc zero d₀ s₁) ⁻¹))
          (comp₌-cong ((postWhisker-inverse s₁ face-middle) ⁻¹)
            (id₌ (comp-assoc one d₂ s₁)))) ∙
        framed-junction (comp-assoc one d₂ s₁) (comp-assoc zero d₀ s₁)
          (s₁-d₂ ▷ one) (s₁-d₀ ▷ zero) (comp-unitˡ one) (constant-boundary zero one)
          (s₁ ◁ face-middle)
          (regroup-compatible (comp-assoc one d₂ s₁) (comp-assoc zero d₀ s₁)
            (s₁-d₂ ▷ one) (s₁-d₀ ▷ zero) (comp-unitˡ one) (constant-boundary zero one)
            (s₁ ◁ face-middle) MiddleVertex.target-compatible) }

module _ {Γ : Context} where
  source-unit-source-pair target-unit-source-pair : Cocone (zero {Γ = Γ}) zero [1]
  source-unit-source-pair = record
    { left = id [1]; right = const zero
    ; match = (constant-boundary zero zero) ⁻¹ ∙ comp-unitˡ zero }
  target-unit-source-pair = record
    { left = id [1]; right = id [1]
    ; match = (comp-unitˡ zero) ⁻¹ ∙ comp-unitˡ zero }

  source-unit-target-pair target-unit-target-pair : Cocone (one {Γ = Γ}) one [1]
  source-unit-target-pair = record
    { left = id [1]; right = id [1]
    ; match = (comp-unitˡ one) ⁻¹ ∙ comp-unitˡ one }
  target-unit-target-pair = record
    { left = const one; right = id [1]
    ; match = (comp-unitˡ one) ⁻¹ ∙ constant-boundary one one }

  source-unit-source : CoconeIdentification₁
    (cocone-postcompose s₀ triangle-source) source-unit-source-pair
  source-unit-source = record
    { left = s₀-d₁; right = s₀-d₂
    ; compatible = forward-junction (comp-assoc zero d₁ s₀) (comp-assoc zero d₂ s₀)
        (s₀-d₁ ▷ zero) (s₀-d₂ ▷ zero) (comp-unitˡ zero) (constant-boundary zero zero)
        (s₀ ◁ face-bottom)
        (regroup-compatible (comp-assoc zero d₂ s₀) (comp-assoc zero d₁ s₀)
          (s₀-d₂ ▷ zero) (s₀-d₁ ▷ zero) (constant-boundary zero zero) (comp-unitˡ zero)
          (s₀ ◁ face-bottom) BottomVertex.source-compatible) }

  target-unit-source : CoconeIdentification₁
    (cocone-postcompose s₁ triangle-source) target-unit-source-pair
  target-unit-source = record
    { left = s₁-d₁; right = s₁-d₂
    ; compatible = forward-junction (comp-assoc zero d₁ s₁) (comp-assoc zero d₂ s₁)
        (s₁-d₁ ▷ zero) (s₁-d₂ ▷ zero) (comp-unitˡ zero) (comp-unitˡ zero)
        (s₁ ◁ face-bottom)
        (regroup-compatible (comp-assoc zero d₂ s₁) (comp-assoc zero d₁ s₁)
          (s₁-d₂ ▷ zero) (s₁-d₁ ▷ zero) (comp-unitˡ zero) (comp-unitˡ zero)
          (s₁ ◁ face-bottom) BottomVertex.target-compatible) }

  source-unit-target : CoconeIdentification₁
    (cocone-postcompose s₀ triangle-target) source-unit-target-pair
  source-unit-target = record
    { left = s₀-d₀; right = s₀-d₁
    ; compatible = forward-junction (comp-assoc one d₀ s₀) (comp-assoc one d₁ s₀)
        (s₀-d₀ ▷ one) (s₀-d₁ ▷ one) (comp-unitˡ one) (comp-unitˡ one)
        (s₀ ◁ face-top)
        (regroup-compatible (comp-assoc one d₁ s₀) (comp-assoc one d₀ s₀)
          (s₀-d₁ ▷ one) (s₀-d₀ ▷ one) (comp-unitˡ one) (comp-unitˡ one)
          (s₀ ◁ face-top) TopVertex.source-compatible) }

  target-unit-target : CoconeIdentification₁
    (cocone-postcompose s₁ triangle-target) target-unit-target-pair
  target-unit-target = record
    { left = s₁-d₀; right = s₁-d₁
    ; compatible = forward-junction (comp-assoc one d₀ s₁) (comp-assoc one d₁ s₁)
        (s₁-d₀ ▷ one) (s₁-d₁ ▷ one) (constant-boundary one one) (comp-unitˡ one)
        (s₁ ◁ face-top)
        (regroup-compatible (comp-assoc one d₁ s₁) (comp-assoc one d₀ s₁)
          (s₁-d₁ ▷ one) (s₁-d₀ ▷ one) (comp-unitˡ one) (constant-boundary one one)
          (s₁ ◁ face-top) TopVertex.target-compatible) }

module UniversalEdges {Γ : Context} (C : CAT Γ) where
  private
    X = Ar C
    e = funEval {C = [1]} {D = C}
  universal-arrow : MorphismFamily (ev₀ {C = C}) ev₁
  universal-arrow = record
    { arrow = id X; source-frame = comp-unitʳ ev₀; target-frame = comp-unitʳ ev₁ }

  private
    constant-insertion : (x : MAP One ([1] {Γ = Γ}))
      → productMap (id X) (const {P = [1]} x) =₁ (insert x ∘ pr₁)
    constant-insertion x = (pair-pre (id X) (const {P = X} x) pr₁) ⁻¹ ∙
      pair⁼ (id₌ (id X ∘ pr₁))
        ((comp-assoc pr₁ (terminate X) x) ⁻¹ ∙
          ((x ◁ terminal-identification (terminate [1] ∘ pr₂) (terminate X ∘ pr₁)) ∙
            comp-assoc pr₂ (terminate [1]) x))
    constant-evaluation : (x : MAP One ([1] {Γ = Γ}))
      → (e ∘ productMap (id X) (const {P = [1]} x)) =₁ (evAt x ∘ pr₁)
    constant-evaluation x = (comp-assoc pr₁ (insert x) e) ⁻¹ ∙ (e ◁ constant-insertion x)
    identity-evaluation : (e ∘ productMap (id X) (id [1])) =₁ e
    identity-evaluation = comp-unitʳ e ∙ (e ◁ productMap-id X [1])

  module Degeneracy (s : MAP ([2] {Γ = Γ}) [1]) where
    triangle : MAP X (Fun [2] C)
    triangle = funPre s
    edge-image : (d : MAP ([1] {Γ = Γ}) [2])
      → funUncurry (funPre d ∘ triangle) =₁ (e ∘ productMap (id X) (s ∘ d))
    edge-image d = (e ◁ restriction-compositor {P = X} d s) ∙
      (comp-assoc (product-restriction {P = X} d) (product-restriction s) e ∙
        ((funPre-β {D = C} s ▷ product-restriction {P = X} d) ∙
          funPre-uncurry d triangle))

    module IdentityEdge (d : MAP ([1] {Γ = Γ}) [2]) (ε : (s ∘ d) =₁ id [1]) where
      diagram-image : funUncurry (funPre d ∘ triangle) =₁ e
      diagram-image = identity-evaluation ∙
        ((e ◁ productMap-cong (id₌ (id X)) ε) ∙ edge-image d)
      private
        module Reflected = ReflectedEndpoint (funPre d ∘ triangle) (id X) e
          (evaluate-id e) diagram-image
      comparison : (funPre d ∘ triangle) =₁ id X
      comparison = Reflected.comparison
      image : evaluate-cong e comparison =₂ ((evaluate-id e) ⁻¹ ∙ diagram-image)
      image = Reflected.image
      endpoint : (x : MAP One ([1] {Γ = Γ}))
        → (((evaluate-id e ▷ insert x) ∙ AtPoint.uncurry-image x (id X)) ∙
            (evAt x ◁ comparison)) =₂
          ((diagram-image ▷ insert x) ∙ AtPoint.uncurry-image x (funPre d ∘ triangle))
      endpoint = Reflected.endpoint

    module ConstantEdge (d : MAP ([1] {Γ = Γ}) [2]) (z : MAP One [1])
      (ε : (s ∘ d) =₁ const z) where
      diagram-image : funUncurry (funPre d ∘ triangle) =₁ (evAt {C = C} z ∘ pr₁)
      diagram-image = constant-evaluation z ∙
        ((e ◁ productMap-cong (id₌ (id X)) ε) ∙ edge-image d)
      private
        target = MorphismFamily.arrow (identity-family (evAt {C = C} z))
        target-β = funCurry-β (evAt {C = C} z ∘ pr₁ {C = X} {D = [1]})
        module Reflected = ReflectedEndpoint (funPre d ∘ triangle) target
          (evAt {C = C} z ∘ pr₁) target-β diagram-image
      comparison : (funPre d ∘ triangle) =₁ MorphismFamily.arrow (identity-family (evAt {C = C} z))
      comparison = Reflected.comparison
      image : evaluate-cong e comparison =₂ (target-β ⁻¹ ∙ diagram-image)
      image = Reflected.image
      endpoint : (x : MAP One ([1] {Γ = Γ}))
        → (((target-β ▷ insert x) ∙ AtPoint.uncurry-image x target) ∙
            (evAt x ◁ comparison)) =₂
          ((diagram-image ▷ insert x) ∙ AtPoint.uncurry-image x (funPre d ∘ triangle))
      endpoint = Reflected.endpoint

  module Source where
    module D = Degeneracy s₀
    module First = D.ConstantEdge d₂ zero s₀-d₂
    module Second = D.IdentityEdge d₀ s₀-d₀
    module Long = D.IdentityEdge d₁ s₀-d₁
  module Target where
    module D = Degeneracy s₁
    module First = D.IdentityEdge d₂ s₁-d₂
    module Second = D.ConstantEdge d₀ one s₁-d₀
    module Long = D.IdentityEdge d₁ s₁-d₁

module IdentityDegeneracyEndpoint {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (epsilon : (s ∘ d) =₁ id [1]) (a : MAP One ([1] {Γ = Γ})) where
  private
    module U = UniversalEdges C
    module D = U.Degeneracy s
    module Edge = D.IdentityEdge d epsilon
    module Point = PointEvaluationIdentity {C = C} a
    h : MAP (Ar C) (Ar C)
    h = funPre d ∘ funPre s
    i = insert {P = Ar C} a

  endpoint-image :
    (comp-unitʳ (evAt {C = C} a) ∙ (evAt a ◁ Edge.comparison)) =₂
    ((Edge.diagram-image ▷ i) ∙ AtPoint.uncurry-image a h)
  endpoint-image = Edge.endpoint a ∙
    comp₌-cong (Point.identity-normalization ⁻¹) (id₌ (evAt a ◁ Edge.comparison))

module ConstantDegeneracyEndpoint {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (z : MAP One ([1] {Γ = Γ})) (epsilon : (s ∘ d) =₁ const z) where
  private
    module U = UniversalEdges C
    module D = U.Degeneracy s
    module Edge = D.ConstantEdge d z epsilon
    X = Ar C
    f : MAP X C
    f = evAt z
    h : MAP X (Ar C)
    h = funPre d ∘ funPre s
    target-arrow = MorphismFamily.arrow (identity-family f)
    target-beta = funCurry-β (f ∘ pr₁ {C = X} {D = [1]})

  prefix : (a : MAP One ([1] {Γ = Γ})) → ((f ∘ pr₁) ∘ insert a) =₁ f
  prefix a = comp-unitʳ f ∙
    ((f ◁ pair-β₁ (id X) (const a)) ∙ comp-assoc (insert a) pr₁ f)

  private
    boundary : (a : MAP One ([1] {Γ = Γ})) → (evAt a ∘ target-arrow) =₁ f
    boundary a = comp-unitʳ f ∙
      ((f ◁ pair-β₁ (id X) (const a)) ∙
        (comp-assoc (insert a) pr₁ f ∙ AtPoint.curry-image a (f ∘ pr₁)))
    boundary-factor : (a : MAP One ([1] {Γ = Γ})) → boundary a =₂
      (prefix a ∙ ((target-beta ▷ insert a) ∙ AtPoint.uncurry-image a target-arrow))
    boundary-factor a = (comp₌-assoc (comp-unitʳ f)
        ((f ◁ pair-β₁ (id X) (const a)) ∙ comp-assoc (insert a) pr₁ f)
        (AtPoint.curry-image a (f ∘ pr₁))) ⁻¹ ∙
      comp₌-cong (id₌ (comp-unitʳ f))
        ((comp₌-assoc (f ◁ pair-β₁ (id X) (const a))
          (comp-assoc (insert a) pr₁ f) (AtPoint.curry-image a (f ∘ pr₁))) ⁻¹)
    boundary-image : (a : MAP One ([1] {Γ = Γ})) →
      (boundary a ∙ (evAt a ◁ Edge.comparison)) =₂
      (prefix a ∙ ((Edge.diagram-image ▷ insert a) ∙ AtPoint.uncurry-image a h))
    boundary-image a = comp₌-cong (id₌ (prefix a)) (Edge.endpoint a) ∙
      (comp₌-assoc (prefix a)
        ((target-beta ▷ insert a) ∙ AtPoint.uncurry-image a target-arrow)
        (evAt a ◁ Edge.comparison) ∙
        comp₌-cong (boundary-factor a) (id₌ (evAt a ◁ Edge.comparison)))

  source-image :
    (MorphismFamily.source-frame (identity-family f) ∙ (ev₀ ◁ Edge.comparison)) =₂
    (prefix zero ∙ ((Edge.diagram-image ▷ insert zero) ∙ AtPoint.uncurry-image zero h))
  source-image = boundary-image zero

  target-image :
    (MorphismFamily.target-frame (identity-family f) ∙ (ev₁ ◁ Edge.comparison)) =₂
    (prefix one ∙ ((Edge.diagram-image ▷ insert one) ∙ AtPoint.uncurry-image one h))
  target-image = boundary-image one

module IdentityEdgePointEvaluation {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (epsilon : (s ∘ d) =₁ id [1]) (a : MAP One ([1] {Γ = Γ})) where
  private
    F : CAT Γ
    F = Ar C
    e : MAP (F × [1]) C
    e = funEval
    i : MAP F (F × [1])
    i = insert a
    module U = UniversalEdges C
    module D = U.Degeneracy s
    module Edge = D.IdentityEdge d epsilon
    module Endpoint = IdentityDegeneracyEndpoint C s d epsilon a
    module Identity = IdentityShapeEvaluation {C = C} a
    module Change = ShapeEvaluationNaturality {C = C} epsilon a
    module Shape = InsertionComposition F
    h : MAP F F
    h = funPre d ∘ funPre s
    J = productMap (id F) (s ∘ d)
    Jid = productMap (id F) (id [1])
    direct = post-triangle e J i (Shape.χ (s ∘ d) a)
    direct-id = post-triangle e Jid i (Shape.χ (id [1]) a)
    identity-image = comp-unitʳ e ∙ (e ◁ productMap-id F [1])
    shape-image = e ◁ productMap-cong (id₌ (id F)) epsilon
    edge-image = D.edge-image d
    mu = AtPoint.uncurry-image a h
    tail = (edge-image ▷ i) ∙ mu
    L = evAt-cong {C = C} (comp-unitˡ a)
    E = evAt-cong {C = C} (epsilon ▷ a)
    alpha = shape-image ▷ i
    N = identity-image ▷ i
    expand : ((Edge.diagram-image ▷ i) ∙ mu) =₂ (N ∙ (alpha ∙ tail))
    expand = comp₌-cong (id₌ N) (comp₌-assoc alpha (edge-image ▷ i) mu) ∙
      (comp₌-assoc N (alpha ∙ (edge-image ▷ i)) mu ∙
        (comp₌-cong
          (comp₌-cong (id₌ N) (preWhisker-comp₌ shape-image edge-image i)) (id₌ mu) ∙
          comp₌-cong (preWhisker-comp₌ identity-image (shape-image ∙ edge-image) i) (id₌ mu)))
    step₁ = comp₌-cong (Identity.compatibility ⁻¹) (id₌ (alpha ∙ tail))
    step₂ = comp₌-assoc L direct-id (alpha ∙ tail)
    step₃ = comp₌-cong (id₌ L) ((comp₌-assoc direct-id alpha tail) ⁻¹)
    step₄ = comp₌-cong (id₌ L) (comp₌-cong Change.compatibility (id₌ tail))
    step₅ = comp₌-cong (id₌ L) (comp₌-assoc E direct tail)
    step₆ = (comp₌-assoc L E (direct ∙ tail)) ⁻¹
    shape-normal : (N ∙ (alpha ∙ tail)) =₂ ((L ∙ E) ∙ (direct ∙ tail))
    shape-normal = step₆ ∙ (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙ step₁))))

  endpoint-shape :
    (comp-unitʳ (evAt {C = C} a) ∙ (evAt a ◁ Edge.comparison)) =₂
    ((evAt-cong {C = C} (comp-unitˡ a) ∙ evAt-cong (epsilon ▷ a)) ∙
      (post-triangle e J i (Shape.χ (s ∘ d) a) ∙
        ((D.edge-image d ▷ i) ∙ AtPoint.uncurry-image a h)))
  endpoint-shape = shape-normal ∙ (expand ∙ Endpoint.endpoint-image)

module ConstantEdgePointEvaluation {Γ : Context} (C : CAT Γ)
  (s : MAP ([2] {Γ = Γ}) [1]) (d : MAP ([1] {Γ = Γ}) [2])
  (z : MAP One ([1] {Γ = Γ})) (epsilon : (s ∘ d) =₁ const z) where
  private
    F : CAT Γ
    F = Ar C
    e : MAP (F × [1]) C
    e = funEval
    module U = UniversalEdges C
    module D = U.Degeneracy s
    module Edge = D.ConstantEdge d z epsilon
    module Endpoint = ConstantDegeneracyEndpoint C s d z epsilon
    module Shape = InsertionComposition F
    h : MAP F F
    h = funPre d ∘ funPre s
    J = productMap (id F) (s ∘ d)
    Jconst = productMap (id F) (const {P = [1]} z)
    shape-image = e ◁ productMap-cong (id₌ (id F)) epsilon
    edge-image = D.edge-image d

  module At (a : MAP One ([1] {Γ = Γ})) where
    private
      i : MAP F (F × [1])
      i = insert a
      module Constant = ConstantEvaluation {C = C} a z
      module Change = ShapeEvaluationNaturality {C = C} epsilon a
      direct = post-triangle e J i (Shape.χ (s ∘ d) a)
      direct-constant = post-triangle e Jconst i (Shape.χ (const {P = [1]} z) a)
      mu = AtPoint.uncurry-image a h
      tail = (edge-image ▷ i) ∙ mu
      L = evAt-cong {C = C} (const-evaluate z a)
      E = evAt-cong {C = C} (epsilon ▷ a)
      alpha = shape-image ▷ i
      N = Constant.comparison ▷ i
      prefix = Endpoint.prefix a
      expand : ((Edge.diagram-image ▷ i) ∙ mu) =₂ (N ∙ (alpha ∙ tail))
      expand = comp₌-cong (id₌ N) (comp₌-assoc alpha (edge-image ▷ i) mu) ∙
        (comp₌-assoc N (alpha ∙ (edge-image ▷ i)) mu ∙
          (comp₌-cong
            (comp₌-cong (id₌ N) (preWhisker-comp₌ shape-image edge-image i)) (id₌ mu) ∙
            comp₌-cong (preWhisker-comp₌ Constant.comparison (shape-image ∙ edge-image) i) (id₌ mu)))
      step₁ = (comp₌-assoc prefix N (alpha ∙ tail)) ⁻¹
      step₂ = comp₌-cong Constant.compatibility (id₌ (alpha ∙ tail))
      step₃ = comp₌-assoc L direct-constant (alpha ∙ tail)
      step₄ = comp₌-cong (id₌ L) ((comp₌-assoc direct-constant alpha tail) ⁻¹)
      step₅ = comp₌-cong (id₌ L) (comp₌-cong Change.compatibility (id₌ tail))
      step₆ = comp₌-cong (id₌ L) (comp₌-assoc E direct tail)
      step₇ = (comp₌-assoc L E (direct ∙ tail)) ⁻¹

    shape-route : (evAt {C = C} a ∘ h) =₁ evAt z
    shape-route = (L ∙ E) ∙ (direct ∙ tail)

    diagram-shape :
      (Endpoint.prefix a ∙ ((Edge.diagram-image ▷ i) ∙ AtPoint.uncurry-image a h)) =₂ shape-route
    diagram-shape = step₇ ∙ (step₆ ∙ (step₅ ∙ (step₄ ∙ (step₃ ∙ (step₂ ∙
      (step₁ ∙ comp₌-cong (id₌ prefix) expand))))))

  source-shape :
    (MorphismFamily.source-frame (identity-family (evAt {C = C} z)) ∙
      (ev₀ ◁ Edge.comparison)) =₂ At.shape-route zero
  source-shape = At.diagram-shape zero ∙ Endpoint.source-image

  target-shape :
    (MorphismFamily.target-frame (identity-family (evAt {C = C} z)) ∙
      (ev₁ ◁ Edge.comparison)) =₂ At.shape-route one
  target-shape = At.diagram-shape one ∙ Endpoint.target-image
```
