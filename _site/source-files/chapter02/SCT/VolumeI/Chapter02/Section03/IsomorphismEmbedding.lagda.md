# Isomorphisms embed into all morphisms

Composition with an invertible family acts on the ordinary endpoint
pullbacks. The action retains the full cone matching and its change under
restriction. Left and right inverse families will provide a retraction and
a section separately.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter02.Section03.IsomorphismEmbedding where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; inv₌; comp-assoc; postWhisker-id₌; preWhisker-id₌; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (comp₌-cong; comp₌-assoc)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (comp₌-unitˡ-One; comp₌-unitʳ-One; comp₌-inverseʳ-One; inverse-composite; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (restrict-triangle; restrict-change-square-One; restrict-triangle-assoc)
open import SCT.VolumeI.Chapter01.Section06.Cones
  using (Cone; ConeIdentification₁; cone-restrict)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications
  using (cone-identification-restrict-One; cone-compose; cone-inverse;
    cone-restrict-assoc; cone-restrict-id)
open import SCT.VolumeI.Chapter01.Section06.Pullbacks
  using (Pullback; pullback₁; pullback₂; pullback-cone; pullback-factor;
    pullback-factor-β; pullback-factor-β₁; pullback-factor-β₂)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (pullback-reflect)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; MorphismFamily; MorphismFamilyIdentification)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyOperations
  using (family-comparison; restrict-family; retarget-family;
    retarget-family-comparison; restrict-family-comparison; module FamilyComparison)
open import SCT.VolumeI.Chapter02.Section01.MorphismFamilyComparisons
  using (compose-family-comparisons; id-family-comparison; inverse-family-comparison)
open import SCT.VolumeI.Chapter02.Section01.Triangles using (short-edges; Triangles; triangle-cone; edge₀; edge₁; edge₂)
import SCT.VolumeI.Chapter02.Section02.MorphismComposition as MC
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionTransport using (module CompositionTransport)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionComparisons using (module CompositionComparisons)
open import SCT.VolumeI.Chapter02.Section02.SegalAxiom using (segal-isEquiv)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionAssociativity using (associativity)
open import SCT.VolumeI.Chapter02.Section02.MorphismCompositionUnits using (module MorphismCompositionUnits)
open import SCT.VolumeI.Chapter02.Section01.IdentityFamilyRestriction using (module IdentityFamilyRestriction)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (identity-family)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (section-retraction-isEquiv)
open import SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies using (InverseFamily)
open import SCT.VolumeI.Chapter01.Section03.Equivalences
  using (equiv-transport; equiv-compose; equiv-cancel-right; id-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback; pullback-factor-restrict)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions
  using (pullback-cone-isPullback; pullback-swap; pullback-swap-isEquiv; left-isEquiv-from-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality using (isPullback-cone-identification; module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport
  using (cone-swap; cone-swap-identification; cone-swap-restrict; cone-swap-twice; cone-retarget-match-identification)
open import SCT.VolumeI.Chapter01.Section06.ConePasting using (postcompose-cone-left)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma using (module Pasting)
open import SCT.VolumeI.Chapter02.Section02.TriangleCompletionPresentation using (module CompleteTriangle)
open import SCT.VolumeI.Chapter02.Section02.FramedTrianglePresentations using (presented-composition)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks using (module Nested; module ChosenNested)
open import SCT.VolumeI.Chapter02.Section01.Morphisms using (identityArrow; identity-source; identity-target)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms using (Iso; isoArrow)
open import SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies using (iso-inverse-family)
open import SCT.VolumeI.Chapter02.Section03.InverseMorphismFamilies using (module UniversalIsoFamily)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms
  using (InverseTriangles; firstInverseTriangle; secondInverseTriangle;
    inverseLongEdges; inverseIdentityEdges; isoTriangles)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.Coherence using (comp-unitˡ; comp-unitʳ)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-comp; swap; swap-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (equiv-cancel-left)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section06.Pullbacks using (pullback-match)
open import SCT.VolumeI.Chapter01.Section06.ProductPullbacks using (module Product)
open import SCT.VolumeI.Chapter01.Section06.DiagonalPullbacks using (module DiagonalPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctoriality
  using (CospanMap; pullback-map; module CospanEquivalence)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange using (module ChangeLeftArrow)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-change-left)
open import SCT.VolumeI.Chapter01.Section06.NestedPullbacks using (nested-projection-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.Embeddings
  using (IsEmbedding; embedding-from-projection-isEquiv; embedding-cong;
    equivalence-isEmbedding; module LeftCancellation)
open import SCT.VolumeI.Chapter02.Section03.Isomorphisms using (identityIso; identityIso-arrow)

private
  module _ {Γ : Context} where
    restrict-parameter : {P Q C : CAT Γ} {x y : MAP P C}
      (f : MorphismFamily x y) {r s : MAP Q P} (rho : r =₁ s) →
      MorphismFamilyIdentification One
        (retarget-family (restrict-family f r) (x ◁ rho) (y ◁ rho)) (restrict-family f s)
    restrict-parameter {x = x} {y} f rho = family-comparison _ _ (F.arrow ◁ rho)
      (restrict-change-square-One ev₀ F.arrow x F.source-frame rho)
      (restrict-change-square-One ev₁ F.arrow y F.target-frame rho)
      where module F = MorphismFamily f

    restrict-twice : {P Q R C : CAT Γ} {x y : MAP P C}
      (f : MorphismFamily x y) (r : MAP Q P) (s : MAP R Q) →
      MorphismFamilyIdentification One
        (retarget-family (restrict-family (restrict-family f r) s)
          (comp-assoc s r x) (comp-assoc s r y)) (restrict-family f (r ∘ s))
    restrict-twice f r s = family-comparison _ _ (comp-assoc s r F.arrow)
      (restrict-triangle-assoc ev₀ F.arrow F.source-frame r s)
      (restrict-triangle-assoc ev₁ F.arrow F.target-frame r s)
      where module F = MorphismFamily f

    retarget-id : {P C : CAT Γ} {x y : MAP P C} (f : MorphismFamily x y) →
      MorphismFamilyIdentification One (retarget-family f (id₌ x) (id₌ y)) f
    retarget-id f = family-comparison _ _ (id₌ F.arrow)
      ((comp₌-unitˡ-One F.source-frame) ⁻¹ ∙
        (comp₌-unitʳ-One F.source-frame ∙
          comp₌-cong (id₌ F.source-frame) (postWhisker-id₌ ev₀ F.arrow)))
      ((comp₌-unitˡ-One F.target-frame) ⁻¹ ∙
        (comp₌-unitʳ-One F.target-frame ∙
          comp₌-cong (id₌ F.target-frame) (postWhisker-id₌ ev₁ F.arrow)))
      where module F = MorphismFamily f

    restrict-identity-frame : {P Q U C : CAT Γ}
      (e : MAP U C) (p : MAP P U) (r : MAP Q P) →
      (comp-assoc r p e ∙ restrict-triangle e p (id₌ (e ∘ p)) r) =₂
        id₌ (e ∘ (p ∘ r))
    restrict-identity-frame e p r = comp₌-inverseʳ-One A ∙
      (comp₌-cong (id₌ A) (comp₌-unitˡ-One (A ⁻¹)) ∙
        comp₌-cong (id₌ A) (comp₌-cong (preWhisker-id₌ (e ∘ p) r) (id₌ (A ⁻¹))))
      where A = comp-assoc r p e

  module CompositionSquare {Γ : Context} (C : CAT Γ) (segal : IsEquiv (short-edges C)) where
    square : {P : CAT Γ} {x y z x′ y′ z′ : MAP P C}
      (alpha : MorphismFamily x y) (beta : MorphismFamily y z)
      (alpha′ : MorphismFamily x′ y′) (beta′ : MorphismFamily y′ z′)
      (p : x =₁ x′) (q : y =₁ y′) (r : z =₁ z′) →
      MorphismFamilyIdentification One (retarget-family alpha p q) alpha′ →
      MorphismFamilyIdentification One (retarget-family beta q r) beta′ →
      MorphismFamilyIdentification One
        (retarget-family (MC.Composition.compose C segal beta alpha) p r)
        (MC.Composition.compose C segal beta′ alpha′)
    square alpha beta alpha′ beta′ p q r first second = compose-family-comparisons
      (CompositionComparisons.composition-comparison C segal second first)
      (CompositionTransport.retarget-composition C segal beta alpha p q r)

  module RealizeConeAction {Γ : Context} {A B Z A′ B′ Z′ : CAT Γ}
    {f : MAP A Z} {g : MAP B Z} {f′ : MAP A′ Z′} {g′ : MAP B′ Z′}
    (act : {T : CAT Γ} → Cone f g T → Cone f′ g′ T)
    (compare : {T : CAT Γ} {s t : Cone f g T} → ConeIdentification₁ s t →
      ConeIdentification₁ (act s) (act t))
    (restrict : {T U : CAT Γ} (s : Cone f g T) (r : MAP U T) →
      ConeIdentification₁ (cone-restrict r (act s)) (act (cone-restrict r s))) where
    private
      source-cone = pullback-cone f g
      target-cone = pullback-cone f′ g′

    map : MAP (Pullback f g) (Pullback f′ g′)
    map = pullback-factor (act source-cone)
    universal-computation : ConeIdentification₁ (cone-restrict map target-cone) (act source-cone)
    universal-computation = pullback-factor-β (act source-cone)
    computation : {T : CAT Γ} (s : Cone f g T) →
      ConeIdentification₁ (cone-restrict (map ∘ pullback-factor s) target-cone) (act s)
    computation s = cone-compose (compare (pullback-factor-β s))
      (cone-compose (restrict source-cone (pullback-factor s))
        (cone-compose (cone-identification-restrict-One (pullback-factor s) universal-computation)
          (cone-inverse (cone-restrict-assoc (pullback-factor s) map target-cone))))
```

For postcomposition the input cone is an arrow ending at `x` over its
specified base map. Composition with the restricted family changes that
endpoint to `y`. Comparing cones transports both endpoints of the input
family and the base of the composing family.

```agda
module TargetAction {Γ : Context} {B C : CAT Γ}
  (segal : IsEquiv (short-edges C)) {x y : MAP B C} (f : MorphismFamily x y) where
  private
    module Chosen = MC.Composition C segal

  input : {T : CAT Γ} (t : Cone (ev₁ {C = C}) x T) →
    MorphismFamily (ev₀ ∘ Cone.left t) (x ∘ Cone.right t)
  input t = record
    { arrow = Cone.left t
    ; source-frame = id₌ (ev₀ ∘ Cone.left t)
    ; target-frame = Cone.match t }
  composite : {T : CAT Γ} (t : Cone (ev₁ {C = C}) x T) →
    MorphismFamily (ev₀ ∘ Cone.left t) (y ∘ Cone.right t)
  composite t = Chosen.compose (restrict-family f (Cone.right t)) (input t)
  act : {T : CAT Γ} → Cone (ev₁ {C = C}) x T → Cone (ev₁ {C = C}) y T
  act t = record
    { left = MorphismFamily.arrow (composite t)
    ; right = Cone.right t
    ; match = MorphismFamily.target-frame (composite t) }

  module Compared {T : CAT Γ} {t u : Cone (ev₁ {C = C}) x T} (Phi : ConeIdentification₁ t u) where
    private
      L = ConeIdentification₁.left Phi
      R = ConeIdentification₁.right Phi
      p = ev₀ ◁ L
      q = x ◁ R
      r = y ◁ R
      input-comparison : MorphismFamilyIdentification One (retarget-family (input t) p q) (input u)
      input-comparison = family-comparison _ _ L
        ((comp₌-unitʳ-One p) ⁻¹ ∙ comp₌-unitˡ-One p)
        (ConeIdentification₁.compatible Phi)
      value : MorphismFamilyIdentification One (retarget-family (composite t) p r) (composite u)
      value = CompositionSquare.square C segal (input t) (restrict-family f (Cone.right t))
        (input u) (restrict-family f (Cone.right u)) p q r input-comparison (restrict-parameter f R)
      module Value = FamilyComparison value
    comparison : ConeIdentification₁ (act t) (act u)
    comparison = record { left = Value.identification; right = R; compatible = Value.target }

  module Restriction {T U : CAT Γ} (t : Cone (ev₁ {C = C}) x T) (r : MAP U T) where
    private
      p = Cone.left t
      q = Cone.right t
      source-assoc = comp-assoc r p ev₀
      middle-assoc = comp-assoc r q x
      target-assoc = comp-assoc r q y
      changed = cone-restrict r t
      input-comparison : MorphismFamilyIdentification One
        (retarget-family (restrict-family (input t) r) source-assoc middle-assoc) (input changed)
      input-comparison = family-comparison _ _ (id₌ (p ∘ r))
        ((restrict-identity-frame ev₀ p r) ⁻¹ ∙
          (comp₌-unitˡ-One (id₌ (ev₀ ∘ (p ∘ r))) ∙
            comp₌-cong (id₌ (id₌ (ev₀ ∘ (p ∘ r)))) (postWhisker-id₌ ev₀ (p ∘ r))))
        (comp₌-unitʳ-One (Cone.match changed) ∙
          comp₌-cong (id₌ (Cone.match changed)) (postWhisker-id₌ ev₁ (p ∘ r)))
      output-comparison : MorphismFamilyIdentification One
        (retarget-family (restrict-family (composite t) r) source-assoc target-assoc) (composite changed)
      output-comparison = compose-family-comparisons
        (CompositionSquare.square C segal (restrict-family (input t) r)
          (restrict-family (restrict-family f q) r) (input changed) (restrict-family f (q ∘ r))
          source-assoc middle-assoc target-assoc input-comparison (restrict-twice f q r))
        (retarget-family-comparison source-assoc target-assoc
          (CompositionTransport.restrict-composition C segal (restrict-family f q) (input t) r))
      module Value = FamilyComparison output-comparison
    comparison : ConeIdentification₁ (cone-restrict r (act t)) (act changed)
    comparison = record
      { left = Value.identification
      ; right = id₌ (q ∘ r)
      ; compatible =
          (comp₌-unitˡ-One (Cone.match (cone-restrict r (act t))) ∙
            comp₌-cong (postWhisker-id₌ y (q ∘ r)) (id₌ (Cone.match (cone-restrict r (act t))))) ⁻¹ ∙
          Value.target }

  module Realized = RealizeConeAction act Compared.comparison Restriction.comparison
    using (map; universal-computation; computation)
  open Realized public
```

Precomposition is the dual endpoint construction. Its cone matching is the
source frame, and its unchanged endpoint is the target of the input arrow.

```agda
module SourceAction {Γ : Context} {B C : CAT Γ}
  (segal : IsEquiv (short-edges C)) {x y : MAP B C} (f : MorphismFamily y x) where
  private
    module Chosen = MC.Composition C segal

  input : {T : CAT Γ} (t : Cone (ev₀ {C = C}) x T) →
    MorphismFamily (x ∘ Cone.right t) (ev₁ ∘ Cone.left t)
  input t = record
    { arrow = Cone.left t
    ; source-frame = Cone.match t
    ; target-frame = id₌ (ev₁ ∘ Cone.left t) }
  composite : {T : CAT Γ} (t : Cone (ev₀ {C = C}) x T) →
    MorphismFamily (y ∘ Cone.right t) (ev₁ ∘ Cone.left t)
  composite t = Chosen.compose (input t) (restrict-family f (Cone.right t))
  act : {T : CAT Γ} → Cone (ev₀ {C = C}) x T → Cone (ev₀ {C = C}) y T
  act t = record
    { left = MorphismFamily.arrow (composite t)
    ; right = Cone.right t
    ; match = MorphismFamily.source-frame (composite t) }

  module Compared {T : CAT Γ} {t u : Cone (ev₀ {C = C}) x T} (Phi : ConeIdentification₁ t u) where
    private
      L = ConeIdentification₁.left Phi
      R = ConeIdentification₁.right Phi
      p = y ◁ R
      q = x ◁ R
      r = ev₁ ◁ L
      input-comparison : MorphismFamilyIdentification One (retarget-family (input t) q r) (input u)
      input-comparison = family-comparison _ _ L
        (ConeIdentification₁.compatible Phi)
        ((comp₌-unitʳ-One r) ⁻¹ ∙ comp₌-unitˡ-One r)
      value : MorphismFamilyIdentification One (retarget-family (composite t) p r) (composite u)
      value = CompositionSquare.square C segal (restrict-family f (Cone.right t)) (input t)
        (restrict-family f (Cone.right u)) (input u) p q r (restrict-parameter f R) input-comparison
      module Value = FamilyComparison value
    comparison : ConeIdentification₁ (act t) (act u)
    comparison = record { left = Value.identification; right = R; compatible = Value.source }

  module Restriction {T U : CAT Γ} (t : Cone (ev₀ {C = C}) x T) (r : MAP U T) where
    private
      p = Cone.left t
      q = Cone.right t
      source-assoc = comp-assoc r q y
      middle-assoc = comp-assoc r q x
      target-assoc = comp-assoc r p ev₁
      changed = cone-restrict r t
      input-comparison : MorphismFamilyIdentification One
        (retarget-family (restrict-family (input t) r) middle-assoc target-assoc) (input changed)
      input-comparison = family-comparison _ _ (id₌ (p ∘ r))
        (comp₌-unitʳ-One (Cone.match changed) ∙
          comp₌-cong (id₌ (Cone.match changed)) (postWhisker-id₌ ev₀ (p ∘ r)))
        ((restrict-identity-frame ev₁ p r) ⁻¹ ∙
          (comp₌-unitˡ-One (id₌ (ev₁ ∘ (p ∘ r))) ∙
            comp₌-cong (id₌ (id₌ (ev₁ ∘ (p ∘ r)))) (postWhisker-id₌ ev₁ (p ∘ r))))
      output-comparison : MorphismFamilyIdentification One
        (retarget-family (restrict-family (composite t) r) source-assoc target-assoc) (composite changed)
      output-comparison = compose-family-comparisons
        (CompositionSquare.square C segal (restrict-family (restrict-family f q) r)
          (restrict-family (input t) r) (restrict-family f (q ∘ r)) (input changed)
          source-assoc middle-assoc target-assoc (restrict-twice f q r) input-comparison)
        (retarget-family-comparison source-assoc target-assoc
          (CompositionTransport.restrict-composition C segal (input t) (restrict-family f q) r))
      module Value = FamilyComparison output-comparison
    comparison : ConeIdentification₁ (cone-restrict r (act t)) (act changed)
    comparison = record
      { left = Value.identification
      ; right = id₌ (q ∘ r)
      ; compatible =
          (comp₌-unitˡ-One (Cone.match (cone-restrict r (act t))) ∙
            comp₌-cong (postWhisker-id₌ y (q ∘ r)) (id₌ (Cone.match (cone-restrict r (act t))))) ⁻¹ ∙
          Value.source }

  module Realized = RealizeConeAction act Compared.comparison Restriction.comparison
    using (map; universal-computation; computation)
  open Realized public
```

The cancellation calculation uses the accepted chosen Segal composition,
whose associativity compares complete framed families. Reassociate the
two composing inverse families, restrict their given inverse equation,
and remove the resulting identity. Changing the otherwise unused endpoint
of the intermediate cone input is recorded explicitly.

```agda
module TargetCancellation {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
  (f : MorphismFamily x y) (g : MorphismFamily y x)
  (law : MorphismFamilyIdentification One
    (MC.Composition.compose C (segal-isEquiv C) g f) (identity-family x)) where
  private
    module Chosen = MC.Composition C (segal-isEquiv C)
    module F = TargetAction (segal-isEquiv C) f using (act; input; composite)
    module G = TargetAction (segal-isEquiv C) g using (act; input; composite)

  module At {T : CAT Γ} (t : Cone (ev₁ {C = C}) x T) where
    private
      q = Cone.right t
      u = F.input t
      fq = restrict-family f q
      gq = restrict-family g q
      fg = F.composite t
      module FG = MorphismFamily fg
      w = G.composite (F.act t)
      input-comparison : MorphismFamilyIdentification One
        (retarget-family (G.input (F.act t)) FG.source-frame (id₌ (y ∘ q))) fg
      input-comparison = family-comparison _ _ (id₌ FG.arrow)
        (comp₌-cong (id₌ FG.source-frame) (postWhisker-id₌ ev₀ FG.arrow))
        ((comp₌-unitˡ-One FG.target-frame) ⁻¹ ∙
          (comp₌-unitʳ-One FG.target-frame ∙
            comp₌-cong (id₌ FG.target-frame) (postWhisker-id₌ ev₁ FG.arrow)))
      first : MorphismFamilyIdentification One
        (retarget-family w FG.source-frame (id₌ (x ∘ q))) (Chosen.compose gq fg)
      first = CompositionSquare.square C (segal-isEquiv C)
        (G.input (F.act t)) gq fg gq
        FG.source-frame (id₌ (y ∘ q)) (id₌ (x ∘ q)) input-comparison (retarget-id gq)
      restricted-law : MorphismFamilyIdentification One (Chosen.compose gq fq) (identity-family (x ∘ q))
      restricted-law = compose-family-comparisons (IdentityFamilyRestriction.value x q)
        (compose-family-comparisons (restrict-family-comparison q law)
          (inverse-family-comparison (CompositionTransport.restrict-composition C (segal-isEquiv C) g f q)))
      reassociate : MorphismFamilyIdentification One
        (Chosen.compose gq fg) (Chosen.compose (Chosen.compose gq fq) u)
      reassociate = associativity u fq gq
      cancel : MorphismFamilyIdentification One (Chosen.compose (Chosen.compose gq fq) u) u
      cancel = compose-family-comparisons (MorphismCompositionUnits.target-unit C (segal-isEquiv C) u)
        (CompositionComparisons.composition-comparison C (segal-isEquiv C)
          restricted-law (id-family-comparison u))
      value : MorphismFamilyIdentification One
        (retarget-family w FG.source-frame (id₌ (x ∘ q))) u
      value = compose-family-comparisons cancel (compose-family-comparisons reassociate first)
      module Value = FamilyComparison value
    comparison : ConeIdentification₁ (G.act (F.act t)) t
    comparison = record
      { left = Value.identification
      ; right = id₌ q
      ; compatible = comp₌-cong ((postWhisker-id₌ x q) ⁻¹)
          (id₌ (MorphismFamily.target-frame w)) ∙ Value.target }

  inverse-law : {T : CAT Γ} (t : Cone (ev₁ {C = C}) x T) →
    ConeIdentification₁ (G.act (F.act t)) t
  inverse-law = At.comparison

module SourceCancellation {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
  (f : MorphismFamily y x) (g : MorphismFamily x y)
  (law : MorphismFamilyIdentification One
    (MC.Composition.compose C (segal-isEquiv C) f g) (identity-family x)) where
  private
    module Chosen = MC.Composition C (segal-isEquiv C)
    module F = SourceAction (segal-isEquiv C) f using (act; input; composite)
    module G = SourceAction (segal-isEquiv C) g using (act; input; composite)

  module At {T : CAT Γ} (t : Cone (ev₀ {C = C}) x T) where
    private
      q = Cone.right t
      u = F.input t
      fq = restrict-family f q
      gq = restrict-family g q
      fg = F.composite t
      module FG = MorphismFamily fg
      w = G.composite (F.act t)
      input-comparison : MorphismFamilyIdentification One
        (retarget-family (G.input (F.act t)) (id₌ (y ∘ q)) FG.target-frame) fg
      input-comparison = family-comparison _ _ (id₌ FG.arrow)
        ((comp₌-unitˡ-One FG.source-frame) ⁻¹ ∙
          (comp₌-unitʳ-One FG.source-frame ∙
            comp₌-cong (id₌ FG.source-frame) (postWhisker-id₌ ev₀ FG.arrow)))
        (comp₌-cong (id₌ FG.target-frame) (postWhisker-id₌ ev₁ FG.arrow))
      first : MorphismFamilyIdentification One
        (retarget-family w (id₌ (x ∘ q)) FG.target-frame) (Chosen.compose fg gq)
      first = CompositionSquare.square C (segal-isEquiv C)
        gq (G.input (F.act t)) gq fg
        (id₌ (x ∘ q)) (id₌ (y ∘ q)) FG.target-frame (retarget-id gq) input-comparison
      restricted-law : MorphismFamilyIdentification One (Chosen.compose fq gq) (identity-family (x ∘ q))
      restricted-law = compose-family-comparisons (IdentityFamilyRestriction.value x q)
        (compose-family-comparisons (restrict-family-comparison q law)
          (inverse-family-comparison (CompositionTransport.restrict-composition C (segal-isEquiv C) f g q)))
      reassociate : MorphismFamilyIdentification One
        (Chosen.compose fg gq) (Chosen.compose u (Chosen.compose fq gq))
      reassociate = inverse-family-comparison (associativity gq fq u)
      cancel : MorphismFamilyIdentification One (Chosen.compose u (Chosen.compose fq gq)) u
      cancel = compose-family-comparisons (MorphismCompositionUnits.source-unit C (segal-isEquiv C) u)
        (CompositionComparisons.composition-comparison C (segal-isEquiv C)
          (id-family-comparison u) restricted-law)
      value : MorphismFamilyIdentification One
        (retarget-family w (id₌ (x ∘ q)) FG.target-frame) u
      value = compose-family-comparisons cancel (compose-family-comparisons reassociate first)
      module Value = FamilyComparison value
    comparison : ConeIdentification₁ (G.act (F.act t)) t
    comparison = record
      { left = Value.identification
      ; right = id₌ q
      ; compatible = comp₌-cong ((postWhisker-id₌ x q) ⁻¹)
          (id₌ (MorphismFamily.source-frame w)) ∙ Value.source }

  inverse-law : {T : CAT Γ} (t : Cone (ev₀ {C = C}) x T) →
    ConeIdentification₁ (G.act (F.act t)) t
  inverse-law = At.comparison
```

Each full cone cancellation law recovers the inverse comparison of the
realized maps. The two different inverse families then give the section
and retraction of either composition action.

```agda
private
  module TargetInverseMap {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
    (f : MorphismFamily x y) (g : MorphismFamily y x)
    (law : MorphismFamilyIdentification One
      (MC.Composition.compose C (segal-isEquiv C) g f) (identity-family x)) where
    private
      module F = TargetAction (segal-isEquiv C) f using (map; act)
      module G = TargetAction (segal-isEquiv C) g using (map; computation)
      source-cone = pullback-cone (ev₁ {C = C}) x
    comparison : (G.map ∘ F.map) =₁ id (Pullback (ev₁ {C = C}) x)
    comparison = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id source-cone))
        (cone-compose (TargetCancellation.inverse-law f g law source-cone)
          (G.computation (F.act source-cone))))

  module SourceInverseMap {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
    (f : MorphismFamily y x) (g : MorphismFamily x y)
    (law : MorphismFamilyIdentification One
      (MC.Composition.compose C (segal-isEquiv C) f g) (identity-family x)) where
    private
      module F = SourceAction (segal-isEquiv C) f using (map; act)
      module G = SourceAction (segal-isEquiv C) g using (map; computation)
      source-cone = pullback-cone (ev₀ {C = C}) x
    comparison : (G.map ∘ F.map) =₁ id (Pullback (ev₀ {C = C}) x)
    comparison = pullback-reflect _ _
      (cone-compose (cone-inverse (cone-restrict-id source-cone))
        (cone-compose (SourceCancellation.inverse-law f g law source-cone)
          (G.computation (F.act source-cone))))

module CompositionEquivalences {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
  (f : MorphismFamily x y) (witness : InverseFamily (segal-isEquiv C) f) where
  private
    module W = InverseFamily witness

  postcomposition-isEquiv : IsEquiv (TargetAction.map (segal-isEquiv C) f)
  postcomposition-isEquiv = section-retraction-isEquiv
    (record
      { section = TargetAction.map (segal-isEquiv C) W.right-inverse
      ; section-law = (TargetInverseMap.comparison W.right-inverse f W.right-law) ⁻¹ })
    (record
      { retraction = TargetAction.map (segal-isEquiv C) W.left-inverse
      ; retraction-law = (TargetInverseMap.comparison f W.left-inverse W.left-law) ⁻¹ })

  precomposition-isEquiv : IsEquiv (SourceAction.map (segal-isEquiv C) f)
  precomposition-isEquiv = section-retraction-isEquiv
    (record
      { section = SourceAction.map (segal-isEquiv C) W.left-inverse
      ; section-law = (SourceInverseMap.comparison W.left-inverse f W.left-law) ⁻¹ })
    (record
      { retraction = SourceAction.map (segal-isEquiv C) W.right-inverse
      ; retraction-law = (SourceInverseMap.comparison f W.right-inverse W.right-law) ⁻¹ })
```

A full computation rule transports universality along an equivalence of
the representing pullbacks. This uses the actual factor restriction law,
so the matching of the supplied universal cone remains part of the argument.

```agda
private
  module _ {Γ : Context} where
    restrict-universal-cone : {A B Z S T : CAT Γ} {f : MAP A Z} {g : MAP B Z}
      (s : Cone f g S) → IsPullback s → (r : MAP T S) → IsEquiv r →
      IsPullback (cone-restrict r s)
    restrict-universal-cone s es r er = equiv-transport
      ((pullback-factor-restrict r s) ⁻¹) (equiv-compose r (pullback-factor s) er es)

module TargetUniversalAction {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
  (f : MorphismFamily x y) (witness : InverseFamily (segal-isEquiv C) f) where
  private
    module Action = TargetAction (segal-isEquiv C) f using (map; act; computation)
    map-isEquiv = CompositionEquivalences.postcomposition-isEquiv f witness
  preserves-pullback : {T : CAT Γ} (s : Cone (ev₁ {C = C}) x T) →
    IsPullback s → IsPullback (Action.act s)
  preserves-pullback s es = isPullback-cone-identification (Action.computation s)
    (restrict-universal-cone (pullback-cone ev₁ y) (pullback-cone-isPullback ev₁ y)
      (Action.map ∘ pullback-factor s)
      (equiv-compose (pullback-factor s) Action.map es map-isEquiv))

module SourceUniversalAction {Γ : Context} {B C : CAT Γ} {x y : MAP B C}
  (f : MorphismFamily x y) (witness : InverseFamily (segal-isEquiv C) f) where
  private
    module Action = SourceAction (segal-isEquiv C) f using (map; act; computation)
    map-isEquiv = CompositionEquivalences.precomposition-isEquiv f witness
  preserves-pullback : {T : CAT Γ} (s : Cone (ev₀ {C = C}) y T) →
    IsPullback s → IsPullback (Action.act s)
  preserves-pullback s es = isPullback-cone-identification (Action.computation s)
    (restrict-universal-cone (pullback-cone ev₀ x) (pullback-cone-isPullback ev₀ x)
      (Action.map ∘ pullback-factor s)
      (equiv-compose (pullback-factor s) Action.map es map-isEquiv))
```

Fixing the second short edge of a triangle leaves an arrow ending at the
source of that edge. Segal and pullback pasting make this a universal
endpoint cone. The complete triangle presentation compares its long edge
with postcomposition by the fixed arrow.

```agda
module RightTriangleAction {Γ : Context} {B C : CAT Γ} (f : MAP B (Ar C)) where
  arrow : MorphismFamily (ev₀ ∘ f) (ev₁ ∘ f)
  arrow = record
    { arrow = f; source-frame = id₌ (ev₀ ∘ f); target-frame = id₌ (ev₁ ∘ f) }
  T : CAT Γ
  T = Pullback f (edge₀ {C = C})
  triangle : MAP T (Triangles C)
  triangle = pullback₂
  base : MAP T B
  base = pullback₁
  private
    raw : Cone f (edge₀ {C = C}) T
    raw = pullback-cone f edge₀
    swapped-segal = cone-swap (triangle-cone C)
    module Paste = Pasting f ev₀ ev₁ swapped-segal
      (SwappedCone.isPullback (triangle-cone C) (segal-isEquiv C))
    outer = Paste.Paste.paste raw

  input-cone : Cone (ev₁ {C = C}) (ev₀ ∘ f) T
  input-cone = cone-swap outer
  input-isPullback : IsPullback input-cone
  input-isPullback = SwappedCone.isPullback outer
    (Paste.paste-isPullback raw (pullback-cone-isPullback f edge₀))

  private
    module Action = TargetAction (segal-isEquiv C) arrow using (input; composite; act)
    first = Action.input input-cone
    second = restrict-family arrow base
    pair-cone = MC.ComposableFamilies.cone first second
    u = comp-assoc base f ev₀
    n = Cone.match outer
    raw-pair = cone-swap (postcompose-cone-left f ev₀ outer)
    normalized-pair : Cone.match raw-pair =₂ Cone.match pair-cone
    normalized-pair = comp₌-cong
      (inv₌ ◁ ((comp₌-unitˡ-One (u ⁻¹) ∙
        comp₌-cong (preWhisker-id₌ (ev₀ ∘ f) base) (id₌ (u ⁻¹))) ⁻¹))
      (id₌ (n ⁻¹)) ∙ inverse-composite n (u ⁻¹)
    pair-comparison : ConeIdentification₁ raw-pair pair-cone
    pair-comparison = cone-retarget-match-identification raw-pair (Cone.match pair-cone) normalized-pair
    short : ConeIdentification₁ (cone-restrict triangle (triangle-cone C)) pair-cone
    short = cone-compose pair-comparison
      (cone-compose (cone-inverse (cone-swap-identification (Paste.Paste.postcompose-paste raw)))
        (cone-compose (cone-inverse (cone-swap-identification (cone-swap-restrict triangle (triangle-cone C))))
          (cone-inverse (cone-swap-twice (cone-restrict triangle (triangle-cone C))))))
    module Completed = CompleteTriangle first second triangle short using (long-family; presentation)
    long-comparison : MorphismFamilyIdentification One (Action.composite input-cone) Completed.long-family
    long-comparison = presented-composition (segal-isEquiv C) first second Completed.long-family Completed.presentation
    module Long = FamilyComparison long-comparison

  long-cone : Cone (ev₁ {C = C}) (ev₁ ∘ f) T
  long-cone = record
    { left = edge₁ ∘ triangle; right = base
    ; match = MorphismFamily.target-frame Completed.long-family }

  private
    long-cone-comparison : ConeIdentification₁ (Action.act input-cone) long-cone
    long-cone-comparison = record
      { left = Long.identification; right = id₌ base
      ; compatible =
          (comp₌-unitˡ-One (Cone.match (Action.act input-cone)) ∙
            comp₌-cong (postWhisker-id₌ (ev₁ ∘ f) base) (id₌ (Cone.match (Action.act input-cone)))) ⁻¹ ∙
          Long.target }

  long-isPullback : InverseFamily (segal-isEquiv C) arrow → IsPullback long-cone
  long-isPullback witness = isPullback-cone-identification long-cone-comparison
    (TargetUniversalAction.preserves-pullback arrow witness input-cone input-isPullback)
```

Fixing the first short edge gives the dual universal cone. Its long edge
is compared with precomposition, including the source matching.

```agda
module LeftTriangleAction {Γ : Context} {B C : CAT Γ} (f : MAP B (Ar C)) where
  arrow : MorphismFamily (ev₀ ∘ f) (ev₁ ∘ f)
  arrow = record
    { arrow = f; source-frame = id₌ (ev₀ ∘ f); target-frame = id₌ (ev₁ ∘ f) }
  T : CAT Γ
  T = Pullback f (edge₂ {C = C})
  triangle : MAP T (Triangles C)
  triangle = pullback₂
  base : MAP T B
  base = pullback₁
  private
    raw : Cone f (edge₂ {C = C}) T
    raw = pullback-cone f edge₂
    module Paste = Pasting f ev₁ ev₀ (triangle-cone C) (segal-isEquiv C)
    outer = Paste.Paste.paste raw

  input-cone : Cone (ev₀ {C = C}) (ev₁ ∘ f) T
  input-cone = cone-swap outer
  input-isPullback : IsPullback input-cone
  input-isPullback = SwappedCone.isPullback outer
    (Paste.paste-isPullback raw (pullback-cone-isPullback f edge₂))

  private
    module Action = SourceAction (segal-isEquiv C) arrow using (input; composite; act)
    first = restrict-family arrow base
    second = Action.input input-cone
    pair-cone = MC.ComposableFamilies.cone first second
    u = comp-assoc base f ev₁
    n = Cone.match outer
    raw-pair = postcompose-cone-left f ev₁ outer
    normalized-pair : Cone.match raw-pair =₂ Cone.match pair-cone
    normalized-pair = comp₌-cong ((inverse-inverse n) ⁻¹)
      ((comp₌-unitˡ-One (u ⁻¹) ∙
        comp₌-cong (preWhisker-id₌ (ev₁ ∘ f) base) (id₌ (u ⁻¹))) ⁻¹)
    pair-comparison : ConeIdentification₁ raw-pair pair-cone
    pair-comparison = cone-retarget-match-identification raw-pair (Cone.match pair-cone) normalized-pair
    short : ConeIdentification₁ (cone-restrict triangle (triangle-cone C)) pair-cone
    short = cone-compose pair-comparison (cone-inverse (Paste.Paste.postcompose-paste raw))
    module Completed = CompleteTriangle first second triangle short using (long-family; presentation)
    long-comparison : MorphismFamilyIdentification One (Action.composite input-cone) Completed.long-family
    long-comparison = presented-composition (segal-isEquiv C) first second Completed.long-family Completed.presentation
    module Long = FamilyComparison long-comparison

  long-cone : Cone (ev₀ {C = C}) (ev₀ ∘ f) T
  long-cone = record
    { left = edge₁ ∘ triangle; right = base
    ; match = MorphismFamily.source-frame Completed.long-family }

  private
    long-cone-comparison : ConeIdentification₁ (Action.act input-cone) long-cone
    long-cone-comparison = record
      { left = Long.identification; right = id₌ base
      ; compatible =
          (comp₌-unitˡ-One (Cone.match (Action.act input-cone)) ∙
            comp₌-cong (postWhisker-id₌ (ev₀ ∘ f) base) (id₌ (Cone.match (Action.act input-cone)))) ⁻¹ ∙
          Long.source }

  long-isPullback : InverseFamily (segal-isEquiv C) arrow → IsPullback long-cone
  long-isPullback witness = isPullback-cone-identification long-cone-comparison
    (SourceUniversalAction.preserves-pullback arrow witness input-cone input-isPullback)
```

Imposing a constant long edge leaves an equivalence to the base: paste its
pullback with the universal long-edge cone, then evaluate the identity
arrow at its endpoint. Reordering the two pullbacks identifies this with
the actual category of one-sided inverse triangles over the fixed arrow.

```agda
private
  module ConstantLongEdgeFiber {Γ : Context} {B C E T : CAT Γ}
    (endpoint : MAP E C) (constant : MAP C E)
    (epsilon : (endpoint ∘ constant) =₁ id C) {b : MAP B C}
    (t : Cone endpoint b T) (et : IsPullback t) where
    private
      h = Cone.left t
      inner = cone-swap (pullback-cone h constant)
      module Paste = Pasting constant endpoint b t et
      outer = Paste.Paste.paste inner
    projection-isEquiv : IsEquiv (Cone.right t ∘ pullback₁ {f = h} {g = constant})
    projection-isEquiv = left-isEquiv-from-isPullback
      (equiv-transport (epsilon ⁻¹) (id-isEquiv C)) (cone-swap outer)
      (SwappedCone.isPullback outer
        (Paste.paste-isPullback inner
          (SwappedCone.isPullback (pullback-cone h constant) (pullback-cone-isPullback h constant))))

  module TwoStageFibers {Γ : Context} {B A T E D : CAT Γ}
    (f : MAP B A) (g : MAP T A) (h : MAP T E) (s : MAP D E) where
    private
      Raw = Pullback f g
      J = Pullback h s
      triangle : MAP Raw T
      triangle = pullback₂
      base : MAP Raw B
      base = pullback₁
      forget : MAP J T
      forget = pullback₁
      Fiber = Pullback (h ∘ triangle) s
      one-sided = g ∘ forget
      module First = ChosenNested triangle h s
      module Last = Nested forget g f (cone-swap (pullback-cone f g))
        (SwappedCone.isPullback (pullback-cone f g) (pullback-cone-isPullback f g))
      swap-pullback = pullback-swap triangle forget
      middle : MAP Fiber (Pullback forget triangle)
      middle = swap-pullback ∘ First.insert
      last-base : MAP (Pullback forget triangle) Raw
      last-base = pullback₂

    comparison : MAP Fiber (Pullback one-sided f)
    comparison = Last.flatten ∘ middle
    comparison-isEquiv : IsEquiv comparison
    comparison-isEquiv = equiv-compose middle Last.flatten
      (equiv-compose First.insert swap-pullback First.insert-isEquiv (pullback-swap-isEquiv triangle forget))
      Last.flatten-isEquiv
    private
      middle-base : (last-base ∘ middle) =₁ (pullback₁ {f = h ∘ triangle} {g = s})
      middle-base = First.insert-left ∙
        ((pullback-factor-β₂ (cone-swap (pullback-cone triangle forget)) ▷ First.insert) ∙
          (comp-assoc First.insert swap-pullback last-base) ⁻¹)
    base-comparison : (pullback₂ ∘ comparison) =₁ (base ∘ pullback₁ {f = h ∘ triangle} {g = s})
    base-comparison = (base ◁ middle-base) ∙
      (comp-assoc middle last-base base ∙
        ((pullback-factor-β₂ Last.flat-cone ▷ middle) ∙ (comp-assoc middle Last.flatten pullback₂) ⁻¹))
    projection-isEquiv : IsEquiv (base ∘ pullback₁ {f = h ∘ triangle} {g = s}) →
      IsEquiv (pullback₂ {f = one-sided} {g = f})
    projection-isEquiv e = equiv-cancel-right comparison pullback₂ comparison-isEquiv
      (equiv-transport (base-comparison ⁻¹) e)

module _ {Γ : Context} where
  InverseTriangle : CAT Γ → CAT Γ
  InverseTriangle C = Pullback (edge₁ {C = C}) identityArrow
  rightInverseArrow leftInverseArrow : {C : CAT Γ} → MAP (InverseTriangle C) (Ar C)
  rightInverseArrow = edge₀ ∘ pullback₁
  leftInverseArrow = edge₂ ∘ pullback₁

module OneSidedInverseFibers {Γ : Context} {B C : CAT Γ} (f : MAP B (Ar C)) where
  private
    module Right = RightTriangleAction f using (arrow; long-cone; long-isPullback)
    module Left = LeftTriangleAction f using (arrow; long-cone; long-isPullback)
    module RightOrder = TwoStageFibers f edge₀ edge₁ identityArrow using (projection-isEquiv)
    module LeftOrder = TwoStageFibers f edge₂ edge₁ identityArrow using (projection-isEquiv)
  right-projection-isEquiv : InverseFamily (segal-isEquiv C) Right.arrow →
    IsEquiv (pullback₂ {f = rightInverseArrow} {g = f})
  right-projection-isEquiv witness = RightOrder.projection-isEquiv
    (ConstantLongEdgeFiber.projection-isEquiv ev₁ identityArrow identity-target
      Right.long-cone (Right.long-isPullback witness))
  left-projection-isEquiv : InverseFamily (segal-isEquiv C) Left.arrow →
    IsEquiv (pullback₂ {f = leftInverseArrow} {g = f})
  left-projection-isEquiv witness = LeftOrder.projection-isEquiv
    (ConstantLongEdgeFiber.projection-isEquiv ev₀ identityArrow identity-source
      Left.long-cone (Left.long-isPullback witness))

module UniversalInverseFibers {Γ : Context} (C : CAT Γ) where
  right-projection-isEquiv : IsEquiv (pullback₂ {f = rightInverseArrow} {g = isoArrow C})
  right-projection-isEquiv = OneSidedInverseFibers.right-projection-isEquiv (isoArrow C)
    (iso-inverse-family C (segal-isEquiv C))
  left-projection-isEquiv : IsEquiv (pullback₂ {f = leftInverseArrow} {g = isoArrow C})
  left-projection-isEquiv = OneSidedInverseFibers.left-projection-isEquiv (isoArrow C)
    (iso-inverse-family C (segal-isEquiv C))
```

The product of the two long-edge pullbacks imposes the inverse conditions
separately. Normalize the original object pair by its actual center swap,
then interchange the two pullback stages using the existing nested and
diagonal comparisons. Each stage retains its full selected cone beta.
The final projection comparison identifies the resulting common arrow
with the literal `isoArrow`.

```agda
private
  module _ {Γ : Context} {W X Y Z : CAT Γ} where
    projection-after : (h : MAP X Y) (pi : MAP Y Z) {p : MAP X Z} →
      (pi ∘ h) =₁ p → (k : MAP W X) → (pi ∘ (h ∘ k)) =₁ (p ∘ k)
    projection-after h pi beta k = (beta ▷ k) ∙ (comp-assoc k h pi) ⁻¹

module InverseComparison {Γ : Context} (C : CAT Γ) where
  private
    T : CAT Γ
    T = Triangles C
    H : CAT Γ
    H = Ar C
    A : CAT Γ
    A = InverseTriangles C
    J : CAT Γ
    J = InverseTriangle C
    forget : MAP J T
    forget = pullback₁
    r l : MAP J H
    r = rightInverseArrow
    l = leftInverseArrow
    a-pair : MAP A (T × T)
    a-pair = pair (firstInverseTriangle C) (secondInverseTriangle C)
    u : MAP (J × J) (T × T)
    u = productMap forget forget
    long : MAP (T × T) (H × H)
    long = productMap (edge₁ {C = C}) edge₁
    identities : MAP (C × C) (H × H)
    identities = productMap (identityArrow {C = C}) identityArrow
    short : MAP (T × T) (H × H)
    short = productMap (edge₀ {C = C}) edge₂
    diagonal : MAP H (H × H)
    diagonal = pair (id H) (id H)
    normalization : CospanMap (inverseLongEdges C) (inverseIdentityEdges C) (long ∘ a-pair) identities
    normalization = record
      { left = id A; right = swap {C = C} {D = C}; base = id (H × H)
      ; left-square = (comp-unitˡ (inverseLongEdges C)) ⁻¹ ∙
          (productMap-pair edge₁ edge₁ (firstInverseTriangle C) (secondInverseTriangle C) ∙
            comp-unitʳ (long ∘ a-pair))
      ; right-square = (comp-unitˡ (inverseIdentityEdges C)) ⁻¹ ∙
          productMap-pair identityArrow identityArrow pr₂ pr₁ }
    normalized : MAP (Iso C) (Pullback (long ∘ a-pair) identities)
    normalized = pullback-map normalization
    normalization-isEquiv : IsEquiv normalized
    normalization-isEquiv = CospanEquivalence.pullback-map-isEquiv normalization
      (id-isEquiv A) (swap-isEquiv C C) (id-isEquiv (H × H))
    module LongProduct = Product (pullback-cone (edge₁ {C = C}) identityArrow)
      (pullback-cone (edge₁ {C = C}) identityArrow) using (square; square-isPullback)
    module LongOrder = Nested a-pair long identities LongProduct.square
      (LongProduct.square-isPullback (pullback-cone-isPullback edge₁ identityArrow)
        (pullback-cone-isPullback edge₁ identityArrow))
      using (insert; insert-isEquiv; insertion-cone; nested-cone)
    module ShortDiagonal = DiagonalPullback (edge₀ {C = C}) edge₂ using (module Universal)
    module ShortSquare = ShortDiagonal.Universal (pullback-cone (edge₀ {C = C}) edge₂)
      (pullback-cone-isPullback edge₀ edge₂) using (direct; isPullback)
    module ShortOrder = Nested u short diagonal ShortSquare.direct ShortSquare.isPullback
      using (flatten; flatten-isEquiv; flat-cone)
    module ShortChange = ChangeLeftArrow (productMap-comp forget edge₀ forget edge₂) diagonal
      using (forward; forward-isEquiv)
    module ResultDiagonal = DiagonalPullback r l using (forward; forward-isEquiv; forward-left)
    long-triangles : MAP (Pullback a-pair u) A
    long-triangles = pullback₁
    long-witnesses : MAP (Pullback a-pair u) (J × J)
    long-witnesses = pullback₂
    first-stage : MAP (Iso C) (Pullback a-pair u)
    first-stage = LongOrder.insert ∘ normalized
    second-stage : MAP (Iso C) (Pullback u a-pair)
    second-stage = pullback-swap a-pair u ∘ first-stage
    third-stage : MAP (Iso C) (Pullback (short ∘ u) diagonal)
    third-stage = ShortOrder.flatten ∘ second-stage
    diagonal-stage : MAP (Iso C) (Pullback (productMap r l) diagonal)
    diagonal-stage = ShortChange.forward ∘ third-stage
    first-stage-isEquiv : IsEquiv first-stage
    first-stage-isEquiv = equiv-compose normalized LongOrder.insert normalization-isEquiv LongOrder.insert-isEquiv
    second-stage-isEquiv : IsEquiv second-stage
    second-stage-isEquiv = equiv-compose first-stage (pullback-swap a-pair u)
      first-stage-isEquiv (pullback-swap-isEquiv a-pair u)
    third-stage-isEquiv : IsEquiv third-stage
    third-stage-isEquiv = equiv-compose second-stage ShortOrder.flatten second-stage-isEquiv ShortOrder.flatten-isEquiv
    diagonal-stage-isEquiv : IsEquiv diagonal-stage
    diagonal-stage-isEquiv = equiv-compose third-stage ShortChange.forward third-stage-isEquiv ShortChange.forward-isEquiv
    chosen : Fact.Factorization ResultDiagonal.forward diagonal-stage
    chosen = Fact.factor-through-equiv ResultDiagonal.forward-isEquiv diagonal-stage

  comparison : MAP (Iso C) (Pullback r l)
  comparison = Fact.factor chosen
  comparison-isEquiv : IsEquiv comparison
  comparison-isEquiv = equiv-cancel-left comparison ResultDiagonal.forward ResultDiagonal.forward-isEquiv
    (equiv-transport ((Fact.triangle chosen) ⁻¹) diagonal-stage-isEquiv)
  square : Cone r l (Iso C)
  square = cone-restrict comparison (pullback-cone r l)
  square-isPullback : IsPullback square
  square-isPullback = restrict-universal-cone (pullback-cone r l) (pullback-cone-isPullback r l)
    comparison comparison-isEquiv

  private
    pair-witnesses : (pair (pullback₁ {f = r} {g = l}) pullback₂ ∘ comparison) =₁
      (long-witnesses ∘ first-stage)
    pair-witnesses = projection-after (pullback-swap a-pair u) pullback₁
      (pullback-factor-β₁ (cone-swap (pullback-cone a-pair u))) first-stage ∙
      (projection-after ShortOrder.flatten pullback₁ (pullback-factor-β₁ ShortOrder.flat-cone) second-stage ∙
        (projection-after ShortChange.forward pullback₁
          (pullback-factor-β₁ (cone-change-left (productMap-comp forget edge₀ forget edge₂)
            (pullback-cone (short ∘ u) diagonal))) third-stage ∙
          ((pullback₁ ◁ Fact.triangle chosen) ∙
            (projection-after ResultDiagonal.forward pullback₁ ResultDiagonal.forward-left comparison) ⁻¹)))
    original-triangles : (long-triangles ∘ first-stage) =₁ isoTriangles C
    original-triangles = comp-unitˡ (isoTriangles C) ∙
      (pullback-factor-β₁ (CospanMap.map-cone normalization
        (pullback-cone (inverseLongEdges C) (inverseIdentityEdges C))) ∙
        projection-after LongOrder.insert long-triangles
          (pullback-factor-β₁ LongOrder.insertion-cone) normalized)
    forget-witnesses : (u ∘ (pair (pullback₁ {f = r} {g = l}) pullback₂ ∘ comparison)) =₁
      (a-pair ∘ isoTriangles C)
    forget-witnesses = (a-pair ◁ original-triangles) ∙
      (comp-assoc first-stage long-triangles a-pair ∙
        ((Cone.match LongOrder.nested-cone ⁻¹ ▷ first-stage) ∙
          ((comp-assoc first-stage long-witnesses u) ⁻¹ ∙ (u ◁ pair-witnesses))))
    first-triangle : (forget ∘ (pullback₁ ∘ comparison)) =₁
      (firstInverseTriangle C ∘ isoTriangles C)
    first-triangle = project-pair₁ (firstInverseTriangle C) (secondInverseTriangle C) (isoTriangles C) ∙
      ((pr₁ ◁ forget-witnesses) ∙ before ⁻¹)
      where
      before = (forget ◁ project-pair₁ (pullback₁ {f = r} {g = l}) pullback₂ comparison) ∙
        (comp-assoc (pair (pullback₁ {f = r} {g = l}) pullback₂ ∘ comparison) pr₁ forget ∙
          project-pair₁ (forget ∘ pr₁) (forget ∘ pr₂)
            (pair (pullback₁ {f = r} {g = l}) pullback₂ ∘ comparison))

  comparison-arrow : (r ∘ Cone.left square) =₁ isoArrow C
  comparison-arrow = UniversalIsoFamily.right-short C ∙
    ((edge₀ ◁ first-triangle) ∙ comp-assoc (pullback₁ ∘ comparison) forget edge₀)
```

Uniqueness of either one-sided inverse over the common arrow implies
uniqueness of their combined witness. The nested-pullback argument below
proves that the self-pullback projection is an equivalence. Applying it
to the actual separated Iso cone proves the embedding without Rezk.

```agda
private
  module _ {Γ : Context} where
    swap-projection : {A B E : CAT Γ} (f : MAP A E) (g : MAP B E) →
      IsEquiv (pullback₂ {f = f} {g = g}) → IsEquiv (pullback₁ {f = g} {g = f})
    swap-projection f g e = equiv-cancel-right (pullback-swap f g) pullback₁
      (pullback-swap-isEquiv f g)
      (equiv-transport ((pullback-factor-β₁ (cone-swap (pullback-cone f g))) ⁻¹) e)

    change-right-projection : {A B E : CAT Γ} (f : MAP A E) {g h : MAP B E} →
      g =₁ h → IsEquiv (pullback₂ {f = f} {g = h}) → IsEquiv (pullback₂ {f = f} {g = g})
    change-right-projection f {g} {h} alpha e = equiv-cancel-right (pullback-swap g f) pullback₂
      (pullback-swap-isEquiv g f)
      (equiv-transport ((pullback-factor-β₂ (cone-swap (pullback-cone g f))) ⁻¹)
        (equiv-transport (pullback-factor-β₁ (cone-change-left alpha (pullback-cone g f)))
          (equiv-compose Change.forward pullback₁ Change.forward-isEquiv (swap-projection f h e))))
      where module Change = ChangeLeftArrow alpha f using (forward; forward-isEquiv)

  module IntersectionEmbedding {Γ : Context} {R L A I : CAT Γ}
    (r : MAP R A) (l : MAP L A) (s : Cone r l I) (es : IsPullback s) where
    private
      p : MAP I R
      p = Cone.left s
      i : MAP I A
      i = r ∘ p
      K : CAT Γ
      K = Pullback r i
      u : MAP K R
      u = pullback₁
      v : MAP K I
      v = pullback₂
      module Boundary = ChangeLeftArrow (pullback-match {f = r} {g = i}) l
        using (forward; forward-isEquiv)
      module Inner = Nested u r l s es using (flat-cone; flatten; flatten-isEquiv)
      module Outer = ChosenNested p r i using (flat-cone; flatten; flatten-isEquiv)
    embedding : IsEquiv (pullback₂ {f = r} {g = i}) →
      IsEquiv (pullback₂ {f = l} {g = i}) → IsEmbedding i
    embedding er el = embedding-from-projection-isEquiv i (swap-projection i i self-second)
      where
      other-first : IsEquiv (pullback₁ {f = i} {g = l})
      other-first = swap-projection l i el
      restricted-first : IsEquiv (pullback₁ {f = i ∘ v} {g = l})
      restricted-first = nested-projection-isEquiv v i l other-first
      changed-first : IsEquiv (pullback₁ {f = r ∘ u} {g = l})
      changed-first = equiv-transport
        (pullback-factor-β₁ (cone-change-left (pullback-match {f = r} {g = i})
          (pullback-cone (r ∘ u) l)))
        (equiv-compose Boundary.forward pullback₁ Boundary.forward-isEquiv restricted-first)
      inner-first : IsEquiv (pullback₁ {f = u} {g = p})
      inner-first = equiv-transport (pullback-factor-β₁ Inner.flat-cone)
        (equiv-compose Inner.flatten pullback₁ Inner.flatten-isEquiv changed-first)
      outer-second : IsEquiv (pullback₂ {f = p} {g = u})
      outer-second = equiv-cancel-right (pullback-swap u p) pullback₂ (pullback-swap-isEquiv u p)
        (equiv-transport ((pullback-factor-β₂ (cone-swap (pullback-cone u p))) ⁻¹) inner-first)
      self-second : IsEquiv (pullback₂ {f = i} {g = i})
      self-second = equiv-cancel-right Outer.flatten pullback₂ Outer.flatten-isEquiv
        (equiv-transport ((pullback-factor-β₂ Outer.flat-cone) ⁻¹)
          (equiv-compose pullback₂ v outer-second er))

module _ {Γ : Context} (C : CAT Γ) where
  isoArrow-isEmbedding : IsEmbedding (isoArrow C)
  isoArrow-isEmbedding = embedding-cong Comparison.comparison-arrow
    (Intersection.embedding
      (change-right-projection rightInverseArrow Comparison.comparison-arrow
        (UniversalInverseFibers.right-projection-isEquiv C))
      (change-right-projection leftInverseArrow Comparison.comparison-arrow
        (UniversalInverseFibers.left-projection-isEquiv C)))
    where
    module Comparison = InverseComparison C using (square; square-isPullback; comparison-arrow)
    module Intersection = IntersectionEmbedding rightInverseArrow leftInverseArrow
      Comparison.square Comparison.square-isPullback using (embedding)
```

Only the identity-arrow corollary needs the equivalence of identityIso.
Its given arrow comparison and composition of embeddings supply the
conclusion. The preceding isomorphism embedding remains independent of
that additional hypothesis.

```agda
module _ {Γ : Context} (C : CAT Γ) where
  identityArrow-isEmbedding : IsEquiv (identityIso C) → IsEmbedding (identityArrow {C = C})
  identityArrow-isEmbedding rezk = embedding-cong (identityIso-arrow C)
    (LeftCancellation.compose (identityIso C) (isoArrow C) (isoArrow-isEmbedding C)
      (equivalence-isEmbedding (identityIso C) rezk))
```
