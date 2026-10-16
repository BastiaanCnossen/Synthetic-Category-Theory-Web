# Squares glued along the specified diagonal

The two triangle inclusions are j₀=(s₀,s₁) and j₁=(s₁,s₀).
Their long edges both map to the diagonal. The specified cell traverses
j₀-diagonal and then the inverse of j₁-diagonal; its direction is
j₀ composed with d₁ to j₁ composed with d₁. The square axiom asserts
that this particular square is a pushout.

The existing mapping-out criterion derives the corresponding pullback of
functor categories. Gluing uses its actual native cone and chosen universal
factor. Its beta retains both triangle identifications and their entire
common-diagonal square, for every categorical family source P.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.SquareGluing where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (swap; swap-swap)
open import SCT.VolumeI.Chapter01.Section03.Equivalences using (id-isEquiv; equiv-transport)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (product-square)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback; module UniversalCone)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Points using (decode)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-swap; cone-swap-twice)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality
  using (isPullback-cone-identification; module SwappedCone)
open import SCT.VolumeI.Chapter01.Section06.PullbackConstructions using (isPullback-from-left-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PastingLemma using (module Pasting)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories using (Fun; funEval)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-comp; funPre⁼; funPre-id)
open import SCT.VolumeI.Chapter01.Section07.Currying using (funUncurry; funCurry-β)
open import SCT.VolumeI.Chapter01.Section08.Cocones
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares using (IsPushout; mappingOut)
open import SCT.VolumeI.Chapter01.Section08.FunctorPushoutCriterion
  using (functorOut; pushout→functor-criterion; module NativeParameterizedSquareEvaluation)
open import SCT.VolumeI.Chapter01.Section08.FunctorMappingOutEvaluation
  using (module NativeRestrictionCocones; module OrdinaryMappingCocones; module OrdinaryParameterizedSquareEvaluation)
open import SCT.VolumeI.Chapter01.Section07.Evaluation using (evaluate-cong; evaluate-restrict)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (encode; DiagramFamily; MorphismFamilyIdentification; insert; module AtPoint)
open import SCT.VolumeI.Chapter02.Section01.HomAndSlices
  using (interval-zero-initial; interval-one-terminal)
open import SCT.VolumeI.Chapter02.Section01.WalkingMorphism using ([1]; zero; one)
open import SCT.VolumeI.Chapter02.Section01.WalkingTriangle
  using ([2]; d₀; d₁; d₂; s₀; s₁; s₀-d₀; s₁-d₀; s₀-d₁; s₁-d₁;
    s₀-d₂; s₁-d₂; d₂-zero; d₂-one; d₀-zero; d₀-one; vertex₀; vertex₁; vertex₂;
    s₀-vertex₀; s₁-vertex₀; s₀-vertex₁; s₁-vertex₁; s₀-vertex₂; s₁-vertex₂; initial-family-comparison; terminal-family-comparison)

module _ {Γ : Context} where
  Squares : CAT Γ → CAT Γ
  Squares C = Fun ([1] × [1]) C

  j₀ j₁ : MAP ([2] {Γ = Γ}) ([1] × [1])
  j₀ = pair s₀ s₁
  j₁ = pair s₁ s₀

  diagonal : MAP ([1] {Γ = Γ}) ([1] × [1])
  diagonal = pair (id [1]) (id [1])

  j₀-diagonal : (j₀ ∘ (d₁ {Γ = Γ})) =₁ diagonal
  j₀-diagonal = pair⁼ s₀-d₁ s₁-d₁ ∙ pair-pre s₀ s₁ d₁
  j₁-diagonal : (j₁ ∘ (d₁ {Γ = Γ})) =₁ diagonal
  j₁-diagonal = pair⁼ s₁-d₁ s₀-d₁ ∙ pair-pre s₁ s₀ d₁

  gluing-square : Square (d₁ {Γ = Γ}) j₀
  gluing-square = record
    { source-map = d₁; target-map = j₁
    ; cell = j₁-diagonal ⁻¹ ∙ j₀-diagonal }

  postulate
    square-isPushout : IsPushout gluing-square
```

All four boundary restrictions are the pairings dictated by the six
face-degeneracy equations. The named triangle vertices determine the
four corners, with the common first and last corner retained on both sides.
These equations keep their chosen face and vertex witnesses.

```agda
module _ {Γ : Context} where
  j₀-d₂ : (j₀ ∘ (d₂ {Γ = Γ})) =₁ pair (const zero) (id [1])
  j₀-d₂ = pair⁼ s₀-d₂ s₁-d₂ ∙ pair-pre s₀ s₁ d₂
  j₁-d₂ : (j₁ ∘ (d₂ {Γ = Γ})) =₁ pair (id [1]) (const zero)
  j₁-d₂ = pair⁼ s₁-d₂ s₀-d₂ ∙ pair-pre s₁ s₀ d₂
  j₀-d₀ : (j₀ ∘ (d₀ {Γ = Γ})) =₁ pair (id [1]) (const one)
  j₀-d₀ = pair⁼ s₀-d₀ s₁-d₀ ∙ pair-pre s₀ s₁ d₀
  j₁-d₀ : (j₁ ∘ (d₀ {Γ = Γ})) =₁ pair (const one) (id [1])
  j₁-d₀ = pair⁼ s₁-d₀ s₀-d₀ ∙ pair-pre s₁ s₀ d₀

  j₀-vertex₀ : (j₀ ∘ (vertex₀ {Γ = Γ})) =₁ pair zero zero
  j₀-vertex₀ = pair⁼ s₀-vertex₀ s₁-vertex₀ ∙ pair-pre s₀ s₁ vertex₀
  j₁-vertex₀ : (j₁ ∘ (vertex₀ {Γ = Γ})) =₁ pair zero zero
  j₁-vertex₀ = pair⁼ s₁-vertex₀ s₀-vertex₀ ∙ pair-pre s₁ s₀ vertex₀
  j₀-vertex₁ : (j₀ ∘ (vertex₁ {Γ = Γ})) =₁ pair zero one
  j₀-vertex₁ = pair⁼ s₀-vertex₁ s₁-vertex₁ ∙ pair-pre s₀ s₁ vertex₁
  j₁-vertex₁ : (j₁ ∘ (vertex₁ {Γ = Γ})) =₁ pair one zero
  j₁-vertex₁ = pair⁼ s₁-vertex₁ s₀-vertex₁ ∙ pair-pre s₁ s₀ vertex₁
  j₀-vertex₂ : (j₀ ∘ (vertex₂ {Γ = Γ})) =₁ pair one one
  j₀-vertex₂ = pair⁼ s₀-vertex₂ s₁-vertex₂ ∙ pair-pre s₀ s₁ vertex₂
  j₁-vertex₂ : (j₁ ∘ (vertex₂ {Γ = Γ})) =₁ pair one one
  j₁-vertex₂ = pair⁼ s₁-vertex₂ s₀-vertex₂ ∙ pair-pre s₁ s₀ vertex₂
```

The restriction cone below is literally the previously constructed native
functorOut cone. Its matching is not replaced by a separately pasted
precomposition comparison. Complete cone identifications, rather than
independent leg equations, are the inputs to recovery.

```agda
module _ {Γ : Context} where
  square-cone : (C : CAT Γ) → Cone (funPre {D = C} d₁) (funPre d₁) (Squares C)
  square-cone C = functorOut gluing-square C

  square-functor-pullback : (C : CAT Γ) → IsPullback (square-cone C)
  square-functor-pullback = pushout→functor-criterion gluing-square square-isPushout

  module Families (C : CAT Γ) where
    private
      module Universal = UniversalCone (square-cone C) (square-functor-pullback C)

    glue : {P : CAT Γ} → Cone (funPre {D = C} d₁) (funPre d₁) P → MAP P (Squares C)
    glue = Universal.factor

    glue-β : {P : CAT Γ} (t : Cone (funPre {D = C} d₁) (funPre d₁) P)
      → ConeIdentification₁ (cone-restrict (glue t) (square-cone C)) t
    glue-β = Universal.β

    compare : {P : CAT Γ} (h k : MAP P (Squares C))
      → ConeIdentification₁ (cone-restrict h (square-cone C)) (cone-restrict k (square-cone C))
      → h =₁ k
    compare = Universal.reflect

    glue-η : {P : CAT Γ} (h : MAP P (Squares C))
      → glue (cone-restrict h (square-cone C)) =₁ h
    glue-η h = compare _ h (glue-β (cone-restrict h (square-cone C)))

    module Diagram {P : CAT Γ} (t : Cone (funPre {D = C} d₁) (funPre d₁) P) where
      private
        module Native = NativeRestrictionCocones {P = P} {E = C} d₁ d₁
        module Actual = NativeParameterizedSquareEvaluation {Γ = Γ} {P = P} {E = C}
          gluing-square (glue t)

      value : MAP (P × ([1] × [1])) C
      value = funUncurry (glue t)

      β : CoconeIdentification₁
        (cocone-postcompose value (square-cocone (product-square {P = P} gluing-square)))
        (Native.represented t)
      β = cocone-identification-One
        (cocone-identification-compose
          (Native.evaluate-identification (cone-identification (glue-β t)))
          (cocone-identification-inverse (cocone-identification Actual.identification)))
```

The raw shape maps p₀ and p₂ use ordinary cocone gluing. Naming and decoding
through the existing mapping-out universal cone produce the square together
with its complete cocone beta, including the supplied diagonal matching.
This adapts the finite ordinary-extension proof from the old construction
through public interfaces. It does not identify this chosen raw extension
with an independently selected family factor.

The collapse matchings below are exactly the manuscript paths built from
the chosen s₀-d₁ and s₁-d₁ equations. The four restrictions of p₀ and p₂
are projections of their complete cocone betas.

```agda
module _ {Γ : Context} where
  module Absolute (C : CAT Γ) where
    private
      module Universal = UniversalCone (mappingOut gluing-square C) (square-isPushout C)
      module Encoding = OrdinaryMappingCocones {E = C} d₁ d₁

    module Chosen (t : Cocone (d₁ {Γ = Γ}) d₁ C) where
      private
        point : MAP One (Map ([1] × [1]) C)
        point = Universal.factor (Encoding.encoded t)
        module Actual = OrdinaryParameterizedSquareEvaluation {Γ = Γ} {E = C} gluing-square point

      value : MAP ([1] × [1]) C
      value = decode point

      β : CoconeIdentification₁ (cocone-postcompose value (square-cocone gluing-square)) t
      β = cocone-identification-One
        (cocone-identification-compose (cocone-identification (Encoding.decoded-encoded t))
          (cocone-identification-compose
            (Encoding.decoded-identification (cone-identification (Universal.β (Encoding.encoded t))))
            (cocone-identification-inverse (cocone-identification Actual.identification))))

    glue : Cocone (d₁ {Γ = Γ}) d₁ C → MAP ([1] × [1]) C
    glue = Chosen.value
    glue-β : (t : Cocone (d₁ {Γ = Γ}) d₁ C)
      → CoconeIdentification₁ (cocone-postcompose (glue t) (square-cocone gluing-square)) t
    glue-β = Chosen.β

  private
    collapse-matching : (s : MAP ([2] {Γ = Γ}) [1]) → (s ∘ d₁) =₁ id [1]
      → (id [2] ∘ d₁) =₁ ((d₁ ∘ s) ∘ d₁)
    collapse-matching s ε = (comp-assoc d₁ s d₁) ⁻¹ ∙
      ((d₁ ◁ ε ⁻¹) ∙ ((comp-unitʳ d₁) ⁻¹ ∙ comp-unitˡ d₁))

  lower-cocone upper-cocone : Cocone (d₁ {Γ = Γ}) d₁ [2]
  lower-cocone = record
    { left = id [2]; right = d₁ ∘ s₀; match = collapse-matching s₀ s₀-d₁ }
  upper-cocone = record
    { left = d₁ ∘ s₁; right = id [2]; match = (collapse-matching s₁ s₁-d₁) ⁻¹ }

  p₀ p₂ : MAP ([1] × [1]) ([2] {Γ = Γ})
  p₀ = Absolute.glue [2] lower-cocone
  p₂ = Absolute.glue [2] upper-cocone

  p₀-β : CoconeIdentification₁ (cocone-postcompose p₀ (square-cocone gluing-square)) lower-cocone
  p₀-β = Absolute.glue-β [2] lower-cocone
  p₂-β : CoconeIdentification₁ (cocone-postcompose p₂ (square-cocone gluing-square)) upper-cocone
  p₂-β = Absolute.glue-β [2] upper-cocone

  p₀-j₀ : (p₀ ∘ j₀) =₁ id [2]
  p₀-j₀ = CoconeIdentification₁.left p₀-β
  p₀-j₁ : (p₀ ∘ j₁) =₁ d₁ ∘ s₀
  p₀-j₁ = CoconeIdentification₁.right p₀-β
  p₂-j₀ : (p₂ ∘ j₀) =₁ d₁ ∘ s₁
  p₂-j₀ = CoconeIdentification₁.left p₂-β
  p₂-j₁ : (p₂ ∘ j₁) =₁ id [2]
  p₂-j₁ = CoconeIdentification₁.right p₂-β
```

Two retraction pullbacks follow by cancelling the square-axiom pullback.
After pasting, both outer horizontal functors are equivalences, using the
chosen face-degeneracy and p₀/p₂ restriction equations. The argument keeps
the actual native square cone and its pasted matching throughout.

These are the two square-retraction pullbacks used in the triangle-pullback
argument. The later constant-side triangle pullbacks require a further
Segal cancellation and unit comparisons, which are not asserted here.

```agda
private
  module _ {Γ : Context} where
    horizontal-equivalences : {A B Z T : CAT Γ} {f : MAP A Z} {g : MAP B Z}
      (s : Cone f g T) → IsEquiv f → IsEquiv (Cone.right s) → IsPullback s
    horizontal-equivalences s ef eq = isPullback-cone-identification (cone-swap-twice s)
      (SwappedCone.isPullback (cone-swap s)
        (isPullback-from-left-isEquiv ef (cone-swap s) eq))

module _ {Γ : Context} where
  module RetractionPullbacks (C : CAT Γ) where
    private
      module Lower = Pasting (funPre {D = C} s₀) (funPre d₁) (funPre d₁)
        (cone-swap (square-cone C))
        (SwappedCone.isPullback (square-cone C) (square-functor-pullback C))
      module Upper = Pasting (funPre {D = C} s₁) (funPre d₁) (funPre d₁)
        (square-cone C) (square-functor-pullback C)

    lower-cone : Cone (funPre {D = C} s₀) (funPre j₁) (Fun [2] C)
    lower-cone = record
      { left = funPre d₁; right = funPre p₀
      ; match = (funPre-comp j₁ p₀) ⁻¹ ∙
          ((funPre⁼ p₀-j₁) ⁻¹ ∙ funPre-comp s₀ d₁) }

    lower-isPullback : IsPullback lower-cone
    lower-isPullback = Lower.unpaste-isPullback lower-cone
      (horizontal-equivalences (Lower.Paste.paste lower-cone)
        (equiv-transport
          ((funPre-id [1] C ∙ (funPre⁼ s₀-d₁ ∙ funPre-comp d₁ s₀)) ⁻¹)
          (id-isEquiv (Fun [1] C)))
        (equiv-transport
          ((funPre-id [2] C ∙ (funPre⁼ p₀-j₀ ∙ funPre-comp j₀ p₀)) ⁻¹)
          (id-isEquiv (Fun [2] C))))

    upper-cone : Cone (funPre {D = C} s₁) (funPre j₀) (Fun [2] C)
    upper-cone = record
      { left = funPre d₁; right = funPre p₂
      ; match = (funPre-comp j₀ p₂) ⁻¹ ∙
          ((funPre⁼ p₂-j₀) ⁻¹ ∙ funPre-comp s₁ d₁) }

    upper-isPullback : IsPullback upper-cone
    upper-isPullback = Upper.unpaste-isPullback upper-cone
      (horizontal-equivalences (Upper.Paste.paste upper-cone)
        (equiv-transport
          ((funPre-id [1] C ∙ (funPre⁼ s₁-d₁ ∙ funPre-comp d₁ s₁)) ⁻¹)
          (id-isEquiv (Fun [1] C)))
        (equiv-transport
          ((funPre-id [2] C ∙ (funPre⁼ p₂-j₁ ∙ funPre-comp j₁ p₂)) ⁻¹)
          (id-isEquiv (Fun [2] C))))
```

The coordinate descriptions of p₀ and p₂ follow from their whole cocone
betas and the endpoint uniqueness of interval diagrams. Here min and max
are literally the uncurried existing faces d₂ and d₀. Their recognition
uses the chosen framed initial/terminal comparisons, retaining both endpoint
conditions before extracting the underlying diagram identification.

The four coordinate equations and their paired forms below are underlying
functor identifications. No further higher compatibility between these
coordinate identifications is asserted.

```agda
module _ {Γ : Context} where
  min max : MAP ([1] × [1]) ([1] {Γ = Γ})
  min = funUncurry d₂
  max = funUncurry d₀

  min-right-zero : (min ∘ insert zero) =₁ const (zero {Γ = Γ})
  min-right-zero = s₀-d₂ ∙ (AtPoint.uncurry-image zero d₂) ⁻¹
  min-right-one : (min ∘ insert one) =₁ id ([1] {Γ = Γ})
  min-right-one = s₁-d₂ ∙ (AtPoint.uncurry-image one d₂) ⁻¹
  max-right-zero : (max ∘ insert zero) =₁ id ([1] {Γ = Γ})
  max-right-zero = s₀-d₀ ∙ (AtPoint.uncurry-image zero d₀) ⁻¹
  max-right-one : (max ∘ insert one) =₁ const (one {Γ = Γ})
  max-right-one = s₁-d₀ ∙ (AtPoint.uncurry-image one d₀) ⁻¹

  private
    initial-diagram-compare : {P : CAT Γ} (y : MAP P [1])
      (F G : MAP (P × [1]) [1])
      → (F ∘ insert zero) =₁ const zero → (F ∘ insert one) =₁ y
      → (G ∘ insert zero) =₁ const zero → (G ∘ insert one) =₁ y → F =₁ G
    initial-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
      (evaluate-cong (funEval {C = [1]} {D = [1]})
        (MorphismFamilyIdentification.identification
          (initial-family-comparison zero interval-zero-initial y
            (encode (record { diagram = F; source-frame = f₀; target-frame = f₁ }))
            (encode (record { diagram = G; source-frame = g₀; target-frame = g₁ })))) ∙
        (funCurry-β F) ⁻¹)

    terminal-diagram-compare : {P : CAT Γ} (y : MAP P [1])
      (F G : MAP (P × [1]) [1])
      → (F ∘ insert zero) =₁ y → (F ∘ insert one) =₁ const one
      → (G ∘ insert zero) =₁ y → (G ∘ insert one) =₁ const one → F =₁ G
    terminal-diagram-compare y F G f₀ f₁ g₀ g₁ = funCurry-β G ∙
      (evaluate-cong (funEval {C = [1]} {D = [1]})
        (MorphismFamilyIdentification.identification
          (terminal-family-comparison one interval-one-terminal y
            (encode (record { diagram = F; source-frame = f₀; target-frame = f₁ }))
            (encode (record { diagram = G; source-frame = g₀; target-frame = g₁ })))) ∙
        (funCurry-β F) ⁻¹)

    recognize-min : (H : MAP ([1] × [1]) ([1] {Γ = Γ}))
      → (H ∘ insert zero) =₁ const zero → (H ∘ insert one) =₁ id [1] → H =₁ min
    recognize-min H h₀ h₁ = initial-diagram-compare (id [1]) H min
      h₀ h₁ min-right-zero min-right-one
    recognize-max : (H : MAP ([1] × [1]) ([1] {Γ = Γ}))
      → (H ∘ insert zero) =₁ id [1] → (H ∘ insert one) =₁ const one → H =₁ max
    recognize-max H h₀ h₁ = terminal-diagram-compare (id [1]) H max
      h₀ h₁ max-right-zero max-right-one
    recognize-second-projection : (H : MAP ([1] × [1]) ([1] {Γ = Γ}))
      → (H ∘ insert zero) =₁ const zero → (H ∘ insert one) =₁ const one → H =₁ pr₂
    recognize-second-projection H h₀ h₁ = initial-diagram-compare (const one) H pr₂ h₀ h₁
      (pair-β₂ (id [1]) (const zero)) (pair-β₂ (id [1]) (const one))

  glue-bottom : {C : CAT Γ} (t : Cocone (d₁ {Γ = Γ}) d₁ C)
    → (Absolute.glue C t ∘ insert zero) =₁ (Cocone.right t ∘ d₂)
  glue-bottom {C} t = (CoconeIdentification₁.right (Absolute.glue-β C t) ▷ d₂) ∙
    ((comp-assoc d₂ j₁ (Absolute.glue C t)) ⁻¹ ∙ (Absolute.glue C t ◁ j₁-d₂ ⁻¹))
  glue-top : {C : CAT Γ} (t : Cocone (d₁ {Γ = Γ}) d₁ C)
    → (Absolute.glue C t ∘ insert one) =₁ (Cocone.left t ∘ d₀)
  glue-top {C} t = (CoconeIdentification₁.left (Absolute.glue-β C t) ▷ d₀) ∙
    ((comp-assoc d₀ j₀ (Absolute.glue C t)) ⁻¹ ∙ (Absolute.glue C t ◁ j₀-d₀ ⁻¹))

  private
    coordinate-bottom : (F : MAP ([2] {Γ = Γ}) [1]) (t : Cocone d₁ d₁ [2])
      → ((F ∘ Absolute.glue [2] t) ∘ insert zero) =₁ ((F ∘ Cocone.right t) ∘ d₂)
    coordinate-bottom F t = (comp-assoc d₂ (Cocone.right t) F) ⁻¹ ∙
      ((F ◁ glue-bottom t) ∙ comp-assoc (insert zero) (Absolute.glue [2] t) F)
    coordinate-top : (F : MAP ([2] {Γ = Γ}) [1]) (t : Cocone d₁ d₁ [2])
      → ((F ∘ Absolute.glue [2] t) ∘ insert one) =₁ ((F ∘ Cocone.left t) ∘ d₀)
    coordinate-top F t = (comp-assoc d₀ (Cocone.left t) F) ⁻¹ ∙
      ((F ◁ glue-top t) ∙ comp-assoc (insert one) (Absolute.glue [2] t) F)
    collapse-coordinate : (s : MAP ([2] {Γ = Γ}) [1]) → (s ∘ d₁) =₁ id [1]
      → (t : MAP [2] [1]) → (s ∘ (d₁ ∘ t)) =₁ t
    collapse-coordinate s ε t = comp-unitˡ t ∙ ((ε ▷ t) ∙ (comp-assoc t d₁ s) ⁻¹)

  s₀-p₀ : (s₀ ∘ p₀) =₁ min
  s₀-p₀ = recognize-min _
    (s₀-d₂ ∙ ((collapse-coordinate s₀ s₀-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₀ lower-cocone))
    (s₀-d₀ ∙ ((comp-unitʳ s₀ ▷ d₀) ∙ coordinate-top s₀ lower-cocone))
  s₁-p₀ : (s₁ ∘ p₀) =₁ (pr₂ {C = [1] {Γ = Γ}} {D = [1]})
  s₁-p₀ = recognize-second-projection _
    (s₀-d₂ ∙ ((collapse-coordinate s₁ s₁-d₁ s₀ ▷ d₂) ∙ coordinate-bottom s₁ lower-cocone))
    (s₁-d₀ ∙ ((comp-unitʳ s₁ ▷ d₀) ∙ coordinate-top s₁ lower-cocone))
  s₀-p₂ : (s₀ ∘ p₂) =₁ (pr₂ {C = [1] {Γ = Γ}} {D = [1]})
  s₀-p₂ = recognize-second-projection _
    (s₀-d₂ ∙ ((comp-unitʳ s₀ ▷ d₂) ∙ coordinate-bottom s₀ upper-cocone))
    (s₁-d₀ ∙ ((collapse-coordinate s₀ s₀-d₁ s₁ ▷ d₀) ∙ coordinate-top s₀ upper-cocone))
  s₁-p₂ : (s₁ ∘ p₂) =₁ max
  s₁-p₂ = recognize-max _
    (s₁-d₂ ∙ ((comp-unitʳ s₁ ▷ d₂) ∙ coordinate-bottom s₁ upper-cocone))
    (s₁-d₀ ∙ ((collapse-coordinate s₁ s₁-d₁ s₁ ▷ d₀) ∙ coordinate-top s₁ upper-cocone))

  j₀-p₀ : (j₀ ∘ p₀) =₁ pair min pr₂
  j₀-p₀ = pair⁼ s₀-p₀ s₁-p₀ ∙ pair-pre s₀ s₁ p₀
  j₁-p₀ : (j₁ ∘ p₀) =₁ pair pr₂ min
  j₁-p₀ = pair⁼ s₁-p₀ s₀-p₀ ∙ pair-pre s₁ s₀ p₀
  j₀-p₂ : (j₀ ∘ p₂) =₁ pair pr₂ max
  j₀-p₂ = pair⁼ s₀-p₂ s₁-p₂ ∙ pair-pre s₀ s₁ p₂
  j₁-p₂ : (j₁ ∘ p₂) =₁ pair max pr₂
  j₁-p₂ = pair⁼ s₁-p₂ s₀-p₂ ∙ pair-pre s₁ s₀ p₂
```

## Minimum, maximum and projections as glued squares

Gluing two copies of the same degeneracy gives minimum or maximum. The two
mixed choices give the projections. Their common-edge identifications are
specified through the identity functor. These are underlying functor
identifications; equality to other derived matching witnesses is not asserted.

For the first projection, read the two other sides and exchange the interval
coordinates. Initiality then identifies the exchanged diagram with the second
projection. This uses the existing uniqueness argument without a second
general cocone-reflection construction.

```agda
  minimum-cocone maximum-cocone first-projection-cocone second-projection-cocone :
    Cocone (d₁ {Γ = Γ}) d₁ [1]
  minimum-cocone = record { left = s₀; right = s₀; match = id₌ (s₀ ∘ d₁) }
  maximum-cocone = record { left = s₁; right = s₁; match = id₌ (s₁ ∘ d₁) }
  first-projection-cocone = record { left = s₀; right = s₁; match = s₁-d₁ ⁻¹ ∙ s₀-d₁ }
  second-projection-cocone = record { left = s₁; right = s₀; match = s₀-d₁ ⁻¹ ∙ s₁-d₁ }

  square-minimum : Absolute.glue [1] minimum-cocone =₁ min
  square-minimum = recognize-min _
    (s₀-d₂ ∙ glue-bottom minimum-cocone) (s₀-d₀ ∙ glue-top minimum-cocone)

  square-maximum : Absolute.glue [1] maximum-cocone =₁ max
  square-maximum = recognize-max _
    (s₁-d₂ ∙ glue-bottom maximum-cocone) (s₁-d₀ ∙ glue-top maximum-cocone)

  square-second-projection : Absolute.glue [1] second-projection-cocone =₁ pr₂
  square-second-projection = recognize-second-projection _
    (s₀-d₂ ∙ glue-bottom second-projection-cocone)
    (s₁-d₀ ∙ glue-top second-projection-cocone)

  private
    glue-left : {C : CAT Γ} (t : Cocone (d₁ {Γ = Γ}) d₁ C)
      → (Absolute.glue C t ∘ pair (const zero) (id [1])) =₁ (Cocone.left t ∘ d₂)
    glue-left {C} t = (CoconeIdentification₁.left (Absolute.glue-β C t) ▷ d₂) ∙
      ((comp-assoc d₂ j₀ (Absolute.glue C t)) ⁻¹ ∙ (Absolute.glue C t ◁ j₀-d₂ ⁻¹))

    glue-right : {C : CAT Γ} (t : Cocone (d₁ {Γ = Γ}) d₁ C)
      → (Absolute.glue C t ∘ pair (const one) (id [1])) =₁ (Cocone.right t ∘ d₀)
    glue-right {C} t = (CoconeIdentification₁.right (Absolute.glue-β C t) ▷ d₀) ∙
      ((comp-assoc d₀ j₁ (Absolute.glue C t)) ⁻¹ ∙ (Absolute.glue C t ◁ j₁-d₀ ⁻¹))

    swap-insert : (point : MAP One ([1] {Γ = Γ}))
      → (swap ∘ insert point) =₁ pair (const point) (id [1])
    swap-insert point = pair⁼ (pair-β₂ (id [1]) (const point)) (pair-β₁ (id [1]) (const point)) ∙
      pair-pre pr₂ pr₁ (insert point)

    exchanged-row : (H : MAP ([1] × [1]) ([1] {Γ = Γ})) (point : MAP One [1])
      → ((H ∘ swap) ∘ insert point) =₁ (H ∘ pair (const point) (id [1]))
    exchanged-row H point = (H ◁ swap-insert point) ∙ comp-assoc (insert point) swap H

  square-first-projection : Absolute.glue [1] first-projection-cocone =₁ pr₁
  square-first-projection = pair-β₂ pr₂ pr₁ ∙
    ((exchanged ▷ swap) ∙
      ((comp-assoc swap swap H) ⁻¹ ∙
        ((H ◁ (swap-swap [1] [1]) ⁻¹) ∙ (comp-unitʳ H) ⁻¹)))
    where
      H : MAP ([1] × [1]) ([1] {Γ = Γ})
      H = Absolute.glue [1] first-projection-cocone
      exchanged : (H ∘ swap) =₁ pr₂
      exchanged = recognize-second-projection _
        (s₀-d₂ ∙ (glue-left first-projection-cocone ∙ exchanged-row H zero))
        (s₁-d₀ ∙ (glue-right first-projection-cocone ∙ exchanged-row H one))
```

The remaining four lattice boundary equations follow from the named vertices
of the two face families. Evaluating a family at a point and then uncurrying
agrees with restricting its uncurrying to that row. Applying this to the
specified face-to-vertex identifications supplies the left endpoint laws;
no symmetry of minimum or maximum is assumed.

```agda
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; product-unitˡ-inverse; product-unitˡ-pr₂-inverse)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing using (productMap-pair)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun using (funName; funName-β)

private
  module _ {Γ : Context} {X I C : CAT Γ} where
    row-from-point : (h : MAP X (Fun I C)) (x : MAP One X) (f : MAP I C)
      → (h ∘ x) =₁ funName f
      → (funUncurry h ∘ pair (const x) (id I)) =₁ f
    row-from-point h x f δ = named-row ∙
      ((evaluate-cong e δ ▷ u) ∙
        (((evaluate-restrict e h x) ⁻¹ ▷ u) ∙
          ((comp-assoc u k (funUncurry h)) ⁻¹ ∙
            (funUncurry h ◁ (at-row ⁻¹)))))
      where
        e : MAP (Fun I C × I) C
        e = funEval
        u : MAP I (One × I)
        u = product-unitˡ-inverse I
        k : MAP (One × I) (X × I)
        k = productMap x (id I)
        at-row : (k ∘ u) =₁ pair (const x) (id I)
        at-row = pair⁼ (id₌ (const x)) (comp-unitˡ (id I)) ∙
          productMap-pair x (id I) (terminate I) (id I)
        named-row : (funUncurry (funName f) ∘ u) =₁ f
        named-row = comp-unitʳ f ∙
          ((f ◁ product-unitˡ-pr₂-inverse I) ∙
            (comp-assoc u pr₂ f ∙ (funName-β f ▷ u)))

module _ {Γ : Context} where
  min-left-zero : (min ∘ pair (const zero) (id [1])) =₁ const (zero {Γ = Γ})
  min-left-zero = row-from-point d₂ zero (const zero) d₂-zero
  min-left-one : (min ∘ pair (const one) (id [1])) =₁ id ([1] {Γ = Γ})
  min-left-one = row-from-point d₂ one (id [1]) d₂-one
  max-left-zero : (max ∘ pair (const zero) (id [1])) =₁ id ([1] {Γ = Γ})
  max-left-zero = row-from-point d₀ zero (id [1]) d₀-zero
  max-left-one : (max ∘ pair (const one) (id [1])) =₁ const (one {Γ = Γ})
  max-left-one = row-from-point d₀ one (const one) d₀-one
```
