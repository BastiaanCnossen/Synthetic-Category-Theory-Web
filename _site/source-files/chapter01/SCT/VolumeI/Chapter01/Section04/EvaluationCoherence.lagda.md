# Evaluation and its composition comparisons

The calculation keeps the family parameter independent of both the mapping
term source and its evaluation source. Each computation is a full square
with the original supplied comparison as its constant side.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.EvaluationCoherence where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌;
    postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus using (pair⁼)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.Currying
open import SCT.VolumeI.Chapter01.Section04.Composition
import SCT.VolumeI.Chapter01.Section04.CompositionEvaluationFamily as BetaFirstFamily
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase
  using (uncurry-compose; evaluation-compose; evaluation⁼; forget-evaluation⁼)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingOverBase using (module OverFirstFactor)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (IdentificationOver)

module _ {Γ : Context} {X : CAT Γ} where
  open Terms.Equalities X using (_＝_)

  private
    paste-fixed : {A B : CAT Γ} {x y x′ y′ x″ y″ : MAP A B}
      {t : x ＝ y} {m : x′ ＝ y′} {b : x″ ＝ y″}
      {l₁ : x =₁ x′} {r₁ : y =₁ y′} {l₂ : x′ =₁ x″} {r₂ : y′ =₁ y″}
      → SquareCell₌ t m (const l₁) (const r₁)
      → SquareCell₌ m b (const l₂) (const r₂)
      → SquareCell₌ t b (const (l₂ ∙ l₁)) (const (r₂ ∙ r₁))
    paste-fixed {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂} first second =
      replace-sides₌ (const-comp l₂ l₁) (const-comp r₂ r₁) (paste-square₌ first second)

    unit-input-square : {R C : CAT Γ} (x : MAP R C)
      → SquareCell₌ (const {P = X} (id₌ (id C)) ▷ x) (const (id₌ x))
          (const (comp-unitˡ x)) (const (comp-unitˡ x))
    unit-input-square {C = C} x = replace-edges₌ ((pre-constant (id₌ (id C)) x) ⁻¹) (id₌ _)
      (constant-square₌ {X = X} ((comp₌-unitˡ-One (comp-unitˡ x)) ⁻¹ ∙
        (comp₌-unitʳ-One (comp-unitˡ x) ∙
          comp₌-cong (id₌ (comp-unitˡ x)) (preWhisker-id₌ (id C) x))))

```

The evaluation-at-a-pair square first varies the mapping term and then the
pair of evaluation inputs. Product pairing computes both changes. The
postwhiskering composition law joins the coordinate normalizations into the
literal specified uncurry-at comparison.

```agda
  module _ {R P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    uncurry-at-outer : {y y′ : Term (Map C D)} (α : y ＝ y′)
      (p : MAP R P) (x : MAP R C)
      → SquareCell₌ (uncurry⁼ α ▷ pair p x)
          (apply-map⁼ (α ▷ p) (const (id₌ x)))
          (const (uncurry-at y p x)) (const (uncurry-at y′ p x))
    uncurry-at-outer {y} {y′} α p x =
      let input = productMap-cong α (const (id₌ (id C)))
          first = whisker-mixed input (pair p x) mapEval
          second = replace-sides₌
            (post-constant mapEval (productMap-pair y (id C) p x))
            (post-constant mapEval (productMap-pair y′ (id C) p x))
            (post-square₌ mapEval (productMap-pair-outer α (const (id₌ (id C))) p x))
          third = replace-sides₌
            (post-constant mapEval (pair⁼ (id₌ (y ∘ p)) (comp-unitˡ x)))
            (post-constant mapEval (pair⁼ (id₌ (y′ ∘ p)) (comp-unitˡ x)))
            (post-square₌ mapEval (replace-sides₌
              (pair⁼-constant (id₌ (y ∘ p)) (comp-unitˡ x))
              (pair⁼-constant (id₌ (y′ ∘ p)) (comp-unitˡ x))
              (pair⁼-square (identity-square₌ (α ▷ p)) (unit-input-square x))))
          joined = replace-sides₌
            (const-cong ((postWhisker-comp₌ mapEval
              (pair⁼ (id₌ (y ∘ p)) (comp-unitˡ x)) (productMap-pair y (id C) p x)) ⁻¹))
            (const-cong ((postWhisker-comp₌ mapEval
              (pair⁼ (id₌ (y′ ∘ p)) (comp-unitˡ x)) (productMap-pair y′ (id C) p x)) ⁻¹))
            (paste-fixed second third)
      in replace-edges₌ ((preWhisker (pair p x) ◁ uncurry⁼-evaluate α) ⁻¹) (id₌ _)
        (paste-fixed first joined)

    uncurry-at-inner : (y : Term (Map C D))
      {p p′ : MAP R P} {x x′ : MAP R C} (σ : p ＝ p′) (τ : x ＝ x′)
      → SquareCell₌ (uncurry y ◁ pair⁼ σ τ) (apply-map⁼ (y ◁ σ) τ)
          (const (uncurry-at y p x)) (const (uncurry-at y p′ x′))
    uncurry-at-inner y {p} {p′} {x} {x′} σ τ =
      let first = postWhisker-comp (pair⁼ σ τ) (productMap y (id C)) mapEval
          second = replace-sides₌
            (post-constant mapEval (productMap-pair y (id C) p x))
            (post-constant mapEval (productMap-pair y (id C) p′ x′))
            (post-square₌ mapEval (productMap-pair-inner y (id C) σ τ))
          third = replace-sides₌
            (post-constant mapEval (pair⁼ (id₌ (y ∘ p)) (comp-unitˡ x)))
            (post-constant mapEval (pair⁼ (id₌ (y ∘ p′)) (comp-unitˡ x′)))
            (post-square₌ mapEval (replace-sides₌
              (pair⁼-constant (id₌ (y ∘ p)) (comp-unitˡ x))
              (pair⁼-constant (id₌ (y ∘ p′)) (comp-unitˡ x′))
              (pair⁼-square (identity-square₌ (y ◁ σ)) (postWhisker-id τ))))
          joined = replace-sides₌
            (const-cong ((postWhisker-comp₌ mapEval
              (pair⁼ (id₌ (y ∘ p)) (comp-unitˡ x)) (productMap-pair y (id C) p x)) ⁻¹))
            (const-cong ((postWhisker-comp₌ mapEval
              (pair⁼ (id₌ (y ∘ p′)) (comp-unitˡ x′)) (productMap-pair y (id C) p′ x′)) ⁻¹))
            (paste-fixed second third)
      in paste-fixed first joined

  module _ {P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    uncurry-as-apply-natural : {y y′ : Term (Map C D)} (α : y ＝ y′)
      → SquareCell₌ (uncurry⁼ α)
          (apply-map⁼ (α ▷ pr₁) (const (id₌ pr₂)))
          (const (uncurry-as-apply y)) (const (uncurry-as-apply y′))
    uncurry-as-apply-natural {y} {y′} α =
      replace-edges₌ ((uncurry⁼-evaluate α) ⁻¹) (id₌ _)
        (replace-sides₌
          (post-constant mapEval (pair⁼ (id₌ (y ∘ pr₁)) (comp-unitˡ pr₂)))
          (post-constant mapEval (pair⁼ (id₌ (y′ ∘ pr₁)) (comp-unitˡ pr₂)))
          (post-square₌ mapEval (replace-sides₌
            (pair⁼-constant (id₌ (y ∘ pr₁)) (comp-unitˡ pr₂))
            (pair⁼-constant (id₌ (y′ ∘ pr₁)) (comp-unitˡ pr₂))
            (pair⁼-square (identity-square₌ (α ▷ pr₁)) (unit-input-square pr₂)))))

    apply-map-square : {y₀ y₁ y₂ y₃ : Term (Map C D)} {x₀ x₁ x₂ x₃ : Term C}
      {t₁ : y₀ ＝ y₁} {b₁ : y₂ ＝ y₃} {l₁ : y₀ ＝ y₂} {r₁ : y₁ ＝ y₃}
      {t₂ : x₀ ＝ x₁} {b₂ : x₂ ＝ x₃} {l₂ : x₀ ＝ x₂} {r₂ : x₁ ＝ x₃}
      → SquareCell₌ t₁ b₁ l₁ r₁ → SquareCell₌ t₂ b₂ l₂ r₂
      → SquareCell₌ (apply-map⁼ t₁ t₂) (apply-map⁼ b₁ b₂)
          (apply-map⁼ l₁ l₂) (apply-map⁼ r₁ r₂)
    apply-map-square first second = post-square₌ mapEval (pair⁼-square first second)

  private
    inverse-fixed : {A B : CAT Γ} {x y x′ y′ : MAP A B}
      {t : x ＝ y} {b : x′ ＝ y′} {l : x =₁ x′} {r : y =₁ y′}
      → SquareCell₌ t b (const l) (const r)
      → SquareCell₌ b t (const (l ⁻¹)) (const (r ⁻¹))
    inverse-fixed {l = l} {r} square =
      replace-sides₌ ((const-inv l) ⁻¹) ((const-inv r) ⁻¹) (inverse-square₌ square)

    apply-map-constant : {P C D : CAT Γ} {y y′ : MAP P (Map C D)} {x x′ : MAP P C}
      (α : y =₁ y′) (β : x =₁ x′)
      → apply-map⁼ (const {P = X} α) (const β) =₁ const (apply-map⁼ {X = One {Γ}} α β)
    apply-map-constant α β = post-constant mapEval (pair⁼ α β) ∙
      (postWhisker mapEval ◁ pair⁼-constant α β)

    apply-fixed-square : {P C D : CAT Γ}
      {y₀ y₁ y₂ y₃ : MAP P (Map C D)} {x₀ x₁ x₂ x₃ : MAP P C}
      {t₁ : y₀ ＝ y₁} {b₁ : y₂ ＝ y₃} {l₁ : y₀ =₁ y₂} {r₁ : y₁ =₁ y₃}
      {t₂ : x₀ ＝ x₁} {b₂ : x₂ ＝ x₃} {l₂ : x₀ =₁ x₂} {r₂ : x₁ =₁ x₃}
      → SquareCell₌ t₁ b₁ (const {P = X} l₁) (const r₁)
      → SquareCell₌ t₂ b₂ (const {P = X} l₂) (const r₂)
      → SquareCell₌ (apply-map⁼ t₁ t₂) (apply-map⁼ b₁ b₂)
          (const {P = X} (apply-map⁼ {X = One {Γ}} l₁ l₂))
          (const (apply-map⁼ {X = One {Γ}} r₁ r₂))
    apply-fixed-square {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂} first second =
      replace-sides₌ (apply-map-constant l₁ l₂) (apply-map-constant r₁ r₂)
        (apply-map-square first second)

    coordinate-square : {R A B C : CAT Γ} (F : MAP B C) (G : MAP A B)
      {u v : MAP R A} {x y : MAP R B} (α : u ＝ v) (β : x ＝ y)
      (l : (G ∘ u) =₁ x) (r : (G ∘ v) =₁ y)
      → SquareCell₌ (G ◁ α) β (const l) (const r)
      → SquareCell₌ ((F ∘ G) ◁ α) (F ◁ β)
          (const ((F ◁ l) ∙ comp-assoc u G F))
          (const ((F ◁ r) ∙ comp-assoc v G F))
    coordinate-square F G α β l r square = paste-fixed (postWhisker-comp α G F)
      (replace-sides₌ (post-constant F l) (post-constant F r) (post-square₌ F square))

  module _ {P C D E : CAT Γ} where
    open Terms.InContext P using (Term)

```

Composition applied to an input is computed on the paired triple. Its first
and second coordinates retain the projection squares, while the inner and
outer applications retain their binary restriction squares. The specified
currying beta closes the same route as apply-map-compose.

```agda
    apply-map-compose-natural : {y y′ : Term (Map D E)} {x x′ : Term (Map C D)} {z z′ : Term C}
      (α : y ＝ y′) (β : x ＝ x′) (τ : z ＝ z′)
      → SquareCell₌ (apply-map⁼ (compose⁼ α β) τ)
          (apply-map⁼ α (apply-map⁼ β τ))
          (const (apply-map-compose y x z)) (const (apply-map-compose y′ x′ z′))
    apply-map-compose-natural {y} {y′} {x} {x′} {z} {z′} α β τ =
      let triple = pair (pair y x) z
          triple′ = pair (pair y′ x′) z′
          changed = pair⁼ (pair⁼ α β) τ
          first = pair-β₁ y x ∙
            ((pr₁ ◁ pair-β₁ (pair y x) z) ∙ comp-assoc triple pr₁ pr₁)
          first′ = pair-β₁ y′ x′ ∙
            ((pr₁ ◁ pair-β₁ (pair y′ x′) z′) ∙ comp-assoc triple′ pr₁ pr₁)
          second = pair-β₂ y x ∙
            ((pr₂ ◁ pair-β₁ (pair y x) z) ∙ comp-assoc triple pr₁ pr₂)
          second′ = pair-β₂ y′ x′ ∙
            ((pr₂ ◁ pair-β₁ (pair y′ x′) z′) ∙ comp-assoc triple′ pr₁ pr₂)
          third = pair-β₂ (pair y x) z
          third′ = pair-β₂ (pair y′ x′) z′
          first-square = paste-fixed
            (coordinate-square pr₁ pr₁ changed (pair⁼ α β)
              (pair-β₁ (pair y x) z) (pair-β₁ (pair y′ x′) z′)
              (pair⁼-triangle₁ (pair⁼ α β) τ))
            (pair⁼-triangle₁ α β)
          second-square = paste-fixed
            (coordinate-square pr₂ pr₁ changed (pair⁼ α β)
              (pair-β₁ (pair y x) z) (pair-β₁ (pair y′ x′) z′)
              (pair⁼-triangle₁ (pair⁼ α β) τ))
            (pair⁼-triangle₂ α β)
          third-square = pair⁼-triangle₂ (pair⁼ α β) τ
          inner = apply-map⁼ second third ∙ apply-map-pre (pr₂ ∘ pr₁) pr₂ triple
          inner′ = apply-map⁼ second′ third′ ∙ apply-map-pre (pr₂ ∘ pr₁) pr₂ triple′
          inner-square = paste-fixed
            (Binary.binary-pre-substitution mapEval (pr₂ ∘ pr₁) pr₂ changed)
            (apply-fixed-square second-square third-square)
          outer = apply-map⁼ first inner ∙
            apply-map-pre (pr₁ ∘ pr₁) (apply-map (pr₂ ∘ pr₁) pr₂) triple
          outer′ = apply-map⁼ first′ inner′ ∙
            apply-map-pre (pr₁ ∘ pr₁) (apply-map (pr₂ ∘ pr₁) pr₂) triple′
          outer-square = paste-fixed
            (Binary.binary-pre-substitution mapEval (pr₁ ∘ pr₁)
              (apply-map (pr₂ ∘ pr₁) pr₂) changed)
            (apply-fixed-square first-square inner-square)
          before-square = inverse-fixed (uncurry-at-inner mapComp (pair⁼ α β) τ)
          beta-square = interchange-fixedOuter mapComp-β changed
      in paste-fixed (paste-fixed before-square beta-square) outer-square

  module _ {P C D E : CAT Γ} where
    open Terms.InContext P using (Term)

```

Uncurrying the selected composition comparison uses its beta-first family
naturality. The family parameter is independent of the term source, and the
constant sides retain the literal selected comparison.

```agda
    uncurry-compose-natural : {y y′ : Term (Map D E)} {x x′ : Term (Map C D)}
      (α : y ＝ y′) (β : x ＝ x′)
      → SquareCell₌ (uncurry⁼ (compose⁼ α β))
          (uncurry⁼ α ⋆ pair⁼ (const (id₌ pr₁)) (uncurry⁼ β))
          (const (uncurry-compose y x)) (const (uncurry-compose y′ x′))
    uncurry-compose-natural α β = BetaFirstFamily.FamilyCoordinates.composition-evaluation-natural
      {P = P} {C = C} {D = D} {E = E} α β

  module _ {P C D E : CAT Γ} where
    open Terms.InContext P using (Term)

```

Pair the uncurrying square with the constant identity in the parameter
coordinate. Pasting the inverse pairing-composition square gives naturality
of the actual relative evaluation comparison. This compares underlying
identification families; its components already carry their supplied
compatibility over the base. Faithfulness likewise reflects equality of the
whole underlying families and requires an anima term source.

```agda
    evaluation-compose-natural : {y y′ : Term (Map D E)} {x x′ : Term (Map C D)}
      (α : y ＝ y′) (β : x ＝ x′)
      → SquareCell₌ (evaluation⁼ (compose⁼ α β)) (evaluation⁼ α ⋆ evaluation⁼ β)
          (const (IdentificationOver.identification (evaluation-compose y x)))
          (const (IdentificationOver.identification (evaluation-compose y′ x′)))
    evaluation-compose-natural {y} {y′} {x} {x′} α β =
      let open OverFirstFactor P
          first = replace-sides₌
            (pair⁼-constant (id₌ pr₁) (uncurry-compose y x))
            (pair⁼-constant (id₌ pr₁) (uncurry-compose y′ x′))
            (pair⁼-square (identity-square₌ (const {P = X} (id₌ pr₁)))
              (uncurry-compose-natural α β))
          second = inverse-fixed (pair-pr₁-compose-natural (uncurry⁼ α) (uncurry⁼ β))
      in paste-fixed first second

  module _ {P C D : CAT Γ} where
    open Terms.InContext P using (Term)

    evaluation⁼-reflect : (pAn : isAn P) {x y : Term (Map C D)}
      (α β : x ＝ y) → evaluation⁼ α =₁ evaluation⁼ β → α =₁ β
    evaluation⁼-reflect pAn {x} {y} α β image =
      let input = const (OverFirstFactor.pair-pr₁-β₂ P (uncurry x))
          output = const (OverFirstFactor.pair-pr₁-β₂ P (uncurry y))
          forgotten = comp₌-cong
            (comp₌-cong (id₌ output) (postWhisker pr₂ ◁ image)) (id₌ (input ⁻¹))
      in uncurry⁼-reflect pAn α β
          (forget-evaluation⁼ β ∙ (forgotten ∙ (forget-evaluation⁼ α) ⁻¹))

```
