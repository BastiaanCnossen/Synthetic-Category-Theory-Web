# Native evaluation and encoding of restriction cocones

Native Fun precomposition cones represent cocones on the actual product
restriction. Their independent identification families retain the complete
matching square. Chosen currying encodes a product cocone and computes its
whole image. Mapping encoding additionally requires its actual anima source
witness, for the concrete converse and terminal adapters.

A private span-retraction calculation chooses reverse cells by reflection
against the given corner retractions and derives their complete matching
comparison. The swap client uses the specified swap-swap identifications;
the terminal client uses the actual projection and insertion retractions.
Only the roundtrip over the original span is required. Terminal encoding
keeps the selected Points.name legs, and its decoded comparison is
explicitly normalized to the existing Points.decode-name betas.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter01.Section08.FunctorMappingOutEvaluation where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; inv₌; preWhisker-id₌; comp-unitˡ; comp-unitʳ; comp-assoc; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (preWhisker-comp; preWhisker-id; whisker-mixed)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; swap; swap-swap; swap-isEquiv; product-unitˡ-inverse; product-unitˡ-pr₂-inverse; product-unitˡ-isEquiv)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (cancel-right; comp₌-inverseˡ-One; cancel-left; inverse-identity; comp₌-unitʳ-One; comp₌-unitˡ-One; inverse-composite; inverse-inverse; preWhisker-inverse; postWhisker-inverse)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; changeEndpoints-cong; transport-square; reflect-transported-square; restore-boundaries; changeEndpoints-iterated; square-to-changeEndpoints; postWhisker-changeEndpoints; changeEndpoints-extend-square)
import SCT.VolumeI.Chapter01.Section03.Factorizations as Fact
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square; comp-square)
import SCT.VolumeI.Chapter01.Section03.Squares as Squares
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-over₁-One; pair-pre-over₂-One)
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares using (mappingOut)
open import SCT.VolumeI.Chapter01.Section03.WhiskeringEquivalence using (factor-through-postWhisker; factor-through-postWhisker₂)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles using (post-triangle; restrict-triangle; lies-over-inverse; restrict-change-square-One; restrict-square-One; post-triangle-outer; post-square-cell; post-square-cell-id; post-square-cell-comp; post-square-cell-outer; lies-over-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change; post-restrict-triangle; post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (left-unitor-comp; postWhisker-id-One; triangle-whiskered; right-unitor-comp; whisker-mixed-One; postWhisker-comp-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction using (product-restriction; restriction-compositor; parameter-separation-composition; product-square; module SeparationSecondInput)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor using (productMap-cong-triangle₁; productMap-cong; productMap-cong₂; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate; productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map; uncurry; mapCurry; mapCurry-β)
open import SCT.VolumeI.Chapter01.Section04.Currying using (module CurriedRepresentation; uncurry⁼; uncurry-reflect; uncurry-reflect-β)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre-uncurry)
open import SCT.VolumeI.Chapter01.Section04.Points using (name; name-representation; decode; decode-name)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-inputs; evaluate-restrict-substitution)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
open import SCT.VolumeI.Chapter01.Section07.Currying using (funCurry; funCurry-β; funUncurry; reflect; reflect-β; reflect-β-One; evaluation-reflection₂)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre⁼; funPre⁼-evaluation; funPre-β; funPre-comp; funPre-uncurry; funPre-uncurry-inputs)
import SCT.VolumeI.Chapter01.Section07.PreEvaluationSubstitution as Pre
open import SCT.VolumeI.Chapter01.Section08.Cocones
open import SCT.VolumeI.Chapter01.Section08.MappingOutEvaluation using (module MappingOutEvaluation; module ParameterizedSquareEvaluation)

import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase as OverBase
import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution as FirstFactor
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-extensionality)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution using (evaluate-restrict-assoc)

private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)
    constant-endpoints : {A B : CAT Γ} {x x′ y y′ : MAP A B}
      (p : x =₁ x′) (q : y =₁ y′) (α : x =₁ y)
      → changeEndpoints (const {P = X} p) (const q) (const α) =₁ const (changeEndpoints p q α)
    constant-endpoints p q α = const-comp q (α ∙ p ⁻¹) ∙
      comp₌-cong (id₌ (const q))
        (const-comp α (p ⁻¹) ∙ comp₌-cong (id₌ (const α)) ((const-inv p) ⁻¹))

    module _ {F K D T : CAT Γ} (e : MAP (F × K) D) where
      evaluation-square : {f g f′ g′ : MAP T F}
        {α : f ＝ g} {β : f′ ＝ g′} {p : f ＝ f′} {q : g ＝ g′}
        → SquareCell₌ α β p q
        → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β) (evaluate⁼ e p) (evaluate⁼ e q)
      evaluation-square {α = α} {β} {p} {q} square = evaluate⁼-composition e β p ∙
        (evaluate⁼-cong e square ∙ (evaluate⁼-composition e q α) ⁻¹)
      evaluation-fixed-square : {f g f′ g′ : MAP T F}
        {α : f ＝ g} {β : f′ ＝ g′} {p : f =₁ f′} {q : g =₁ g′}
        → SquareCell₌ α β (const p) (const q)
        → SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β)
            (const (evaluate-cong e p)) (const (evaluate-cong e q))
      evaluation-fixed-square {p = p} {q} square = replace-sides₌
        (evaluate⁼-constant e p) (evaluate⁼-constant e q) (evaluation-square square)


```

A represented matching square determines a native matching through the
specified endpoint frames. The image below removes those frames and uses
the actual evaluation action. Higher reflection retains its chosen factor
and image triangle. The reflected legs are supplied by each client.

```agda
private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)
    module _ {F K D T : CAT Γ} (e : MAP (F × K) D)
      {f₀ g₀ f₁ g₁ : MAP T F}
      (σ₀ : f₀ =₁ g₀) (σ₁ : f₁ =₁ g₁) (α : f₀ ＝ f₁) (β : g₀ ＝ g₁)
      {a₀ b₀ a₁ b₁ : MAP (T × K) D}
      (p₀ : evaluate e f₀ =₁ a₀) (q₀ : evaluate e g₀ =₁ b₀)
      (p₁ : evaluate e f₁ =₁ a₁) (q₁ : evaluate e g₁ =₁ b₁)
      {a : a₀ ＝ a₁} {b : b₀ ＝ b₁}
      (L : SquareCell₌ (evaluate⁼ e α) a (const p₀) (const p₁))
      (R : SquareCell₌ (evaluate⁼ e β) b (const q₀) (const q₁))
      (Ψ : SquareCell₌ a b
        (const (changeEndpoints p₀ q₀ (evaluate-cong e σ₀)))
        (const (changeEndpoints p₁ q₁ (evaluate-cong e σ₁)))) where

      framed-matching-image :
        (evaluation-action e f₀ g₁ ∘ (const σ₁ ∙ α)) =₁
        (evaluation-action e f₀ g₁ ∘ (β ∙ const σ₀))
      framed-matching-image =
        (evaluation-action-evaluate e (β ∙ const σ₀)) ⁻¹ ∙
          ((target-image ⁻¹ ∙ (native-square ∙ source-image)) ∙
            evaluation-action-evaluate e (const σ₁ ∙ α))
        where
          transported : SquareCell₌ a b
            (changeEndpoints (const p₀) (const q₀) (const (evaluate-cong e σ₀)))
            (changeEndpoints (const p₁) (const q₁) (const (evaluate-cong e σ₁)))
          transported = replace-sides₌
            ((constant-endpoints p₀ q₀ (evaluate-cong e σ₀)) ⁻¹)
            ((constant-endpoints p₁ q₁ (evaluate-cong e σ₁)) ⁻¹) Ψ
          native-square : SquareCell₌ (evaluate⁼ e α) (evaluate⁼ e β)
            (const (evaluate-cong e σ₀)) (const (evaluate-cong e σ₁))
          native-square = reflect-transported-square
            (const p₀) (const q₀) (const p₁) (const q₁)
            (const (evaluate-cong e σ₀)) (const (evaluate-cong e σ₁))
            (evaluate⁼ e α) (evaluate⁼ e β) a b L R transported
          source-image : evaluate⁼ e (const σ₁ ∙ α) =₁
            (const (evaluate-cong e σ₁) ∙ evaluate⁼ e α)
          source-image = comp₌-cong (evaluate⁼-constant e σ₁) (id₌ (evaluate⁼ e α)) ∙
            evaluate⁼-composition e (const σ₁) α
          target-image : evaluate⁼ e (β ∙ const σ₀) =₁
            (evaluate⁼ e β ∙ const (evaluate-cong e σ₀))
          target-image = comp₌-cong (id₌ (evaluate⁼ e β)) (evaluate⁼-constant e σ₀) ∙
            evaluate⁼-composition e β (const σ₀)


private
  module _ {Γ : Context} {X : CAT Γ} where
    open Terms.Equalities X using (_＝_)
    constant-inverse-three : {A B : CAT Γ} {a b c d : MAP A B}
      (p : c =₁ d) (q : b =₁ d) (r : a =₁ b)
      → ((const {P = X} p) ⁻¹ ∙ (const q ∙ const r)) =₁
          const (p ⁻¹ ∙ (q ∙ r))
    constant-inverse-three p q r = const-comp (p ⁻¹) (q ∙ r) ∙
      comp₌-cong ((const-inv p) ⁻¹) (const-comp q r)

  module ChangeSpan {Γ : Context} {A B C A′ B′ C′ E : CAT Γ}
    (u : MAP A B) (l : MAP A C) (u′ : MAP A′ B′) (l′ : MAP A′ C′)
    (pA : MAP A′ A) (pB : MAP B′ B) (pC : MAP C′ C)
    (δu : (pB ∘ u′) =₁ (u ∘ pA)) (δl : (pC ∘ l′) =₁ (l ∘ pA)) where

    module Route {T T′ : CAT Γ} (f : MAP A T) (f′ : MAP A′ T′)
      (p : MAP T′ T) (δ : (p ∘ f′) =₁ (f ∘ pA)) where
      ρ : (h : MAP T E) → ((h ∘ p) ∘ f′) =₁ ((h ∘ f) ∘ pA)
      ρ h = (comp-assoc pA f h) ⁻¹ ∙ ((h ◁ δ) ∙ comp-assoc f′ p h)

      module _ {X : CAT Γ} where
        open Terms.Equalities X using (_＝_)
        natural : {h k : MAP T E} (α : h ＝ k)
          → SquareCell₌ ((α ▷ p) ▷ f′) ((α ▷ f) ▷ pA)
              (const (ρ h)) (const (ρ k))
        natural {h} {k} α = replace-sides₌
          (constant-inverse-three (comp-assoc pA f h) (h ◁ δ) (comp-assoc f′ p h))
          (constant-inverse-three (comp-assoc pA f k) (k ◁ δ) (comp-assoc f′ p k))
          (paste-square₌
            (paste-square₌ (preWhisker-comp α p f′) ((interchange-fixedInner α δ) ⁻¹))
            (inverse-square₌ (preWhisker-comp α f pA)))

    module L = Route u u′ pB δu
      using (natural; ρ)
    module R = Route l l′ pC δl
      using (natural; ρ)

    value : Cocone u l E → Cocone u′ l′ E
    value s = record
      { left = Cocone.left s ∘ pB
      ; right = Cocone.right s ∘ pC
      ; match = (R.ρ (Cocone.right s)) ⁻¹ ∙
          ((Cocone.match s ▷ pA) ∙ L.ρ (Cocone.left s)) }

    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)
      identification : {s t : Cocone u l E}
        → CoconeIdentification X s t → CoconeIdentification X (value s) (value t)
      identification {s} {t} Φ = record
        { left = CoconeIdentification.left Φ ▷ pB
        ; right = CoconeIdentification.right Φ ▷ pC
        ; compatible = replace-sides₌
            (constant-inverse-three (R.ρ (Cocone.right s))
              (Cocone.match s ▷ pA) (L.ρ (Cocone.left s)))
            (constant-inverse-three (R.ρ (Cocone.right t))
              (Cocone.match t ▷ pA) (L.ρ (Cocone.left t)))
            (paste-square₌
              (paste-square₌ (L.natural (CoconeIdentification.left Φ))
                (replace-sides₌ (pre-constant (Cocone.match s) pA)
                  (pre-constant (Cocone.match t) pA)
                  (pre-square₌ pA (CoconeIdentification.compatible Φ))))
              (inverse-square₌ (R.natural (CoconeIdentification.right Φ)))) }

-- REVIEW ONLY: actual ChangeSpan commutes with fixed postcomposition.
-- Uses private ChangeSpan from the native owner; no new chosen reverse cells.
private
  module _ {Γ : Context} {A B C A′ B′ C′ T E : CAT Γ}
    (u : MAP A B) (l : MAP A C) (u′ : MAP A′ B′) (l′ : MAP A′ C′)
    (pA : MAP A′ A) (pB : MAP B′ B) (pC : MAP C′ C)
    (δu : (pB ∘ u′) =₁ (u ∘ pA)) (δl : (pC ∘ l′) =₁ (l ∘ pA))
    (H : MAP T E) (s : Cocone u l T) where
    private
      module Before = ChangeSpan {E = T} u l u′ l′ pA pB pC δu δl
        using (value; module L; module R)
      module After = ChangeSpan {E = E} u l u′ l′ pA pB pC δu δl
        using (value; module L; module R)
      x = Cocone.left s
      y = Cocone.right s
      σ = Cocone.match s
      ρx = Before.L.ρ x
      ρy = Before.R.ρ y
      hx = After.L.ρ (H ∘ x)
      hy = After.R.ρ (H ∘ y)
      nx = post-square-cell H pA (x ∘ u) (x ∘ pB) u′ ρx
      ny = post-square-cell H pA (y ∘ l) (y ∘ pC) l′ ρy
      ηx = comp-assoc u x H
      ηy = comp-assoc l y H
      ζx = comp-assoc pA (x ∘ u) H
      ζy = comp-assoc pA (y ∘ l) H
      ωx = comp-assoc u′ (x ∘ pB) H
      ωy = comp-assoc l′ (y ∘ pC) H
      λx = comp-assoc pB x H
      λy = comp-assoc pC y H
      q₀ = Cocone.match (cocone-postcompose H s) ▷ pA
      q₁ = (H ◁ σ) ▷ pA
      q₂ = H ◁ (σ ▷ pA)

      -- Congruence retains both endpoint changes and the entire middle edge.
      endpoints-cong : {K Z : CAT Γ} {a b a′ b′ : MAP K Z}
        {p p′ : a =₁ a′} {q q′ : b =₁ b′} {α α′ : a =₁ b}
        → p =₂ p′ → q =₂ q′ → α =₂ α′
        → changeEndpoints p q α =₂ changeEndpoints p′ q′ α′
      endpoints-cong dp dq dα = comp₌-cong dq (comp₌-cong dα (inv₌ ◁ dp))

      source-normal : changeEndpoints (hx ⁻¹) (hy ⁻¹) q₀
        =₂ Cocone.match (After.value (cocone-postcompose H s))
      source-normal = comp₌-cong (id₌ (hy ⁻¹))
        (comp₌-cong (id₌ q₀) (inverse-inverse hx))
      original-normal : changeEndpoints (ρx ⁻¹) (ρy ⁻¹) (σ ▷ pA)
        =₂ Cocone.match (Before.value s)
      original-normal = comp₌-cong (id₌ (ρy ⁻¹))
        (comp₌-cong (id₌ (σ ▷ pA)) (inverse-inverse ρx))
      mixed-normal : changeEndpoints ζx ζy q₁ =₂ q₂
      mixed-normal = square-to-changeEndpoints ζx ζy q₁ q₂
        (whisker-mixed-One σ pA H)
      middle-normal : changeEndpoints ((H ◁ ρx) ⁻¹) ((H ◁ ρy) ⁻¹) q₂
        =₂ H ◁ Cocone.match (Before.value s)
      middle-normal = (postWhisker H ◁ original-normal) ∙
        (endpoints-cong (postWhisker-inverse H ρx) (postWhisker-inverse H ρy)
          (id₌ q₂) ∙ postWhisker-changeEndpoints H (ρx ⁻¹) (ρy ⁻¹) (σ ▷ pA)) ⁻¹
      final-normal : changeEndpoints (ωx ⁻¹) (ωy ⁻¹)
          (H ◁ Cocone.match (Before.value s))
        =₂ Cocone.match (cocone-postcompose H (Before.value s))
      final-normal = comp₌-cong (id₌ (ωy ⁻¹))
        (comp₌-cong (id₌ (H ◁ Cocone.match (Before.value s))) (inverse-inverse ωx))

      left-inverse : nx ⁻¹ =₂ ((ωx ⁻¹ ∙ (H ◁ ρx) ⁻¹) ∙ ζx)
      left-inverse = (comp₌-cong (inverse-composite (H ◁ ρx) ωx) (inverse-inverse ζx) ∙
          inverse-composite (ζx ⁻¹) ((H ◁ ρx) ∙ ωx))
      right-inverse : ny ⁻¹ =₂ ((ωy ⁻¹ ∙ (H ◁ ρy) ⁻¹) ∙ ζy)
      right-inverse = (comp₌-cong (inverse-composite (H ◁ ρy) ωy) (inverse-inverse ζy) ∙
          inverse-composite (ζy ⁻¹) ((H ◁ ρy) ∙ ωy))
      iterated-normal :
        changeEndpoints (ωx ⁻¹) (ωy ⁻¹)
          (changeEndpoints ((H ◁ ρx) ⁻¹) ((H ◁ ρy) ⁻¹)
            (changeEndpoints ζx ζy q₁))
        =₂ changeEndpoints (nx ⁻¹) (ny ⁻¹) q₁
      iterated-normal = endpoints-cong (left-inverse ⁻¹) (right-inverse ⁻¹) (id₌ q₁) ∙
        (changeEndpoints-iterated ζx ζy
          (ωx ⁻¹ ∙ (H ◁ ρx) ⁻¹) (ωy ⁻¹ ∙ (H ◁ ρy) ⁻¹) q₁ ∙
          changeEndpoints-iterated ((H ◁ ρx) ⁻¹) ((H ◁ ρy) ⁻¹)
            (ωx ⁻¹) (ωy ⁻¹) (changeEndpoints ζx ζy q₁))
      target-normal : changeEndpoints (nx ⁻¹) (ny ⁻¹) q₁
        =₂ Cocone.match (cocone-postcompose H (Before.value s))
      target-normal = final-normal ∙
        (endpoints-cong (id₌ (ωx ⁻¹)) (id₌ (ωy ⁻¹)) middle-normal ∙
          (endpoints-cong (id₌ (ωx ⁻¹)) (id₌ (ωy ⁻¹))
            (endpoints-cong (id₌ ((H ◁ ρx) ⁻¹)) (id₌ ((H ◁ ρy) ⁻¹)) mixed-normal) ∙
            iterated-normal ⁻¹))

      raw-middle : SquareCell₌ ηx ηy (Cocone.match (cocone-postcompose H s)) (H ◁ σ)
      raw-middle = (comp-inv-left ηy ((H ◁ σ) ∙ ηx)) ⁻¹
      raw-square : SquareCell₌ (λx ▷ u′) (λy ▷ l′)
        (changeEndpoints (hx ⁻¹) (hy ⁻¹) q₀)
        (changeEndpoints (nx ⁻¹) (ny ⁻¹) q₁)
      raw-square = transport-square (hx ⁻¹) (nx ⁻¹) (hy ⁻¹) (ny ⁻¹)
        q₀ q₁ (ηx ▷ pA) (ηy ▷ pA) (λx ▷ u′) (λy ▷ l′)
        (inverse-square₌ (post-square-cell-comp pA u pB u′ δu x H))
        (inverse-square₌ (post-square-cell-comp pA l pC l′ δl y H))
        (pre-square₌ pA raw-middle)
    change-span-postcomposition : CoconeIdentification₁
      (After.value (cocone-postcompose H s)) (cocone-postcompose H (Before.value s))
    change-span-postcomposition = record
      { left = λx
      ; right = λy
      ; compatible = replace-sides₌ source-normal target-normal raw-square }

-- Direct owners added at assembly: Coherence.inv₌, Triangles.post-square-cell/comp,
-- EndpointTransport.iterated/square-to-changeEndpoints/postWhisker-changeEndpoints,
-- FunctorCoherence.whisker-mixed-One. All proofs remain private and finite.

-- REVIEW ONLY: whole cocone unit and associativity, selected components.
private
  module _ {Γ : Context} {A B C T : CAT Γ} {u : MAP A B} {l : MAP A C}
    (s : Cocone u l T) where
    postcompose-unit : CoconeIdentification₁ (cocone-postcompose (id T) s) s
    postcompose-unit = record
      { left = comp-unitˡ (Cocone.left s)
      ; right = comp-unitˡ (Cocone.right s)
      ; compatible = (post-square-cell-id l (Cocone.right s) (Cocone.left s)
          u (Cocone.match s)) ⁻¹ }

    postcompose-assoc : {E Z : CAT Γ} (g : MAP T E) (f : MAP E Z)
      → CoconeIdentification₁ (cocone-postcompose (f ∘ g) s)
          (cocone-postcompose f (cocone-postcompose g s))
    postcompose-assoc g f = record
      { left = comp-assoc (Cocone.left s) g f
      ; right = comp-assoc (Cocone.right s) g f
      ; compatible = post-square-cell-comp l (Cocone.right s) (Cocone.left s)
          u (Cocone.match s) g f }

-- Both matching equations are the actual post-square-cell calculations;
-- unit uses the inverse of the stated scalar unit equation. No leg-only unit.

-- REVIEW ONLY: fixed postcomposition acts on whole scalar cocone identifications.
private
  module _ {Γ : Context} {A B C T E : CAT Γ} {u : MAP A B} {l : MAP A C}
    (H : MAP T E) {s t : Cocone u l T} (Φ : CoconeIdentification₁ s t) where
    private
      α = CoconeIdentification₁.left Φ
      β = CoconeIdentification₁.right Φ
      fs = (comp-assoc u (Cocone.left s) H) ⁻¹
      ft = (comp-assoc u (Cocone.left t) H) ⁻¹
      gs = (comp-assoc l (Cocone.right s) H) ⁻¹
      gt = (comp-assoc l (Cocone.right t) H) ⁻¹
      σs = H ◁ Cocone.match s
      σt = H ◁ Cocone.match t
      matching-normal : (z : Cocone u l T)
        → changeEndpoints ((comp-assoc u (Cocone.left z) H) ⁻¹)
            ((comp-assoc l (Cocone.right z) H) ⁻¹) (H ◁ Cocone.match z)
          =₂ Cocone.match (cocone-postcompose H z)
      matching-normal z = comp₌-cong (id₌ ((comp-assoc l (Cocone.right z) H) ⁻¹))
        (comp₌-cong (id₌ (H ◁ Cocone.match z))
          (inverse-inverse (comp-assoc u (Cocone.left z) H)))
    fixed-postcomposition : CoconeIdentification₁
      (cocone-postcompose H s) (cocone-postcompose H t)
    fixed-postcomposition = record
      { left = H ◁ α
      ; right = H ◁ β
      ; compatible = replace-sides₌ (matching-normal s) (matching-normal t)
          (transport-square fs ft gs gt σs σt
            (H ◁ (α ▷ u)) (H ◁ (β ▷ l)) ((H ◁ α) ▷ u) ((H ◁ β) ▷ l)
            (inverse-square₌ (whisker-mixed-One α u H))
            (inverse-square₌ (whisker-mixed-One β l H))
            (post-square₌ H (CoconeIdentification₁.compatible Φ))) }
-- Direct owners: EndpointTransport.transport-square; FunctorCoherence.whisker-mixed-One.

-- REVIEW ONLY: recover an entire cocone identification through an equivalence.
-- Private terminal-adapter calculation; retains its chosen reflection factors.
private
  module CoconePostcompositionRecovery {Γ : Context} {X A B C T E : CAT Γ}
    {u : MAP A B} {l : MAP A C} (H : MAP T E) (hEquiv : IsEquiv H)
    (s t : Cocone u l T)
    (Φ : CoconeIdentification X (cocone-postcompose H s) (cocone-postcompose H t)) where
    open Terms.Equalities X using (_＝_)
    private
      left-factor = factor-through-postWhisker H hEquiv (CoconeIdentification.left Φ)
      right-factor = factor-through-postWhisker H hEquiv (CoconeIdentification.right Φ)
    left : Cocone.left s ＝ Cocone.left t
    left = Fact.factor left-factor
    right : Cocone.right s ＝ Cocone.right t
    right = Fact.factor right-factor
    left-image : (H ◁ left) =₁ CoconeIdentification.left Φ
    left-image = Fact.triangle left-factor
    right-image : (H ◁ right) =₁ CoconeIdentification.right Φ
    right-image = Fact.triangle right-factor
    private
      frame-left : (z : Cocone u l T)
        → (H ∘ (Cocone.left z ∘ u)) =₁ ((H ∘ Cocone.left z) ∘ u)
      frame-left z = (comp-assoc u (Cocone.left z) H) ⁻¹
      frame-right : (z : Cocone u l T)
        → (H ∘ (Cocone.right z ∘ l)) =₁ ((H ∘ Cocone.right z) ∘ l)
      frame-right z = (comp-assoc l (Cocone.right z) H) ⁻¹
      fs = const {P = X} (frame-left s)
      gs = const {P = X} (frame-right s)
      ft = const {P = X} (frame-left t)
      gt = const {P = X} (frame-right t)
      σs = H ◁ const {P = X} (Cocone.match s)
      σt = H ◁ const {P = X} (Cocone.match t)
      raw-left = H ◁ (left ▷ u)
      raw-right = H ◁ (right ▷ l)
      middle-left = (H ◁ left) ▷ u
      middle-right = (H ◁ right) ▷ l

      matching-frame : (z : Cocone u l T)
        → changeEndpoints (const {P = X} (frame-left z)) (const (frame-right z))
            (H ◁ const (Cocone.match z)) =₁ const (Cocone.match (cocone-postcompose H z))
      matching-frame z = const-cong
        (comp₌-cong (id₌ (frame-right z))
          (comp₌-cong (id₌ (H ◁ Cocone.match z))
            (inverse-inverse (comp-assoc u (Cocone.left z) H)))) ∙
        (constant-endpoints (frame-left z) (frame-right z) (H ◁ Cocone.match z) ∙
          comp₌-cong (id₌ (const (frame-right z)))
            (comp₌-cong (post-constant H (Cocone.match z))
              (id₌ ((const (frame-left z)) ⁻¹))))

      left-square : SquareCell₌ raw-left middle-left fs ft
      left-square = replace-sides₌
        ((const-inv (comp-assoc u (Cocone.left s) H)) ⁻¹)
        ((const-inv (comp-assoc u (Cocone.left t) H)) ⁻¹)
        (inverse-square₌ (whisker-mixed left u H))
      right-square : SquareCell₌ raw-right middle-right gs gt
      right-square = replace-sides₌
        ((const-inv (comp-assoc l (Cocone.right s) H)) ⁻¹)
        ((const-inv (comp-assoc l (Cocone.right t) H)) ⁻¹)
        (inverse-square₌ (whisker-mixed right l H))
      transported : SquareCell₌ middle-left middle-right
        (changeEndpoints fs gs σs) (changeEndpoints ft gt σt)
      transported = replace-sides₌ ((matching-frame s) ⁻¹) ((matching-frame t) ⁻¹)
        (replace-edges₌ ((preWhisker u ◁ left-image) ⁻¹)
          ((preWhisker l ◁ right-image) ⁻¹) (CoconeIdentification.compatible Φ))
      native-square : SquareCell₌ raw-left raw-right σs σt
      native-square = reflect-transported-square fs gs ft gt σs σt
        raw-left raw-right middle-left middle-right left-square right-square transported

    source-boundary = const {P = X} (Cocone.match t) ∙ (left ▷ u)
    target-boundary = (right ▷ l) ∙ const {P = X} (Cocone.match s)
    private
      source-image = postWhisker-comp₌ H (const (Cocone.match t)) (left ▷ u)
      target-image = postWhisker-comp₌ H (right ▷ l) (const (Cocone.match s))
      wanted-image : (H ◁ source-boundary) =₁ (H ◁ target-boundary)
      wanted-image = target-image ⁻¹ ∙ (native-square ∙ source-image)
    matching-factor = factor-through-postWhisker₂ H hEquiv source-boundary target-boundary wanted-image
    compatible : SquareCell₌ (left ▷ u) (right ▷ l)
      (const (Cocone.match s)) (const (Cocone.match t))
    compatible = Fact.factor matching-factor
    matching-image : ((postWhisker (postWhisker H)) ∘ compatible) =₁ wanted-image
    matching-image = Fact.triangle matching-factor
    value : CoconeIdentification X s t
    value = record { left = left; right = right; compatible = compatible }

-- Reuses existing private constant-endpoints in the native owner.
-- Direct owners: WhiskeringEquivalence.factor-through-postWhisker₂,
-- Whiskering.whisker-mixed, EndpointTransport.reflect-transported-square.

private
  module RecoveredSpanCell {Γ : Context} {A A′ B B′ : CAT Γ}
    (J : MAP A B) (H : MAP A′ B′)
    (pA : MAP A′ A) (pB : MAP B′ B) (qA : MAP A A′) (qB : MAP B B′)
    (εA : (pA ∘ qA) =₁ id A) (εB : (pB ∘ qB) =₁ id B)
    (pBEquiv : IsEquiv pB) (transpose-cell : (pB ∘ H) =₁ (J ∘ pA)) where
    reverse-image : (pB ∘ (qB ∘ J)) =₁ (pB ∘ (H ∘ qA))
    reverse-image = comp-assoc qA H pB ∙
      ((transpose-cell ⁻¹ ▷ qA) ∙
        ((comp-assoc qA pA J) ⁻¹ ∙
          ((J ◁ εA ⁻¹) ∙
            ((comp-unitʳ J) ⁻¹ ∙
              (comp-unitˡ J ∙ ((εB ▷ J) ∙ (comp-assoc J qB pB) ⁻¹))))))
    reverse-factor : Fact.Factorization (postWhisker pB) reverse-image
    reverse-factor = factor-through-postWhisker pB pBEquiv reverse-image
    reverse-cell : (qB ∘ J) =₁ (H ∘ qA)
    reverse-cell = Fact.factor reverse-factor
    reverse-cell-image : (pB ◁ reverse-cell) =₂ reverse-image
    reverse-cell-image = Fact.triangle reverse-factor

    private
      module _ {C D : CAT Γ} {w x y z : MAP C D} where
        strip-left : (p : y =₁ z) (t : x =₁ y) (r : w =₁ x)
          → (p ⁻¹ ∙ ((p ∙ t) ∙ r)) =₂ (t ∙ r)
        strip-left p t r = comp₌-cong (inv-comp-left p t) (id₌ r) ∙
          (comp₌-assoc (p ⁻¹) (p ∙ t) r) ⁻¹
        strip-inverse : (p : y =₁ z) (t : x =₁ z) (r : w =₁ x)
          → (p ∙ ((p ⁻¹ ∙ t) ∙ r)) =₂ (t ∙ r)
        strip-inverse p t r = comp₌-cong (comp-inv-left p t) (id₌ r) ∙
          (comp₌-assoc p (p ⁻¹ ∙ t) r) ⁻¹

      source-assoc = comp-assoc J qB pB
      target-assoc = comp-assoc qA H pB
      middle = transpose-cell ▷ qA
      corner-assoc = comp-assoc qA pA J
      unit = J ◁ εA
      right-unit = comp-unitʳ J
      left-unit = comp-unitˡ J
      source-unit = εB ▷ J
      desired = left-unit ∙ source-unit
      tail₄ = desired ∙ source-assoc ⁻¹
      tail₃ = right-unit ⁻¹ ∙ tail₄
      tail₂ = unit ⁻¹ ∙ tail₃
      tail₁ = corner-assoc ⁻¹ ∙ tail₂
      tail₀ = middle ⁻¹ ∙ tail₁
      normalized = target-assoc ∙ tail₀
      normalized-image : (pB ◁ reverse-cell) =₂ normalized
      normalized-image = comp₌-cong (id₌ target-assoc)
        (comp₌-cong (preWhisker-inverse transpose-cell qA)
          (comp₌-cong (id₌ (corner-assoc ⁻¹))
            (comp₌-cong (postWhisker-inverse J εA)
              (comp₌-cong (id₌ (right-unit ⁻¹))
                ((comp₌-assoc left-unit source-unit (source-assoc ⁻¹)) ⁻¹))))) ∙
        reverse-cell-image

    Ω : ((pB ∘ qB) ∘ J) =₁ (J ∘ (pA ∘ qA))
    Ω = corner-assoc ∙
      (middle ∙ (target-assoc ⁻¹ ∙ ((pB ◁ reverse-cell) ∙ source-assoc)))
    composed-cell-compatible :
      (comp-unitʳ J ∙ ((J ◁ εA) ∙ Ω)) =₂ (comp-unitˡ J ∙ (εB ▷ J))
    composed-cell-compatible =
      inv-comp-right desired source-assoc ∙
      (strip-inverse right-unit tail₄ source-assoc ∙
      (comp₌-cong (id₌ right-unit) (strip-inverse unit tail₃ source-assoc) ∙
      (comp₌-cong (id₌ right-unit)
        (comp₌-cong (id₌ unit) (strip-inverse corner-assoc tail₂ source-assoc)) ∙
      (comp₌-cong (id₌ right-unit)
        (comp₌-cong (id₌ unit)
          (comp₌-cong (id₌ corner-assoc) (strip-inverse middle tail₁ source-assoc))) ∙
      (comp₌-cong (id₌ right-unit)
        (comp₌-cong (id₌ unit)
          (comp₌-cong (id₌ corner-assoc)
            (comp₌-cong (id₌ middle) (strip-left target-assoc tail₀ source-assoc)))) ∙
      comp₌-cong (id₌ right-unit)
        (comp₌-cong (id₌ unit)
          (comp₌-cong (id₌ corner-assoc)
            (comp₌-cong (id₌ middle)
              (comp₌-cong (id₌ (target-assoc ⁻¹))
                (comp₌-cong normalized-image (id₌ source-assoc)))))))))))

    private
      restored-source = desired ∙ source-assoc ⁻¹
      restored-target = right-unit ∙ (unit ∙ corner-assoc)
      restricted = middle ∙ target-assoc ⁻¹
      image = pB ◁ reverse-cell
      joined = restored-target ∙ (restricted ∙ image)
      nested = middle ∙ (target-assoc ⁻¹ ∙ (image ∙ source-assoc))
      expand-boundary : (joined ∙ source-assoc) =₂ (right-unit ∙ (unit ∙ Ω))
      expand-boundary = comp₌-cong (id₌ right-unit)
          (comp₌-assoc unit corner-assoc nested) ∙
        (comp₌-assoc right-unit (unit ∙ corner-assoc) nested ∙
        (comp₌-cong (id₌ restored-target)
          (comp₌-assoc middle (target-assoc ⁻¹) (image ∙ source-assoc)) ∙
        (comp₌-cong (id₌ restored-target)
          (comp₌-assoc restricted image source-assoc) ∙
          comp₌-assoc restored-target (restricted ∙ image) source-assoc)))
      joined-image : joined =₂ restored-source
      joined-image = comp₌-cong (composed-cell-compatible ∙ expand-boundary)
        (id₌ (source-assoc ⁻¹)) ∙ (comp-inv-right joined source-assoc) ⁻¹
      split-image : ((restored-target ∙ restricted) ∙ image) =₂ restored-source
      split-image = joined-image ∙ comp₌-assoc restored-target restricted image
      recovered-span-square : SquareCell₌ (pB ◁ reverse-cell ⁻¹) restored-target
        (restrict-triangle pB H transpose-cell qA) restored-source
      recovered-span-square = comp-inv-right (restored-target ∙ restricted) image ∙
        (comp₌-cong (split-image ⁻¹) (id₌ (image ⁻¹)) ∙
          comp₌-cong (id₌ restored-source) (postWhisker-inverse pB reverse-cell))

    post-recovered-span : {E : CAT Γ} (h : MAP B E)
      → (post-triangle h pB (qB ∘ J) restored-source ∙
          (((h ∘ pB) ◁ reverse-cell ⁻¹) ∙ comp-assoc qA H (h ∘ pB))) =₂
        ((h ◁ restored-target) ∙
          (comp-assoc qA (J ∘ pA) h ∙ (post-triangle h pB H transpose-cell ▷ qA)))
    post-recovered-span h = post-triangle-change h pB H qA (qB ∘ J)
      (reverse-cell ⁻¹) transpose-cell restored-source restored-target recovered-span-square

    corner-β : {E : CAT Γ} (h : MAP B E) → ((h ∘ pB) ∘ qB) =₁ h
    corner-β h = comp-unitʳ h ∙ post-triangle h pB qB εB

    corner-β-restrict : {E : CAT Γ} (h : MAP B E)
      → (post-triangle h pB (qB ∘ J) restored-source ∙ comp-assoc J qB (h ∘ pB)) =₂
          (corner-β h ▷ J)
    corner-β-restrict h = (preWhisker-comp₌ (comp-unitʳ h) (post-triangle h pB qB εB) J) ⁻¹ ∙
      (comp₌-cong ((triangle-whiskered J h) ⁻¹) (id₌ (post-triangle h pB qB εB ▷ J)) ∙
      ((comp₌-assoc (h ◁ left-unit) (comp-assoc J (id B) h)
        (post-triangle h pB qB εB ▷ J)) ⁻¹ ∙
      (post-restrict-triangle h pB qB J εB left-unit ∙
      (comp₌-cong
        (postWhisker h ◁ comp₌-assoc left-unit source-unit (source-assoc ⁻¹))
        (id₌ (comp-assoc (qB ∘ J) pB h ∙ comp-assoc J qB (h ∘ pB))) ∙
        comp₌-assoc (h ◁ restored-source) (comp-assoc (qB ∘ J) pB h)
          (comp-assoc J qB (h ∘ pB))))))

    source-corner-β : {E : CAT Γ} (h : MAP B E)
      → (((h ∘ J) ∘ pA) ∘ qA) =₁ (h ∘ J)
    source-corner-β h = comp-unitʳ (h ∘ J) ∙ post-triangle (h ∘ J) pA qA εA
    forward-frame : {E : CAT Γ} (h : MAP B E)
      → ((h ∘ pB) ∘ H) =₁ ((h ∘ J) ∘ pA)
    forward-frame h = (comp-assoc pA J h) ⁻¹ ∙ post-triangle h pB H transpose-cell
    reverse-frame : {E : CAT Γ} (h : MAP B E)
      → (((h ∘ pB) ∘ qB) ∘ J) =₁ (((h ∘ pB) ∘ H) ∘ qA)
    reverse-frame h = (comp-assoc qA H (h ∘ pB)) ⁻¹ ∙
      post-triangle (h ∘ pB) qB J reverse-cell

    private
      module FrameCalculation {E : CAT Γ} (h : MAP B E) where
        L = h ◁ restored-target
        B₀ = comp-assoc qA (J ∘ pA) h
        A₀ = comp-assoc pA J h ▷ qA
        t = post-triangle h pB H transpose-cell ▷ qA
        Q = comp-assoc qA H (h ∘ pB)
        S = comp-assoc J qB (h ∘ pB)
        M = (h ∘ pB) ◁ reverse-cell
        tail = ((h ∘ pB) ◁ reverse-cell ⁻¹) ∙ Q
        known = post-triangle h pB (qB ∘ J) restored-source

        source-corner-post : source-corner-β h =₂ (L ∙ (B₀ ∙ A₀))
        source-corner-post = comp₌-cong
          ((postWhisker-comp₌ h right-unit (post-triangle J pA qA εA)) ⁻¹)
          (id₌ (B₀ ∙ A₀)) ∙
          ((comp₌-assoc (h ◁ right-unit) (h ◁ post-triangle J pA qA εA) (B₀ ∙ A₀)) ⁻¹ ∙
          (comp₌-cong (id₌ (h ◁ right-unit)) (post-triangle-comp h J pA qA εA) ∙
          (comp₌-assoc (h ◁ right-unit) (comp-assoc (id A) J h)
            (post-triangle (h ∘ J) pA qA εA) ∙
            comp₌-cong (right-unitor-comp J h) (id₌ (post-triangle (h ∘ J) pA qA εA)))))

        forward-normal : (forward-frame h ▷ qA) =₂ (A₀ ⁻¹ ∙ t)
        forward-normal = comp₌-cong (preWhisker-inverse (comp-assoc pA J h) qA) (id₌ t) ∙
          preWhisker-comp₌ ((comp-assoc pA J h) ⁻¹) (post-triangle h pB H transpose-cell) qA
        source-forward-normal : (source-corner-β h ∙ (forward-frame h ▷ qA)) =₂ (L ∙ (B₀ ∙ t))
        source-forward-normal = comp₌-cong (id₌ L)
          (comp₌-cong (id₌ B₀) (comp-inv-left A₀ t)) ∙
          (comp₌-cong (id₌ L) (comp₌-assoc B₀ A₀ (A₀ ⁻¹ ∙ t)) ∙
          (comp₌-assoc L (B₀ ∙ A₀) (A₀ ⁻¹ ∙ t) ∙
            comp₌-cong source-corner-post forward-normal))

        reverse-inverse : (reverse-frame h) ⁻¹ =₂ (S ⁻¹ ∙ tail)
        reverse-inverse = comp₌-cong (id₌ (S ⁻¹))
          (comp₌-cong ((postWhisker-inverse (h ∘ pB) reverse-cell) ⁻¹) (id₌ Q)) ∙
          (comp₌-assoc (S ⁻¹) (M ⁻¹) Q ∙
          (comp₌-cong (inverse-composite M S) (inverse-inverse Q) ∙
            inverse-composite (Q ⁻¹) (M ∙ S)))
        left-normal : ((corner-β h ▷ J) ∙ (reverse-frame h) ⁻¹) =₂ (known ∙ tail)
        left-normal = comp₌-cong (id₌ known) (comp-inv-left S tail) ∙
          (comp₌-assoc known S (S ⁻¹ ∙ tail) ∙
            comp₌-cong ((corner-β-restrict h) ⁻¹) reverse-inverse)
        post-comparison : ((corner-β h ▷ J) ∙ (reverse-frame h) ⁻¹) =₂
          (source-corner-β h ∙ (forward-frame h ▷ qA))
        post-comparison = source-forward-normal ⁻¹ ∙ (post-recovered-span h ∙ left-normal)

    combined-frame : {E : CAT Γ} (h : MAP B E)
      → (source-corner-β h ∙ ((forward-frame h ▷ qA) ∙ reverse-frame h)) =₂ (corner-β h ▷ J)
    combined-frame h = inv-comp-right (corner-β h ▷ J) (reverse-frame h) ∙
      (comp₌-cong ((FrameCalculation.post-comparison h) ⁻¹) (id₌ (reverse-frame h)) ∙
        (comp₌-assoc (source-corner-β h) (forward-frame h ▷ qA) (reverse-frame h)) ⁻¹)

private
  module CornerRestriction {Γ : Context} {A A′ E : CAT Γ}
    (p : MAP A′ A) (q : MAP A A′) (ε : (p ∘ q) =₁ id A) where
    β : (h : MAP A E) → ((h ∘ p) ∘ q) =₁ h
    β h = comp-unitʳ h ∙ ((h ◁ ε) ∙ comp-assoc q p h)
    module _ {X : CAT Γ} where
      open Terms.Equalities X using (_＝_)
      private
        constant-three : {C D : CAT Γ} {w x y z : MAP C D}
          (c : y =₁ z) (b : x =₁ y) (a : w =₁ x)
          → (const {P = X} c ∙ (const b ∙ const a)) =₁ const (c ∙ (b ∙ a))
        constant-three c b a = const-comp c (b ∙ a) ∙
          comp₌-cong (id₌ (const c)) (const-comp b a)
      natural : {h k : MAP A E} (α : h ＝ k)
        → SquareCell₌ ((α ▷ p) ▷ q) α (const (β h)) (const (β k))
      natural {h} {k} α = replace-sides₌
        (constant-three (comp-unitʳ h) (h ◁ ε) (comp-assoc q p h))
        (constant-three (comp-unitʳ k) (k ◁ ε) (comp-assoc q p k))
        (paste-square₌
          (paste-square₌ (preWhisker-comp α p q) ((interchange-fixedInner α ε) ⁻¹))
          (preWhisker-id α))

  module CoconeSpanRetraction {Γ : Context} {A A′ B B′ C C′ E : CAT Γ}
    (u : MAP A B) (l : MAP A C) (u′ : MAP A′ B′) (l′ : MAP A′ C′)
    (pA : MAP A′ A) (pB : MAP B′ B) (pC : MAP C′ C)
    (qA : MAP A A′) (qB : MAP B B′) (qC : MAP C C′)
    (εA : (pA ∘ qA) =₁ id A) (εB : (pB ∘ qB) =₁ id B) (εC : (pC ∘ qC) =₁ id C)
    (pBEquiv : IsEquiv pB) (pCEquiv : IsEquiv pC)
    (δu : (pB ∘ u′) =₁ (u ∘ pA)) (δl : (pC ∘ l′) =₁ (l ∘ pA)) where
    private
      module U = RecoveredSpanCell u u′ pA pB qA qB εA εB pBEquiv δu
        using (combined-frame; corner-β; forward-frame; reverse-cell; reverse-frame; source-corner-β)
      module L = RecoveredSpanCell l l′ pA pC qA qC εA εC pCEquiv δl
        using (combined-frame; corner-β; forward-frame; reverse-cell; reverse-frame; source-corner-β)
      module Forward = ChangeSpan {E = E} u l u′ l′ pA pB pC δu δl
        using (identification; value)
      module Back = ChangeSpan {E = E} u′ l′ u l qA qB qC U.reverse-cell L.reverse-cell
        using (identification; value)
      module Corner = CornerRestriction {E = E} pA qA εA
        using (natural)
    forward : Cocone u l E → Cocone u′ l′ E
    forward = Forward.value
    back : Cocone u′ l′ E → Cocone u l E
    back = Back.value

    back-postcomposition : {Z : CAT Γ} (H : MAP E Z) (s : Cocone u′ l′ E)
      → CoconeIdentification₁
          (ChangeSpan.value {E = Z} u′ l′ u l qA qB qC U.reverse-cell L.reverse-cell
            (cocone-postcompose H s))
          (cocone-postcompose H (back s))
    back-postcomposition H s = change-span-postcomposition
      u′ l′ u l qA qB qC U.reverse-cell L.reverse-cell H s

    forward-identification : {X : CAT Γ} {s t : Cocone u l E}
      → CoconeIdentification X s t → CoconeIdentification X (forward s) (forward t)
    forward-identification = Forward.identification
    back-identification : {X : CAT Γ} {s t : Cocone u′ l′ E}
      → CoconeIdentification X s t → CoconeIdentification X (back s) (back t)
    back-identification = Back.identification
    twice : Cocone u l E → Cocone u l E
    twice s = back (forward s)

    module Calculation (s : Cocone u l E) where
      private
        h = Cocone.left s
        k = Cocone.right s
        σ = Cocone.match s
        lT = U.forward-frame h
        rT = L.forward-frame k
        lB = U.reverse-frame h
        rB = L.reverse-frame k
        lT′ = lT ▷ qA
        rT′ = rT ▷ qA
        raw = (σ ▷ pA) ▷ qA
        combined-left = lT′ ∙ lB
        combined-right = rT′ ∙ rB
        left-source = U.source-corner-β h
        right-source = L.source-corner-β k
        left-target = U.corner-β h ▷ u
        right-target = L.corner-β k ▷ l
        tail = raw ∙ combined-left

        match-whisker : (Cocone.match (Forward.value s) ▷ qA) =₂
          (rT′ ⁻¹ ∙ (raw ∙ lT′))
        match-whisker = comp₌-cong (preWhisker-inverse rT qA)
          (preWhisker-comp₌ (σ ▷ pA) lT qA) ∙
          preWhisker-comp₌ (rT ⁻¹) ((σ ▷ pA) ∙ lT) qA
        matching-normal : Cocone.match (twice s) =₂ (combined-right ⁻¹ ∙ tail)
        matching-normal = comp₌-cong ((inverse-composite rT′ rB) ⁻¹) (id₌ tail) ∙
          ((comp₌-assoc (rB ⁻¹) (rT′ ⁻¹) tail) ⁻¹ ∙
          (comp₌-cong (id₌ (rB ⁻¹))
            (comp₌-cong (id₌ (rT′ ⁻¹)) (comp₌-assoc raw lT′ lB)) ∙
          (comp₌-cong (id₌ (rB ⁻¹)) (comp₌-assoc (rT′ ⁻¹) (raw ∙ lT′) lB) ∙
            comp₌-cong (id₌ (rB ⁻¹)) (comp₌-cong match-whisker (id₌ lB)))))
        corner-square : SquareCell₌ raw σ left-source right-source
        corner-square = unconst-sides₌ (Corner.natural {X = One} σ)
        left-normal : (σ ∙ left-target) =₂ (right-source ∙ tail)
        left-normal = comp₌-assoc right-source raw combined-left ∙
          (comp₌-cong (corner-square ⁻¹) (id₌ combined-left) ∙
          ((comp₌-assoc σ left-source combined-left) ⁻¹ ∙
            comp₌-cong (id₌ σ) ((U.combined-frame h) ⁻¹)))
        right-normal : (right-target ∙ Cocone.match (twice s)) =₂ (right-source ∙ tail)
        right-normal = comp₌-cong (id₌ right-source) (comp-inv-left combined-right tail) ∙
          (comp₌-assoc right-source combined-right (combined-right ⁻¹ ∙ tail) ∙
            comp₌-cong ((L.combined-frame k) ⁻¹) matching-normal)
      comparison : CoconeIdentification₁ (twice s) s
      comparison = record
        { left = U.corner-β h
        ; right = L.corner-β k
        ; compatible = right-normal ⁻¹ ∙ left-normal }

private
  module SwapRestriction {Γ : Context} {P A B : CAT Γ} (f : MAP A B) where
    J : MAP (P × A) (P × B)
    J = product-restriction f
    H : MAP (A × P) (B × P)
    H = productMap f (id P)
    pA : MAP (A × P) (P × A)
    pA = swap
    pB : MAP (B × P) (P × B)
    pB = swap
    qA : MAP (P × A) (A × P)
    qA = swap
    qB : MAP (P × B) (B × P)
    qB = swap
    εA : (pA ∘ qA) =₁ id (P × A)
    εA = swap-swap P A
    εB : (pB ∘ qB) =₁ id (P × B)
    εB = swap-swap P B

    left₁ : (pr₂ ∘ H) =₁ (id P ∘ pr₂)
    left₁ = pair-β₂ (f ∘ pr₁) (id P ∘ pr₂)
    left₂ : (pr₁ ∘ H) =₁ (f ∘ pr₁)
    left₂ = pair-β₁ (f ∘ pr₁) (id P ∘ pr₂)
    right₁ : ((id P ∘ pr₁) ∘ pA) =₁ (id P ∘ pr₂)
    right₁ = (id P ◁ pair-β₁ pr₂ pr₁) ∙ comp-assoc pA pr₁ (id P)
    right₂ : ((f ∘ pr₂) ∘ pA) =₁ (f ∘ pr₁)
    right₂ = (f ◁ pair-β₂ pr₂ pr₁) ∙ comp-assoc pA pr₂ f
    transpose-cell : (pB ∘ H) =₁ (J ∘ pA)
    transpose-cell = (pair-pre (id P ∘ pr₁) (f ∘ pr₂) pA) ⁻¹ ∙
      (pair⁼ (right₁ ⁻¹ ∙ left₁) (right₂ ⁻¹ ∙ left₂) ∙ pair-pre pr₂ pr₁ H)


private
  module TerminalRestriction {Γ : Context} {A B : CAT Γ} (f : MAP A B) where
    J : MAP A B
    J = f
    H : MAP (One × A) (One × B)
    H = product-restriction f
    pA : MAP (One × A) A
    pA = pr₂
    pB : MAP (One × B) B
    pB = pr₂
    qA : MAP A (One × A)
    qA = product-unitˡ-inverse A
    qB : MAP B (One × B)
    qB = product-unitˡ-inverse B
    εA : (pA ∘ qA) =₁ id A
    εA = product-unitˡ-pr₂-inverse A
    εB : (pB ∘ qB) =₁ id B
    εB = product-unitˡ-pr₂-inverse B
    transpose-cell : (pB ∘ H) =₁ (J ∘ pA)
    transpose-cell = pair-β₂ (id One ∘ pr₁) (f ∘ pr₂)


private
  module SwapCoconeRoundtrip {Γ : Context} {P A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) =
    CoconeSpanRetraction {E = E}
      (SwapRestriction.J {P = P} u) (SwapRestriction.J {P = P} l)
      (SwapRestriction.H {P = P} u) (SwapRestriction.H {P = P} l)
      (SwapRestriction.pA {P = P} u) (SwapRestriction.pB {P = P} u) (SwapRestriction.pB {P = P} l)
      (SwapRestriction.qA {P = P} u) (SwapRestriction.qB {P = P} u) (SwapRestriction.qB {P = P} l)
      (SwapRestriction.εA {P = P} u) (SwapRestriction.εB {P = P} u) (SwapRestriction.εB {P = P} l)
      (swap-isEquiv B P) (swap-isEquiv C P)
      (SwapRestriction.transpose-cell {P = P} u) (SwapRestriction.transpose-cell {P = P} l)

  module TerminalCoconeRoundtrip {Γ : Context} {A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) =
    CoconeSpanRetraction {E = E}
      (TerminalRestriction.J u) (TerminalRestriction.J l)
      (TerminalRestriction.H u) (TerminalRestriction.H l)
      (TerminalRestriction.pA u) (TerminalRestriction.pB u) (TerminalRestriction.pB l)
      (TerminalRestriction.qA u) (TerminalRestriction.qB u) (TerminalRestriction.qB l)
      (TerminalRestriction.εA u) (TerminalRestriction.εB u) (TerminalRestriction.εB l)
      (product-unitˡ-isEquiv B) (product-unitˡ-isEquiv C)
      (TerminalRestriction.transpose-cell u) (TerminalRestriction.transpose-cell l)

-- REVIEW ONLY: concrete projection image of the ACTUAL restriction compositor.
-- Local terminal adapter prerequisite, no existing03/shared source edits.
private
  module ProjectionCompositor {Γ : Context} {P A B C : CAT Γ}
    (f : MAP A B) (g : MAP B C) where
    private
      Jf = product-restriction {P = P} f
      Jg = product-restriction {P = P} g
      product-compositor = restriction-compositor {P = P} f g
      βf = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)
      βg = pair-β₂ (id P ∘ pr₁) (g ∘ pr₂)
      βgf = pair-β₂ (id P ∘ pr₁) ((g ∘ f) ∘ pr₂)
      coordinate = post-square-cell g pr₂ f pr₂ Jf βf
      first-coordinate = post-square-cell (id P) pr₁ (id P) pr₁ Jf
        (pair-β₁ (id P ∘ pr₁) (f ∘ pr₂))
      first = pair-evaluation-over₂-One (id P ∘ pr₁) (g ∘ pr₂) Jf
        first-coordinate coordinate
      second = unconst-sides₌
        (productMap-cong-triangle₂ (comp-unitˡ (id P)) (id₌ (g ∘ f)))
      bottom-normal : ((id₌ (g ∘ f) ▷ pr₂) ∙ coordinate) =₂ coordinate
      bottom-normal = comp₌-unitˡ-One coordinate ∙
        comp₌-cong (preWhisker-id₌ (g ∘ f) pr₂) (id₌ coordinate)

    square : SquareCell₌ (pr₂ ◁ product-compositor) coordinate
      (restrict-triangle pr₂ Jg βg Jf) βgf
    square = replace-edges₌ (id₌ (pr₂ ◁ product-compositor)) bottom-normal
      (lies-over-comp pr₂ first second)

-- This is the concrete ProductCompositorImages second coordinate from the
-- checked product coherence calculation, followed by the ACTUAL first-unit
-- productMap-cong factor in κ. Projection triangles and scalar id conversion
-- are retained. Required existing owners: Triangles, PairingRestriction,
-- ProductFunctor and ProductRestriction; no claimed equality of inverse mates.

-- REVIEW ONLY: full projection square of the actual product-square.
-- Keeps the selected product compositor and supplied σ. No reverse-mate claim.
private
  module ProjectionSquare {Γ : Context} {P A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) where
    private
      u = Square.source-map s
      v = Square.target-map s
      σ = Square.cell s
      Ju = product-restriction {P = P} u
      Jl = product-restriction {P = P} l
      Jr = product-restriction {P = P} r
      Jv = product-restriction {P = P} v
      pA = pr₂ {C = P} {D = A}
      pB = pr₂ {C = P} {D = B}
      pC = pr₂ {C = P} {D = C}
      pD = pr₂ {C = P} {D = D}
      βu = pair-β₂ (id P ∘ pr₁) (u ∘ pr₂)
      βl = pair-β₂ (id P ∘ pr₁) (l ∘ pr₂)
      βr = pair-β₂ (id P ∘ pr₁) (r ∘ pr₂)
      βv = pair-β₂ (id P ∘ pr₁) (v ∘ pr₂)
      module Forward = ChangeSpan {E = D} u l Ju Jl pA pB pC βu βl
        using (value)
      module Left = ProjectionCompositor {P = P} u r
        using (square)
      module Right = ProjectionCompositor {P = P} l v
        using (square)
      Al = comp-assoc Ju Jr pD
      Ar = comp-assoc Jl Jv pD
      L = pD ◁ restriction-compositor {P = P} u r
      R = pD ◁ restriction-compositor {P = P} l v
      M = pD ◁ productMap-cong (id₌ (id P)) σ
      coordinate-left = post-square-cell r pA u pB Ju βu
      coordinate-right = post-square-cell v pA l pC Jl βl
      raw = pD ◁ Square.cell (product-square {P = P} s)
      expanded = R ⁻¹ ∙ (M ∙ L)
      target-match = coordinate-right ⁻¹ ∙ ((σ ▷ pA) ∙ coordinate-left)
      middle : SquareCell₌ M (σ ▷ pA)
        (pair-β₂ (id P ∘ pr₁) ((r ∘ u) ∘ pr₂))
        (pair-β₂ (id P ∘ pr₁) ((v ∘ l) ∘ pr₂))
      middle = unconst-sides₌ (productMap-cong-triangle₂ (id₌ (id P)) σ)
      raw-normal : raw =₂ expanded
      raw-normal = comp₌-cong (postWhisker-inverse pD (restriction-compositor l v))
        (postWhisker-comp₌ pD (productMap-cong (id₌ (id P)) σ) (restriction-compositor u r)) ∙
          postWhisker-comp₌ pD ((restriction-compositor l v) ⁻¹)
            (productMap-cong (id₌ (id P)) σ ∙ restriction-compositor u r)
      raw-square : SquareCell₌ raw target-match
        ((βr ▷ Ju) ∙ Al ⁻¹) ((βv ▷ Jl) ∙ Ar ⁻¹)
      raw-square = replace-edges₌ (raw-normal ⁻¹) (id₌ target-match)
        (inv-comp-square₌ (adjoin-square₌ Left.square middle) Right.square)
      source-normal : changeEndpoints (Al ⁻¹) (Ar ⁻¹) raw =₂
        (Ar ⁻¹ ∙ (raw ∙ Al))
      source-normal = comp₌-cong (id₌ (Ar ⁻¹))
        (comp₌-cong (id₌ raw) (inverse-inverse Al))

    source : Cocone Ju Jl D
    source = cocone-postcompose pD (square-cocone (product-square {P = P} s))
    target : Cocone Ju Jl D
    target = Forward.value (square-cocone s)
    matching : SquareCell₌ (βr ▷ Ju) (βv ▷ Jl) (Cocone.match source) (Cocone.match target)
    matching = transpose-square₌
      (replace-sides₌ (comp-inv-right (βr ▷ Ju) (Al ⁻¹))
        (comp-inv-right (βv ▷ Jl) (Ar ⁻¹))
        (replace-edges₌ source-normal (id₌ target-match)
          (changeEndpoints-extend-square (Al ⁻¹) (Ar ⁻¹) raw raw-square)))
    comparison : CoconeIdentification₁ source target
    comparison = record { left = βr; right = βv; compatible = matching }

-- ProjectionSquare needs the existing private ChangeSpan in the native owner.
-- The full coordinate route of Forward is literally post-square-cell, so the
-- target matching is its chosen changeEndpoints expression, without extra law.

-- Remaining assembly lives after TerminalCoconeRoundtrip/ProjectionSquare.
-- Whole scalar pasting and inversion are the existing family operations at One.
private
  module _ {Γ : Context} {A B C T : CAT Γ} {u : MAP A B} {l : MAP A C} where
    compose-cocone₁ : {s t z : Cocone u l T}
      → CoconeIdentification₁ t z → CoconeIdentification₁ s t → CoconeIdentification₁ s z
    compose-cocone₁ Ψ Φ = cocone-identification-One
      (cocone-identification-compose (cocone-identification Ψ) (cocone-identification Φ))
    inverse-cocone₁ : {s t : Cocone u l T}
      → CoconeIdentification₁ s t → CoconeIdentification₁ t s
    inverse-cocone₁ Φ = cocone-identification-One
      (cocone-identification-inverse (cocone-identification Φ))

  module TerminalProductSquare {Γ : Context} {A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) where
    private
      u = Square.source-map s
      ordinary = square-cocone s
      product = square-cocone (product-square {P = One} s)
      p = pr₂ {C = One} {D = D}
      q = product-unitˡ-inverse D
      ε = product-unitˡ-pr₂-inverse D
      module Product = TerminalCoconeRoundtrip {E = One × D} u l
        using (back; back-postcomposition)
      module Ordinary = TerminalCoconeRoundtrip {E = D} u l
        using (back; back-identification; twice; module Calculation)
      module Projection = ProjectionSquare {P = One} s
        using (comparison)
      recovered = Product.back product
      inserted = cocone-postcompose q ordinary
      back-projection : CoconeIdentification₁
        (cocone-postcompose p recovered) (Ordinary.back (cocone-postcompose p product))
      back-projection = inverse-cocone₁ (Product.back-postcomposition p product)
      back-square : CoconeIdentification₁
        (Ordinary.back (cocone-postcompose p product)) (Ordinary.twice ordinary)
      back-square = cocone-identification-One
        (Ordinary.back-identification (cocone-identification Projection.comparison))
      projected-recovered : CoconeIdentification₁ (cocone-postcompose p recovered) ordinary
      projected-recovered = compose-cocone₁ (Ordinary.Calculation.comparison ordinary)
        (compose-cocone₁ back-square back-projection)
      retraction-action : CoconeIdentification₁
        (cocone-postcompose (p ∘ q) ordinary) (cocone-postcompose (id D) ordinary)
      retraction-action = cocone-identification-One (record
        { left = ε ▷ Cocone.left ordinary
        ; right = ε ▷ Cocone.right ordinary
        ; compatible = post-square-cell-outer l (Cocone.right ordinary)
            (Cocone.left ordinary) u (Cocone.match ordinary) ε })
      projected-inserted : CoconeIdentification₁ (cocone-postcompose p inserted) ordinary
      projected-inserted = compose-cocone₁ (postcompose-unit ordinary)
        (compose-cocone₁ retraction-action (inverse-cocone₁ (postcompose-assoc ordinary q p)))
      projected-comparison : CoconeIdentification₁
        (cocone-postcompose p recovered) (cocone-postcompose p inserted)
      projected-comparison = compose-cocone₁ (inverse-cocone₁ projected-inserted) projected-recovered
      module Recovery = CoconePostcompositionRecovery p (product-unitˡ-isEquiv D)
        recovered inserted (cocone-identification projected-comparison)
        using (value)
    comparison : CoconeIdentification₁
      (Product.back product) (cocone-postcompose q ordinary)
    comparison = cocone-identification-One Recovery.value

-- No equality between independent reverse mates is asserted. Both leg factors
-- and the higher matching factor are the actual chosen postwhiskering reflection.
-- The whole id·ordinary → ordinary comparison is essential in projected-inserted.

module _ {Γ : Context} where
  module NativeRestrictionCocones {P A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) where
    Ju : MAP (P × A) (P × B)
    Ju = product-restriction u
    Jl : MAP (P × A) (P × C)
    Jl = product-restriction l
    private
      eA = funEval {C = A} {D = E}
      eB = funEval {C = B} {D = E}
      eC = funEval {C = C} {D = E}
      F = funPre {D = E} u
      G = funPre {D = E} l

    represented : Cone F G P → Cocone Ju Jl E
    represented s = record
      { left = evaluate eB (Cone.left s); right = evaluate eC (Cone.right s)
      ; match = changeEndpoints (funPre-uncurry u (Cone.left s)) (funPre-uncurry l (Cone.right s))
          (evaluate-cong eA (Cone.match s)) }

    evaluate-identification : {X : CAT Γ} {s t : Cone F G P}
      → ConeIdentification X s t → CoconeIdentification X (represented s) (represented t)
    evaluate-identification {X = X} {s} {t} Φ = record
      { left = evaluate⁼ eB (ConeIdentification.left Φ)
      ; right = evaluate⁼ eC (ConeIdentification.right Φ)
      ; compatible = replace-sides₌
          (constant-endpoints {X = X} (funPre-uncurry u (Cone.left s)) (funPre-uncurry l (Cone.right s))
            (evaluate-cong eA (Cone.match s)))
          (constant-endpoints {X = X} (funPre-uncurry u (Cone.left t)) (funPre-uncurry l (Cone.right t))
            (evaluate-cong eA (Cone.match t)))
          (transport-square
            (const {P = X} (funPre-uncurry u (Cone.left s))) (const (funPre-uncurry u (Cone.left t)))
            (const (funPre-uncurry l (Cone.right s))) (const (funPre-uncurry l (Cone.right t)))
            (const (evaluate-cong eA (Cone.match s))) (const (evaluate-cong eA (Cone.match t)))
            (evaluate⁼ eA (F ◁ ConeIdentification.left Φ)) (evaluate⁼ eA (G ◁ ConeIdentification.right Φ))
            (evaluate⁼ eB (ConeIdentification.left Φ) ▷ Ju) (evaluate⁼ eC (ConeIdentification.right Φ) ▷ Jl)
            (funPre-uncurry-inputs u (ConeIdentification.left Φ))
            (funPre-uncurry-inputs l (ConeIdentification.right Φ))
            (evaluation-fixed-square {X = X} eA (ConeIdentification.compatible Φ))) }

    module CurriedCocone (s : Cocone Ju Jl E) where
      left = funCurry {C = B} {D = E} (Cocone.left s)
      right = funCurry {C = C} {D = E} (Cocone.right s)
      left-β = funCurry-β {C = B} {D = E} (Cocone.left s)
      right-β = funCurry-β {C = C} {D = E} (Cocone.right s)
      private
        input = left-β ▷ Ju
        output = right-β ▷ Jl
        desired = output ⁻¹ ∙ (Cocone.match s ∙ input)
        left-change = funPre-uncurry u left
        right-change = funPre-uncurry l right
        raw-match = right-change ⁻¹ ∙ (desired ∙ left-change)
      value : Cone F G P
      value = record
        { left = left; right = right
        ; match = reflect eA (funUniversal A E) (F ∘ left) (G ∘ right) raw-match }
      abstract
        matching-image : Cocone.match (represented value) =₂ desired
        matching-image = restore-boundaries left-change right-change desired
          (evaluate-cong eA (Cone.match value))
          (reflect-β-One eA (funUniversal A E) (F ∘ left) (G ∘ right) raw-match)
        compatible : SquareCell₌ (left-β ▷ Ju) (right-β ▷ Jl)
          (Cocone.match (represented value)) (Cocone.match s)
        compatible = comp₌-cong (id₌ output) (matching-image ⁻¹) ∙
          (comp-inv-left output (Cocone.match s ∙ input)) ⁻¹
      comparison : CoconeIdentification₁ (represented value) s
      comparison = record { left = left-β; right = right-β; compatible = compatible }

    module ReflectedCocone {X : CAT Γ} (s t : Cone F G P)
      (Φ : CoconeIdentification X (represented s) (represented t)) where
      open Terms.Equalities X using (_＝_)
      left : Cone.left s ＝ Cone.left t
      left = reflect eB (funUniversal B E) (Cone.left s) (Cone.left t) (CoconeIdentification.left Φ)
      right : Cone.right s ＝ Cone.right t
      right = reflect eC (funUniversal C E) (Cone.right s) (Cone.right t) (CoconeIdentification.right Φ)
      left-image : evaluate⁼ eB left =₁ CoconeIdentification.left Φ
      left-image = reflect-β eB (funUniversal B E) (Cone.left s) (Cone.left t) (CoconeIdentification.left Φ)
      right-image : evaluate⁼ eC right =₁ CoconeIdentification.right Φ
      right-image = reflect-β eC (funUniversal C E) (Cone.right s) (Cone.right t) (CoconeIdentification.right Φ)
      private
        left-square : SquareCell₌ (evaluate⁼ eA (F ◁ left)) (CoconeIdentification.left Φ ▷ Ju)
          (const (funPre-uncurry u (Cone.left s))) (const (funPre-uncurry u (Cone.left t)))
        left-square = replace-edges₌ (id₌ (evaluate⁼ eA (F ◁ left)))
          (preWhisker Ju ◁ left-image) (funPre-uncurry-inputs u left)
        right-square : SquareCell₌ (evaluate⁼ eA (G ◁ right)) (CoconeIdentification.right Φ ▷ Jl)
          (const (funPre-uncurry l (Cone.right s))) (const (funPre-uncurry l (Cone.right t)))
        right-square = replace-edges₌ (id₌ (evaluate⁼ eA (G ◁ right)))
          (preWhisker Jl ◁ right-image) (funPre-uncurry-inputs l right)
      source-boundary = const {P = X} (Cone.match t) ∙ (F ◁ left)
      target-boundary = (G ◁ right) ∙ const {P = X} (Cone.match s)
      native-action = evaluation-action eA (F ∘ Cone.left s) (G ∘ Cone.right t)
      wanted-image : (native-action ∘ source-boundary) =₁ (native-action ∘ target-boundary)
      wanted-image = framed-matching-image eA (Cone.match s) (Cone.match t) (F ◁ left) (G ◁ right)
        (funPre-uncurry u (Cone.left s)) (funPre-uncurry l (Cone.right s))
        (funPre-uncurry u (Cone.left t)) (funPre-uncurry l (Cone.right t))
        left-square right-square (CoconeIdentification.compatible Φ)
      matching-factor : Fact.Factorization (postWhisker native-action) wanted-image
      matching-factor = evaluation-reflection₂ eA (funUniversal A E)
        source-boundary target-boundary wanted-image
      compatible : SquareCell₌ (F ◁ left) (G ◁ right) (const (Cone.match s)) (const (Cone.match t))
      compatible = Fact.factor matching-factor
      matching-image : (postWhisker native-action ∘ compatible) =₁ wanted-image
      matching-image = Fact.triangle matching-factor
      value : ConeIdentification X s t
      value = record { left = left; right = right; compatible = compatible }

    curry-represented : (s : Cone F G P)
      → ConeIdentification₁ (CurriedCocone.value (represented s)) s
    curry-represented s = cone-identification-One
      (ReflectedCocone.value (CurriedCocone.value (represented s)) s
        (cocone-identification (CurriedCocone.comparison (represented s))))

  module MappingCoconeEncoding {P A B C E : CAT Γ} (pAn : isAn P)
    (u : MAP A B) (l : MAP A C)
    (s : Cocone (product-restriction {P = P} u) (product-restriction l) E) where
    private
      module M = MappingOutEvaluation {P = P} {E = E} u l
        using (represented)
      Ju = product-restriction {P = P} u
      Jl = product-restriction {P = P} l
    left = mapCurry pAn (Cocone.left s)
    right = mapCurry pAn (Cocone.right s)
    left-β = mapCurry-β pAn (Cocone.left s)
    right-β = mapCurry-β pAn (Cocone.right s)
    private
      input = left-β ▷ Ju
      output = right-β ▷ Jl
      desired = output ⁻¹ ∙ (Cocone.match s ∙ input)
      left-change = mapPre-uncurry u left
      right-change = mapPre-uncurry l right
      raw-match = right-change ⁻¹ ∙ (desired ∙ left-change)
    value : Cone (mapPre {D = E} u) (mapPre l) P
    value = record
      { left = left; right = right
      ; match = uncurry-reflect pAn (mapPre u ∘ left) (mapPre l ∘ right) raw-match }
    abstract
      matching-image : Cocone.match (M.represented value) =₂ desired
      matching-image = restore-boundaries left-change right-change desired
        (uncurry⁼ (Cone.match value))
        (uncurry-reflect-β pAn (mapPre u ∘ left) (mapPre l ∘ right) raw-match)
      compatible : SquareCell₌ (left-β ▷ Ju) (right-β ▷ Jl)
        (Cocone.match (M.represented value)) (Cocone.match s)
      compatible = comp₌-cong (id₌ output) (matching-image ⁻¹) ∙
        (comp-inv-left output (Cocone.match s ∙ input)) ⁻¹
    comparison : CoconeIdentification₁ (M.represented value) s
    comparison = record { left = left-β; right = right-β; compatible = compatible }

module _ {Γ : Context} where
  module NativeOrdinaryCocones {P A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) where
    Hu : MAP (A × P) (B × P)
    Hu = productMap u (id P)
    Hl : MAP (A × P) (C × P)
    Hl = productMap l (id P)
    private
      e = funEval {C = P} {D = E}

    represented : Cocone u l (Fun P E) → Cocone Hu Hl E
    represented s = record
      { left = evaluate e (Cocone.left s)
      ; right = evaluate e (Cocone.right s)
      ; match = changeEndpoints (evaluate-restrict e (Cocone.left s) u)
          (evaluate-restrict e (Cocone.right s) l) (evaluate-cong e (Cocone.match s)) }

    evaluate-identification : {X : CAT Γ} {s t : Cocone u l (Fun P E)}
      → CoconeIdentification X s t → CoconeIdentification X (represented s) (represented t)
    evaluate-identification {X} {s} {t} Φ = record
      { left = evaluate⁼ e (CoconeIdentification.left Φ)
      ; right = evaluate⁼ e (CoconeIdentification.right Φ)
      ; compatible = replace-sides₌
          (constant-endpoints {X = X} (evaluate-restrict e (Cocone.left s) u)
            (evaluate-restrict e (Cocone.right s) l) (evaluate-cong e (Cocone.match s)))
          (constant-endpoints {X = X} (evaluate-restrict e (Cocone.left t) u)
            (evaluate-restrict e (Cocone.right t) l) (evaluate-cong e (Cocone.match t)))
          (transport-square
            (const {P = X} (evaluate-restrict e (Cocone.left s) u))
            (const (evaluate-restrict e (Cocone.left t) u))
            (const (evaluate-restrict e (Cocone.right s) l))
            (const (evaluate-restrict e (Cocone.right t) l))
            (const (evaluate-cong e (Cocone.match s))) (const (evaluate-cong e (Cocone.match t)))
            (evaluate⁼ e (CoconeIdentification.left Φ ▷ u))
            (evaluate⁼ e (CoconeIdentification.right Φ ▷ l))
            (evaluate⁼ e (CoconeIdentification.left Φ) ▷ Hu)
            (evaluate⁼ e (CoconeIdentification.right Φ) ▷ Hl)
            (evaluate-restrict-inputs e (CoconeIdentification.left Φ) u)
            (evaluate-restrict-inputs e (CoconeIdentification.right Φ) l)
            (evaluation-fixed-square {X = X} e (CoconeIdentification.compatible Φ))) }

    module CurriedCocone (s : Cocone Hu Hl E) where
      left = funCurry {C = P} {D = E} (Cocone.left s)
      right = funCurry {C = P} {D = E} (Cocone.right s)
      left-β = funCurry-β {C = P} {D = E} (Cocone.left s)
      right-β = funCurry-β {C = P} {D = E} (Cocone.right s)
      private
        input = left-β ▷ Hu
        output = right-β ▷ Hl
        desired = output ⁻¹ ∙ (Cocone.match s ∙ input)
        left-change = evaluate-restrict e left u
        right-change = evaluate-restrict e right l
        raw-match = right-change ⁻¹ ∙ (desired ∙ left-change)
      value : Cocone u l (Fun P E)
      value = record
        { left = left; right = right
        ; match = reflect e (funUniversal P E) (left ∘ u) (right ∘ l) raw-match }
      abstract
        matching-image : Cocone.match (represented value) =₂ desired
        matching-image = restore-boundaries left-change right-change desired
          (evaluate-cong e (Cocone.match value))
          (reflect-β-One e (funUniversal P E) (left ∘ u) (right ∘ l) raw-match)
        compatible : SquareCell₌ (left-β ▷ Hu) (right-β ▷ Hl)
          (Cocone.match (represented value)) (Cocone.match s)
        compatible = comp₌-cong (id₌ output) (matching-image ⁻¹) ∙
          (comp-inv-left output (Cocone.match s ∙ input)) ⁻¹
      comparison : CoconeIdentification₁ (represented value) s
      comparison = record { left = left-β; right = right-β; compatible = compatible }

module _ {Γ : Context} where
  module TransposedRestrictionCocones {P A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) where
    Ju : MAP (P × A) (P × B)
    Ju = product-restriction u
    Jl : MAP (P × A) (P × C)
    Jl = product-restriction l
    Hu : MAP (A × P) (B × P)
    Hu = productMap u (id P)
    Hl : MAP (A × P) (C × P)
    Hl = productMap l (id P)
    private
      module O = NativeOrdinaryCocones {P = P} {E = E} u l
        using (represented; module CurriedCocone)
      module Roundtrip = SwapCoconeRoundtrip {P = P} {E = E} u l
        using (back; back-identification; forward; forward-identification; twice; module Calculation)
    transposed : Cocone Ju Jl E → Cocone Hu Hl E
    transposed = Roundtrip.forward
    transpose-identification : {X : CAT Γ} {s t : Cocone Ju Jl E}
      → CoconeIdentification X s t → CoconeIdentification X (transposed s) (transposed t)
    transpose-identification = Roundtrip.forward-identification
    untransposed : Cocone Hu Hl E → Cocone Ju Jl E
    untransposed = Roundtrip.back
    untranspose-identification : {X : CAT Γ} {s t : Cocone Hu Hl E}
      → CoconeIdentification X s t → CoconeIdentification X (untransposed s) (untransposed t)
    untranspose-identification = Roundtrip.back-identification
    twice-transposed : Cocone Ju Jl E → Cocone Ju Jl E
    twice-transposed = Roundtrip.twice
    transpose-roundtrip : (s : Cocone Ju Jl E) → CoconeIdentification₁ (twice-transposed s) s
    transpose-roundtrip = Roundtrip.Calculation.comparison
    module CurriedCocone (s : Cocone Ju Jl E) where
      private
        module Curried = O.CurriedCocone (transposed s)
          using (comparison; value)
      value : Cocone u l (Fun P E)
      value = Curried.value
      comparison : CoconeIdentification₁ (O.represented value) (transposed s)
      comparison = Curried.comparison

private
  module _ {Γ : Context} {X : CAT Γ} where
    constant-cocone-identification : {A B C E : CAT Γ} {u : MAP A B} {l : MAP A C}
      {s t : Cocone u l E} → CoconeIdentification₁ s t → CoconeIdentification X s t
    constant-cocone-identification {u = u} {l} Φ = record
      { left = const {P = X} (CoconeIdentification₁.left Φ)
      ; right = const {P = X} (CoconeIdentification₁.right Φ)
      ; compatible = replace-edges₌
          ((pre-constant (CoconeIdentification₁.left Φ) u) ⁻¹)
          ((pre-constant (CoconeIdentification₁.right Φ) l) ⁻¹)
          (constant-square₌ (CoconeIdentification₁.compatible Φ)) }

module _ {Γ : Context} where
  module OrdinaryMappingCocones {A B C E : CAT Γ} (u : MAP A B) (l : MAP A C) where
    private
      module Roundtrip = TerminalCoconeRoundtrip {E = E} u l
        using (back; back-identification; forward; forward-identification; module Calculation)
      module M = MappingOutEvaluation {P = One} {E = E} u l
        using (evaluate-identification; represented; module RecoveredIdentification)
    product-cocone : Cocone u l E → Cocone (product-restriction {P = One} u) (product-restriction l) E
    product-cocone = Roundtrip.forward
    encoded : Cocone u l E → Cone (mapPre {D = E} u) (mapPre l) One
    encoded s = MappingCoconeEncoding.value one-isAn u l (product-cocone s)
    decoded : Cone (mapPre {D = E} u) (mapPre l) One → Cocone u l E
    decoded s = Roundtrip.back (M.represented s)
    encoded-left-name : (s : Cocone u l E) → Cone.left (encoded s) =₁ name (Cocone.left s)
    encoded-left-name s = id₌ (name (Cocone.left s))
    encoded-right-name : (s : Cocone u l E) → Cone.right (encoded s) =₁ name (Cocone.right s)
    encoded-right-name s = id₌ (name (Cocone.right s))
    decoded-left : (s : Cone (mapPre {D = E} u) (mapPre l) One)
      → Cocone.left (decoded s) =₁ decode (Cone.left s)
    decoded-left s = id₌ (decode (Cone.left s))
    decoded-right : (s : Cone (mapPre {D = E} u) (mapPre l) One)
      → Cocone.right (decoded s) =₁ decode (Cone.right s)
    decoded-right s = id₌ (decode (Cone.right s))

    module _ {X : CAT Γ} where
      encoded-identification : {s t : Cocone u l E}
        → CoconeIdentification X s t → ConeIdentification X (encoded s) (encoded t)
      encoded-identification {s} {t} Φ = M.RecoveredIdentification.identification one-isAn (encoded s) (encoded t)
        (cocone-identification-compose
          (cocone-identification-inverse
            (constant-cocone-identification (MappingCoconeEncoding.comparison one-isAn u l (product-cocone t))))
          (cocone-identification-compose (Roundtrip.forward-identification Φ)
            (constant-cocone-identification (MappingCoconeEncoding.comparison one-isAn u l (product-cocone s)))))
      decoded-identification : {s t : Cone (mapPre {D = E} u) (mapPre l) One}
        → ConeIdentification X s t → CoconeIdentification X (decoded s) (decoded t)
      decoded-identification Φ = Roundtrip.back-identification (M.evaluate-identification Φ)

    private
      leg-normal : {T : CAT Γ} (h : MAP T E)
        → ((comp-unitʳ h ∙ ((h ◁ product-unitˡ-pr₂-inverse T) ∙
            comp-assoc (product-unitˡ-inverse T) pr₂ h)) ∙
            (mapCurry-β one-isAn (h ∘ pr₂) ▷ product-unitˡ-inverse T)) =₂ decode-name h
      leg-normal {T} h = comp₌-cong (id₌ (comp-unitʳ h))
          (comp₌-assoc (h ◁ product-unitˡ-pr₂-inverse T)
            (comp-assoc (product-unitˡ-inverse T) pr₂ h)
            (mapCurry-β one-isAn (h ∘ pr₂) ▷ product-unitˡ-inverse T)) ∙
        comp₌-assoc (comp-unitʳ h)
          ((h ◁ product-unitˡ-pr₂-inverse T) ∙ comp-assoc (product-unitˡ-inverse T) pr₂ h)
          (mapCurry-β one-isAn (h ∘ pr₂) ▷ product-unitˡ-inverse T)
      module DecodeEncoding (s : Cocone u l E) where
        raw : CoconeIdentification₁ (decoded (encoded s)) s
        raw = cocone-identification-One
          (cocone-identification-compose
            (cocone-identification (Roundtrip.Calculation.comparison s))
            (Roundtrip.back-identification (cocone-identification
              (MappingCoconeEncoding.comparison one-isAn u l (product-cocone s)))))
        comparison : CoconeIdentification₁ (decoded (encoded s)) s
        comparison = record
          { left = decode-name (Cocone.left s)
          ; right = decode-name (Cocone.right s)
          ; compatible = replace-edges₌
              (preWhisker u ◁ leg-normal (Cocone.left s))
              (preWhisker l ◁ leg-normal (Cocone.right s))
              (CoconeIdentification₁.compatible raw) }
    decoded-encoded : (s : Cocone u l E) → CoconeIdentification₁ (decoded (encoded s)) s
    decoded-encoded = DecodeEncoding.comparison
module NativeCompositorEvaluation {Γ : Context} {A B C E : CAT Γ}
  (f : MAP A B) (g : MAP B C) where
  private
    eA = funEval {C = A} {D = E}
    eB = funEval {C = B} {D = E}
    eC = funEval {C = C} {D = E}
    Jf = product-restriction {P = Fun C E} f
    Jg = product-restriction {P = Fun C E} g
    before = (funPre-β {D = E} g ▷ Jf) ∙ funPre-uncurry f (funPre {D = E} g)
    after = funPre-β {D = E} (g ∘ f)
    route = (eC ◁ restriction-compositor {P = Fun C E} f g) ∙ comp-assoc Jf Jg eC
    input = after ⁻¹ ∙
      ((eC ◁ restriction-compositor {P = Fun C E} f g) ∙
        (comp-assoc Jf Jg eC ∙ before))

  private
    image : evaluate-cong eA (funPre-comp {D = E} f g) =₂ input
    image = reflect-β-One eA (funUniversal A E) _ _ input

    base-square : SquareCell₌ (evaluate-cong eA (funPre-comp {D = E} f g)) route before after
    base-square = (comp₌-assoc (eC ◁ restriction-compositor f g) (comp-assoc Jf Jg eC) before) ⁻¹ ∙
      (comp-inv-left after
        ((eC ◁ restriction-compositor f g) ∙ (comp-assoc Jf Jg eC ∙ before)) ∙
        comp₌-cong (id₌ after) image)

  private
    module Calculation = Pre.PrecompositionCompositor eA eB eC f g
      (funPre {D = E} f) (funPre g) (funPre (g ∘ f))
      (funPre-β f) (funPre-β g) (funPre-β (g ∘ f)) (funPre-comp f g)
      using (comparison)

  square : {P : CAT Γ} (h : MAP P (Fun C E))
    → SquareCell₌ (evaluate-cong eA (funPre-comp {D = E} f g ▷ h))
        ((funUncurry h ◁ restriction-compositor {P = P} f g) ∙
          comp-assoc (product-restriction {P = P} f)
            (product-restriction {P = P} g) (funUncurry h))
        ((funPre-uncurry g h ▷ product-restriction {P = P} f) ∙
          (funPre-uncurry f (funPre g ∘ h) ∙
            evaluate-cong eA (comp-assoc h (funPre g) (funPre f))))
        (funPre-uncurry (g ∘ f) h)
  square h = Calculation.comparison base-square h

module _ {Γ : Context} where
  module NativeParameterizedInputEvaluation {P A B E : CAT Γ}
    (h : MAP P (Fun B E)) {f g : MAP A B} (α : f =₁ g) where
    private
      Q : CAT Γ
      Q = Fun B E
      RA = productMap h (id A)
      RB = productMap h (id B)
      JQf = product-restriction {P = Q} f
      JQg = product-restriction {P = Q} g
      JPf = product-restriction {P = P} f
      JPg = product-restriction {P = P} g
      δQ = productMap-cong (id₌ (id Q)) α
      δP = productMap-cong (id₌ (id P)) α
      e : MAP (Q × B) E
      e = funEval {C = B} {D = E}
      eA = funEval {C = A} {D = E}
      first : SquareCell₌ (evaluate-cong eA (funPre⁼ {D = E} α ▷ h))
        (evaluate-cong eA (funPre⁼ α) ▷ RA)
        (evaluate-restrict eA (funPre f) h) (evaluate-restrict eA (funPre g) h)
      first = replace-edges₌
        (evaluate⁼-absolute eA (funPre⁼ α ▷ h))
        (preWhisker RA ◁ evaluate⁼-absolute eA (funPre⁼ α))
        (unconst-sides₌ (evaluate-restrict-inputs eA (funPre⁼ α) h))

      base : SquareCell₌ (evaluate-cong eA (funPre⁼ {D = E} α)) (e ◁ δQ)
        (funPre-β f) (funPre-β g)
      base = replace-edges₌ (evaluate⁼-absolute eA (funPre⁼ α))
        (postWhisker e ◁ productMap-cong₂ (const-One (id₌ (id Q))) (id₌ α))
        (unconst-sides₌ (funPre⁼-evaluation α))
      second : SquareCell₌ (evaluate-cong eA (funPre⁼ {D = E} α) ▷ RA)
        ((e ◁ δQ) ▷ RA) (funPre-β f ▷ RA) (funPre-β g ▷ RA)
      second = pre-square₌ RA base
      third : SquareCell₌ ((e ◁ δQ) ▷ RA) (e ◁ (δQ ▷ RA))
        (comp-assoc RA JQf e) (comp-assoc RA JQg e)
      third = whisker-mixed-One δQ RA e
      fourth : SquareCell₌ (e ◁ (δQ ▷ RA)) (e ◁ (RB ◁ δP))
        (e ◁ productMap-separate h f) (e ◁ productMap-separate h g)
      fourth = post-square₌ e (SeparationSecondInput.compatibility h α)
      fifth : SquareCell₌ (e ◁ (RB ◁ δP)) (funUncurry h ◁ δP)
        ((comp-assoc JPf RB e) ⁻¹) ((comp-assoc JPg RB e) ⁻¹)
      fifth = inverse-square₌ (postWhisker-comp-One δP RB e)

    compatibility : SquareCell₌ (evaluate-cong eA (funPre⁼ {D = E} α ▷ h))
      (funUncurry h ◁ productMap-cong (id₌ (id P)) α)
      (funPre-uncurry f h) (funPre-uncurry g h)
    compatibility = paste-square₌
      (paste-square₌ (paste-square₌ (paste-square₌ first second) third) fourth) fifth

-- REVIEW ONLY: complete ordinary decoding of the actual supplied mapping square.
-- Public concrete seam intended for the forward FunctorCriterion implication.
module _ {Γ : Context} where
  module OrdinaryParameterizedSquareEvaluation {A B C D E : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (z : MAP One (Map D E)) where
    private
      u = Square.source-map s
      h = uncurry z
      q = product-unitˡ-inverse D
      ordinary = square-cocone s
      product = square-cocone (product-square {P = One} s)
      module O = OrdinaryMappingCocones {E = E} u l
        using (decoded)
      module R = TerminalCoconeRoundtrip {E = E} u l
        using (back; back-identification)
      module M = MappingOutEvaluation {P = One} {E = E} u l
      module Actual = ParameterizedSquareEvaluation {P = One} s z
        using (identification)
      module Terminal = TerminalProductSquare s
        using (comparison)
      decoded-actual : CoconeIdentification₁
        (O.decoded (cone-restrict z (mappingOut s E)))
        (R.back (cocone-postcompose h product))
      decoded-actual = cocone-identification-One
        (R.back-identification (cocone-identification Actual.identification))
      commuting : CoconeIdentification₁
        (R.back (cocone-postcompose h product))
        (cocone-postcompose h (TerminalCoconeRoundtrip.back {E = One × D} u l product))
      commuting = TerminalCoconeRoundtrip.back-postcomposition {E = One × D} u l h product
      inserted : CoconeIdentification₁
        (cocone-postcompose h (TerminalCoconeRoundtrip.back {E = One × D} u l product))
        (cocone-postcompose h (cocone-postcompose q ordinary))
      inserted = fixed-postcomposition h Terminal.comparison
      associated : CoconeIdentification₁
        (cocone-postcompose h (cocone-postcompose q ordinary))
        (cocone-postcompose (decode z) ordinary)
      associated = inverse-cocone₁ (postcompose-assoc ordinary q h)
    identification : CoconeIdentification₁
      (O.decoded (cone-restrict z (mappingOut s E)))
      (cocone-postcompose (decode z) ordinary)
    identification = compose-cocone₁ associated
      (compose-cocone₁ inserted (compose-cocone₁ commuting decoded-actual))
-- decode z is literally uncurry z ∘ product-unitˡ-inverse D.
-- Both legs are the resulting chosen factors. The full matching is pasted,
-- including actual mappingOut matching and all terminal unit/associativity cells.

```

```agda
private
  module ScalarEvaluation {Γ : Context} {F C E : CAT Γ} (e : MAP (F × C) E) where
    on-identification : {T : CAT Γ} {f g : MAP T F}
      → f =₁ g → evaluate e f =₁ evaluate e g
    on-identification = evaluate-cong e

    congruence : {T : CAT Γ} {f g : MAP T F} {α β : f =₁ g}
      → α =₂ β → on-identification α =₂ on-identification β
    congruence {α = α} {β} p = evaluate⁼-absolute e β ∙
      (evaluate⁼-cong e p ∙ (evaluate⁼-absolute e α) ⁻¹)

    composition : {T : CAT Γ} {f g h : MAP T F} (β : g =₁ h) (α : f =₁ g)
      → on-identification (β ∙ α) =₂ (on-identification β ∙ on-identification α)
    composition β α = comp₌-cong (evaluate⁼-absolute e β) (evaluate⁼-absolute e α) ∙
      (evaluate⁼-composition e β α ∙ (evaluate⁼-absolute e (β ∙ α)) ⁻¹)

    identity : {T : CAT Γ} (f : MAP T F)
      → on-identification (id₌ f) =₂ id₌ (evaluate e f)
    identity f = const-One (id₌ (evaluate e f)) ∙
      (evaluate⁼-identity e f ∙
        (evaluate⁼-cong e ((const-One (id₌ f)) ⁻¹) ∙ (evaluate⁼-absolute e (id₌ f)) ⁻¹))

    inverse : {T : CAT Γ} {f g : MAP T F} (α : f =₁ g)
      → on-identification (α ⁻¹) =₂ (on-identification α) ⁻¹
    inverse {f = f} α = cancel-right (on-identification α)
      ((comp₌-inverseˡ-One (on-identification α)) ⁻¹ ∙
        (identity f ∙ (congruence (comp₌-inverseˡ-One α) ∙ (composition (α ⁻¹) α) ⁻¹)))



-- Whole parameter change of the ACTUAL product square.
-- Private native-owner helper for the direct-curried criterion alternative.
private
  module ProductSquareParameterChange {Γ : Context} {P Q A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (h : MAP P Q) where
    private
      u : MAP A B
      u = Square.source-map s
      v : MAP C D
      v = Square.target-map s
      σ : (r ∘ u) =₁ (v ∘ l)
      σ = Square.cell s
      JPu = product-restriction {P = P} u
      JPl = product-restriction {P = P} l
      JPr = product-restriction {P = P} r
      JPv = product-restriction {P = P} v
      JQu = product-restriction {P = Q} u
      JQl = product-restriction {P = Q} l
      JQr = product-restriction {P = Q} r
      JQv = product-restriction {P = Q} v
      RA : MAP (P × A) (Q × A)
      RA = productMap h (id A)
      RB : MAP (P × B) (Q × B)
      RB = productMap h (id B)
      RC : MAP (P × C) (Q × C)
      RC = productMap h (id C)
      RD : MAP (P × D) (Q × D)
      RD = productMap h (id D)
      Su = productMap-separate h u
      Sl = productMap-separate h l
      Sr = productMap-separate h r
      Sv = productMap-separate h v
      Sru = productMap-separate h (r ∘ u)
      Svl = productMap-separate h (v ∘ l)
      κQu = restriction-compositor {P = Q} u r
      κQl = restriction-compositor {P = Q} l v
      κPu = restriction-compositor {P = P} u r
      κPl = restriction-compositor {P = P} l v
      σQ = productMap-cong (id₌ (id Q)) σ
      σP = productMap-cong (id₌ (id P)) σ
      module Change = ChangeSpan {E = Q × D} JQu JQl JPu JPl RA RB RC (Su ⁻¹) (Sl ⁻¹)
        using (value; module L; module R)
      ρr = Change.L.ρ JQr
      ρv = Change.R.ρ JQv
      Ar = comp-assoc RA JQu JQr
      Av = comp-assoc RA JQl JQv
      Br = comp-assoc JPu RB JQr
      Bv = comp-assoc JPl RC JQv
      L = comp-assoc JPu JPr RD
      R = comp-assoc JPl JPv RD
      α = Sr ▷ JPu
      β = Sv ▷ JPl
      left-total = L ∙ (α ∙ ρr ⁻¹)
      right-total = R ∙ (β ∙ ρv ⁻¹)
      raw-source = Square.cell (product-square {P = Q} s) ▷ RA
      raw-target = RD ◁ Square.cell (product-square {P = P} s)

      post-inverse-inverse : {K Z : CAT Γ} (F : MAP K Z)
        {V : CAT Γ} {f g : MAP V K} (δ : f =₁ g)
        → ((F ◁ δ ⁻¹) ⁻¹) =₂ (F ◁ δ)
      post-inverse-inverse F δ = inverse-inverse (F ◁ δ) ∙ (inv₌ ◁ postWhisker-inverse F δ)
      inverse-left-frame : ρr ⁻¹ =₂ (Br ⁻¹ ∙ ((JQr ◁ Su) ∙ Ar))
      inverse-left-frame = comp₌-cong (id₌ (Br ⁻¹))
          (comp₌-cong (post-inverse-inverse JQr Su) (id₌ Ar)) ∙
        (comp₌-assoc (Br ⁻¹) ((JQr ◁ Su ⁻¹) ⁻¹) Ar ∙
          (comp₌-cong (inverse-composite (JQr ◁ Su ⁻¹) Br) (inverse-inverse Ar) ∙
            inverse-composite (Ar ⁻¹) ((JQr ◁ Su ⁻¹) ∙ Br)))
      inverse-right-frame : ρv ⁻¹ =₂ (Bv ⁻¹ ∙ ((JQv ◁ Sl) ∙ Av))
      inverse-right-frame = comp₌-cong (id₌ (Bv ⁻¹))
          (comp₌-cong (post-inverse-inverse JQv Sl) (id₌ Av)) ∙
        (comp₌-assoc (Bv ⁻¹) ((JQv ◁ Sl ⁻¹) ⁻¹) Av ∙
          (comp₌-cong (inverse-composite (JQv ◁ Sl ⁻¹) Bv) (inverse-inverse Av) ∙
            inverse-composite (Av ⁻¹) ((JQv ◁ Sl ⁻¹) ∙ Bv)))
      left-square : SquareCell₌ (κQu ▷ RA) (RD ◁ κPu) left-total Sru
      left-square =
        (comp₌-cong (id₌ (RD ◁ κPu))
          (comp₌-cong (id₌ L) (comp₌-cong (id₌ α) inverse-left-frame))) ⁻¹ ∙
        parameter-separation-composition h u r
      middle-square : SquareCell₌ (σQ ▷ RA) (RD ◁ σP) Sru Svl
      middle-square = SeparationSecondInput.compatibility h σ
      right-square : SquareCell₌ (κQl ▷ RA) (RD ◁ κPl) right-total Svl
      right-square =
        (comp₌-cong (id₌ (RD ◁ κPl))
          (comp₌-cong (id₌ R) (comp₌-cong (id₌ β) inverse-right-frame))) ⁻¹ ∙
        parameter-separation-composition h l v
      source-normal : raw-source =₂ ((κQl ▷ RA) ⁻¹ ∙ ((σQ ▷ RA) ∙ (κQu ▷ RA)))
      source-normal = comp₌-cong (preWhisker-inverse κQl RA)
        (preWhisker-comp₌ σQ κQu RA) ∙ preWhisker-comp₌ (κQl ⁻¹) (σQ ∙ κQu) RA
      target-normal : raw-target =₂ ((RD ◁ κPl) ⁻¹ ∙ ((RD ◁ σP) ∙ (RD ◁ κPu)))
      target-normal = comp₌-cong (postWhisker-inverse RD κPl)
        (postWhisker-comp₌ RD σP κPu) ∙ postWhisker-comp₌ RD (κPl ⁻¹) (σP ∙ κPu)
      raw-square : SquareCell₌ raw-source raw-target left-total right-total
      raw-square = replace-edges₌ (source-normal ⁻¹) (target-normal ⁻¹)
        (inv-comp-square₌ (adjoin-square₌ left-square middle-square) right-square)
    source : Cocone JPu JPl (Q × D)
    source = Change.value (square-cocone (product-square {P = Q} s))
    target : Cocone JPu JPl (Q × D)
    target = cocone-postcompose RD (square-cocone (product-square {P = P} s))
    private
      source-matching-normal : changeEndpoints (ρr ⁻¹) (ρv ⁻¹) raw-source =₂ Cocone.match source
      source-matching-normal = comp₌-cong (id₌ (ρv ⁻¹))
        (comp₌-cong (id₌ raw-source) (inverse-inverse ρr))
      target-matching-normal : changeEndpoints (L ⁻¹) (R ⁻¹) raw-target =₂ Cocone.match target
      target-matching-normal = comp₌-cong (id₌ (R ⁻¹))
        (comp₌-cong (id₌ raw-target) (inverse-inverse L))
    abstract
      matching : SquareCell₌ α β (Cocone.match source) (Cocone.match target)
      matching = replace-sides₌ source-matching-normal target-matching-normal
        (transport-square (ρr ⁻¹) (L ⁻¹) (ρv ⁻¹) (R ⁻¹) raw-source raw-target
          left-total right-total α β
          (inv-comp-left L (α ∙ ρr ⁻¹))
          (inv-comp-left R (β ∙ ρv ⁻¹)) (transpose-square₌ raw-square))
    comparison : CoconeIdentification₁ source target
    comparison = record { left = Sr; right = Sv; compatible = matching }
-- Needs direct ProductRestriction.parameter-separation-composition import.
-- No equality of whole higher comparison witnesses is asserted.


-- Private native restriction calculation, using the scalar evaluation laws.
private
  module NativeConeParameterChange {Γ : Context} {P Q A B C E : CAT Γ}
    (u : MAP A B) (l : MAP A C) (h : MAP P Q)
    (s : Cone (funPre {D = E} u) (funPre l) Q) where
    private
      eA = funEval {C = A} {D = E}
      eB = funEval {C = B} {D = E}
      eC = funEval {C = C} {D = E}
      module Action = ScalarEvaluation eA
        using (composition; inverse)
      module NP = NativeRestrictionCocones {P = P} {E = E} u l
        using (Jl; Ju; represented)
      module NQ = NativeRestrictionCocones {P = Q} {E = E} u l
        using (Jl; Ju; represented)
      p = Cone.left s
      q = Cone.right s
      τ = Cone.match s
      F = funPre {D = E} u
      G = funPre {D = E} l
      RA = productMap h (id A)
      RB = productMap h (id B)
      RC = productMap h (id C)
      Su = productMap-separate h u
      Sl = productMap-separate h l
      module Change = ChangeSpan {E = E} NQ.Ju NQ.Jl NP.Ju NP.Jl RA RB RC (Su ⁻¹) (Sl ⁻¹)
        using (value; module L; module R)
      module U = Pre.RepresentedPrecomposition eA eB u F (funPre-β u)
        using (substitution)
      module L = Pre.RepresentedPrecomposition eA eC l G (funPre-β l)
        using (substitution)
      μu = funPre-uncurry u p
      μl = funPre-uncurry l q
      ρu = Change.L.ρ (evaluate eB p)
      ρl = Change.R.ρ (evaluate eC q)
      af = comp-assoc h p F
      ag = comp-assoc h q G
      Ef = funPre-uncurry u (p ∘ h) ∙ evaluate-cong eA af
      Eg = funPre-uncurry l (q ∘ h) ∙ evaluate-cong eA ag
      route : {Z : CAT Γ} (f : MAP A Z) (k : MAP Q (Fun Z E))
        → (evaluate eA (funPre f ∘ k) ∘ RA) =₁
            ((evaluate (funEval {C = Z} {D = E}) k ∘ productMap h (id Z)) ∘ product-restriction {P = P} f)
      route {Z} f k =
        (comp-assoc (product-restriction {P = P} f) (productMap h (id Z))
          (evaluate (funEval {C = Z} {D = E}) k)) ⁻¹ ∙
        ((evaluate (funEval {C = Z} {D = E}) k ◁ productMap-separate h f) ∙
          (comp-assoc RA (product-restriction {P = Q} f) (evaluate (funEval {C = Z} {D = E}) k) ∙
            (funPre-uncurry f k ▷ RA)))
      Ef′ = route u p
      Eg′ = route l q
      bf = evaluate-restrict eA (F ∘ p) h
      bg = evaluate-restrict eA (G ∘ q) h

      endpoints : {T : CAT Γ} {x x′ y y′ : MAP T (Fun A E)}
        (a : x =₁ x′) (b : y =₁ y′) (δ : x =₁ y)
        → evaluate-cong eA (changeEndpoints a b δ) =₂
            changeEndpoints (evaluate-cong eA a) (evaluate-cong eA b) (evaluate-cong eA δ)
      endpoints a b δ = comp₌-cong (id₌ (evaluate-cong eA b))
        (comp₌-cong (id₌ (evaluate-cong eA δ)) (Action.inverse a) ∙ Action.composition δ (a ⁻¹)) ∙
        Action.composition b (δ ∙ a ⁻¹)

      pre-endpoints : {K T Z : CAT Γ} {x x′ y y′ : MAP T Z}
        (a : x =₁ x′) (b : y =₁ y′) (δ : x =₁ y) (k : MAP K T)
        → (changeEndpoints a b δ ▷ k) =₂ changeEndpoints (a ▷ k) (b ▷ k) (δ ▷ k)
      pre-endpoints a b δ k = comp₌-cong (id₌ (b ▷ k))
        (comp₌-cong (id₌ (δ ▷ k)) (preWhisker-inverse a k) ∙ preWhisker-comp₌ δ (a ⁻¹) k) ∙
        preWhisker-comp₌ b (δ ∙ a ⁻¹) k

      module Leg {Z : CAT Γ} (f : MAP A Z) (k : MAP Q (Fun Z E)) where
        ez = funEval {C = Z} {D = E}
        μ = funPre-uncurry f k
        RZ = productMap h (id Z)
        JQ = product-restriction {P = Q} f
        JP = product-restriction {P = P} f
        S = productMap-separate h f
        input-assoc = comp-assoc RA JQ (evaluate ez k)
        output-assoc = comp-assoc JP RZ (evaluate ez k)
        ρ = input-assoc ⁻¹ ∙ ((evaluate ez k ◁ S ⁻¹) ∙ output-assoc)
        module K = Pre.RepresentedPrecomposition eA ez f (funPre f) (funPre-β f)
        double-inverse : ((evaluate ez k ◁ S ⁻¹) ⁻¹) =₂ (evaluate ez k ◁ S)
        double-inverse = inverse-inverse (evaluate ez k ◁ S) ∙
          (inv₌ ◁ postWhisker-inverse (evaluate ez k) S)
        inverse-frame : ρ ⁻¹ =₂ (output-assoc ⁻¹ ∙ ((evaluate ez k ◁ S) ∙ input-assoc))
        inverse-frame = comp₌-cong (id₌ (output-assoc ⁻¹))
            (comp₌-cong double-inverse (id₌ input-assoc)) ∙
          (comp₌-assoc (output-assoc ⁻¹) ((evaluate ez k ◁ S ⁻¹) ⁻¹) input-assoc ∙
            (comp₌-cong (inverse-composite (evaluate ez k ◁ S ⁻¹) output-assoc) (inverse-inverse input-assoc) ∙
              inverse-composite (input-assoc ⁻¹) ((evaluate ez k ◁ S ⁻¹) ∙ output-assoc)))
        frame : ((ρ ⁻¹) ∙ (μ ▷ RA)) =₂ route f k
        frame = comp₌-cong (id₌ (output-assoc ⁻¹)) (comp₌-assoc (evaluate ez k ◁ S) input-assoc (μ ▷ RA)) ∙
          (comp₌-assoc (output-assoc ⁻¹) ((evaluate ez k ◁ S) ∙ input-assoc) (μ ▷ RA) ∙
            comp₌-cong inverse-frame (id₌ (μ ▷ RA)))

    source : Cocone NP.Ju NP.Jl E
    source = NP.represented (cone-restrict h s)
    target : Cocone NP.Ju NP.Jl E
    target = Change.value (NQ.represented s)
    left = evaluate-restrict eB p h
    right = evaluate-restrict eC q h
    private
      rawSource = changeEndpoints Ef Eg (evaluate-cong eA (τ ▷ h))
      rawTarget = changeEndpoints Ef′ Eg′ (evaluate-cong eA τ ▷ RA)
      source-normal : Cocone.match source =₂ rawSource
      source-normal = changeEndpoints-iterated (evaluate-cong eA af) (evaluate-cong eA ag)
        (funPre-uncurry u (p ∘ h)) (funPre-uncurry l (q ∘ h)) (evaluate-cong eA (τ ▷ h)) ∙
        changeEndpoints-cong (funPre-uncurry u (p ∘ h)) (funPre-uncurry l (q ∘ h))
          (endpoints af ag (τ ▷ h))
      target-frame-normal : Cocone.match target =₂
        changeEndpoints (ρu ⁻¹) (ρl ⁻¹) (Cocone.match (NQ.represented s) ▷ RA)
      target-frame-normal = comp₌-cong (id₌ (ρl ⁻¹))
        (comp₌-cong (id₌ (Cocone.match (NQ.represented s) ▷ RA)) ((inverse-inverse ρu) ⁻¹))
      target-normal : Cocone.match target =₂ rawTarget
      target-normal = comp₌-cong (Leg.frame l q)
          (comp₌-cong (id₌ (evaluate-cong eA τ ▷ RA)) (inv₌ ◁ Leg.frame u p)) ∙
        (changeEndpoints-iterated (μu ▷ RA) (μl ▷ RA) (ρu ⁻¹) (ρl ⁻¹) (evaluate-cong eA τ ▷ RA) ∙
          changeEndpoints-cong (ρu ⁻¹) (ρl ⁻¹) (pre-endpoints μu μl (evaluate-cong eA τ) RA) ∙
            target-frame-normal)
      middle : SquareCell₌ (evaluate-cong eA (τ ▷ h)) (evaluate-cong eA τ ▷ RA) bf bg
      middle = unconst-sides₌ (replace-edges₌ (evaluate⁼-absolute eA (τ ▷ h))
        (preWhisker RA ◁ evaluate⁼-absolute eA τ) (evaluate-restrict-inputs eA τ h))
      raw-square : SquareCell₌ (left ▷ NP.Ju) (right ▷ NP.Jl) rawSource rawTarget
      raw-square = transport-square Ef Ef′ Eg Eg′
        (evaluate-cong eA (τ ▷ h)) (evaluate-cong eA τ ▷ RA)
        bf bg (left ▷ NP.Ju) (right ▷ NP.Jl)
        ((U.substitution p h) ⁻¹)
        ((L.substitution q h) ⁻¹)
        (transpose-square₌ middle)
    comparison : CoconeIdentification₁ source target
    comparison = record { left = left; right = right
      ; compatible = replace-sides₌ (source-normal ⁻¹) (target-normal ⁻¹) raw-square }
-- ChangeSpan and ScalarEvaluation remain private to this owner.


-- Currying the universal evaluated product square chooses this matching.
-- No identification with the former funPre-comp/funPre⁼ pasting is asserted.
module _ {Γ : Context} where
  module DirectCurriedFunctorSquare {A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (E : CAT Γ) where
    private
      u = Square.source-map s
      v = Square.target-map s
      Q = Fun D E
      e = funEval {C = D} {D = E}
      module NQ = NativeRestrictionCocones {P = Q} {E = E} u l
        using (Jl; Ju; represented; module CurriedCocone)
      universal-product : Cocone NQ.Ju NQ.Jl E
      universal-product = cocone-postcompose e (square-cocone (product-square {P = Q} s))
      module Encoded = NQ.CurriedCocone universal-product
        using (comparison; value)
    value : Cone (funPre {D = E} u) (funPre l) (Fun D E)
    value = Encoded.value
    -- Both legs are definitionally funPre r and funPre v, since funPre is
    -- defined by currying this evaluated restriction.
    module Parameterized {P : CAT Γ} (h : MAP P (Fun D E)) where
      private
        module NP = NativeRestrictionCocones {P = P} {E = E} u l
          using (Jl; Ju; represented)
        module Restriction = NativeConeParameterChange u l h value
          using (comparison)
        module Product = ProductSquareParameterChange s h
          using (comparison; source; target)
        RA = productMap h (id A)
        RB = productMap h (id B)
        RC = productMap h (id C)
        RD = productMap h (id D)
        Su = productMap-separate h u
        Sl = productMap-separate h l
        module Change = ChangeSpan {E = E} NQ.Ju NQ.Jl NP.Ju NP.Jl RA RB RC (Su ⁻¹) (Sl ⁻¹)
          using (identification; value)
        parameter-product = square-cocone (product-square {P = P} s)
        restricted-encoding : CoconeIdentification₁
          (Change.value (NQ.represented value)) (Change.value universal-product)
        restricted-encoding = cocone-identification-One
          (Change.identification (cocone-identification Encoded.comparison))
        commuting : CoconeIdentification₁
          (Change.value universal-product) (cocone-postcompose e Product.source)
        commuting = change-span-postcomposition NQ.Ju NQ.Jl NP.Ju NP.Jl
          RA RB RC (Su ⁻¹) (Sl ⁻¹) e
          (square-cocone (product-square {P = Q} s))
        product-image : CoconeIdentification₁
          (cocone-postcompose e Product.source) (cocone-postcompose e Product.target)
        product-image = fixed-postcomposition e Product.comparison
        associated : CoconeIdentification₁
          (cocone-postcompose e Product.target)
          (cocone-postcompose (funUncurry h) parameter-product)
        associated = inverse-cocone₁ (postcompose-assoc parameter-product RD e)
      source : Cocone NP.Ju NP.Jl E
      source = NP.represented (cone-restrict h value)
      target : Cocone NP.Ju NP.Jl E
      target = cocone-postcompose (funUncurry h) parameter-product
      comparison : CoconeIdentification₁ source target
      comparison = compose-cocone₁ associated
        (compose-cocone₁ product-image
          (compose-cocone₁ commuting
            (compose-cocone₁ restricted-encoding Restriction.comparison)))
-- Direct owner imports: ProductRestriction.parameter-separation-composition;
-- PreEvaluationSubstitution (qualified Pre); Functoriality.funPre-β;
-- EvaluationRepresentation.evaluate-restrict-inputs; private ScalarEvaluation
-- (composition/inverse only needed by NativeConeParameterChange).
-- All comparisons retain the whole supplied product-square matching.

```

```agda
-- Concrete comparison of the actual restricted named map with its encoded cocone.
-- Draft in the native owner, after the terminal helpers/ordinary encoding.
private
  module _ {Γ : Context} {A B C T E : CAT Γ} {u : MAP A B} {l : MAP A C}
    (s : Cocone u l T) {h k : MAP T E} (α : h =₁ k) where
    postcomposition-cong₁ : CoconeIdentification₁ (cocone-postcompose h s) (cocone-postcompose k s)
    postcomposition-cong₁ = cocone-identification-One (record
      { left = α ▷ Cocone.left s
      ; right = α ▷ Cocone.right s
      ; compatible = post-square-cell-outer l (Cocone.right s) (Cocone.left s)
          u (Cocone.match s) α })

module _ {Γ : Context} where
  module OrdinaryPostcompositionEncoding {A B C D E : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (h : MAP D E) where
    private
      u : MAP A B
      u = Square.source-map s
      Ju : MAP (One × A) (One × B)
      Ju = product-restriction u
      Jl : MAP (One × A) (One × C)
      Jl = product-restriction l
      pA : MAP (One × A) A
      pA = pr₂
      pB : MAP (One × B) B
      pB = pr₂
      pC : MAP (One × C) C
      pC = pr₂
      pD : MAP (One × D) D
      pD = pr₂
      ordinary : Cocone u l D
      ordinary = square-cocone s
      product : Cocone Ju Jl (One × D)
      product = square-cocone (product-square {P = One} s)
      module M = MappingOutEvaluation {P = One} {E = E} u l
        using (represented; module RecoveredIdentification)
      module O = OrdinaryMappingCocones {E = E} u l
        using (encoded)
      module R = TerminalCoconeRoundtrip {E = E} u l
        using (forward)
      module RD = TerminalCoconeRoundtrip {E = D} u l
        using (forward)
      module Actual = ParameterizedSquareEvaluation {P = One} s (name h)
        using (identification; source)
      module Projection = ProjectionSquare {P = One} s
        using (comparison)
      name-beta : uncurry (name h) =₁ (h ∘ pD)
      name-beta = CurriedRepresentation.evaluation (name-representation h)
      evaluation-comparison : CoconeIdentification₁ Actual.source (cocone-postcompose (h ∘ pD) product)
      evaluation-comparison = compose-cocone₁ (postcomposition-cong₁ product name-beta) Actual.identification
      projected-comparison : CoconeIdentification₁
        (cocone-postcompose (h ∘ pD) product) (cocone-postcompose h (RD.forward ordinary))
      projected-comparison = compose-cocone₁
        (fixed-postcomposition h Projection.comparison) (postcompose-assoc product pD h)
      commuting : CoconeIdentification₁
        (R.forward (cocone-postcompose h ordinary)) (cocone-postcompose h (RD.forward ordinary))
      commuting = change-span-postcomposition u l Ju Jl pA pB pC
        (pair-β₂ (id One ∘ pr₁) (u ∘ pr₂))
        (pair-β₂ (id One ∘ pr₁) (l ∘ pr₂)) h ordinary
      represented-comparison : CoconeIdentification₁
        (M.represented (cone-restrict (name h) (mappingOut s E)))
        (R.forward (cocone-postcompose h ordinary))
      represented-comparison = compose-cocone₁ (inverse-cocone₁ commuting)
        (compose-cocone₁ projected-comparison evaluation-comparison)
      encoded-comparison : CoconeIdentification₁
        (M.represented (cone-restrict (name h) (mappingOut s E)))
        (M.represented (O.encoded (cocone-postcompose h ordinary)))
      encoded-comparison = compose-cocone₁
        (inverse-cocone₁ (MappingCoconeEncoding.comparison one-isAn u l
          (R.forward (cocone-postcompose h ordinary)))) represented-comparison
    identification : ConeIdentification₁
      (cone-restrict (name h) (mappingOut s E)) (O.encoded (cocone-postcompose h ordinary))
    identification = cone-identification-One
      (M.RecoveredIdentification.identification one-isAn
        (cone-restrict (name h) (mappingOut s E)) (O.encoded (cocone-postcompose h ordinary))
        (cocone-identification encoded-comparison))
-- Direct imports additionally needed: Currying.CurriedRepresentation and Points.name-representation.


-- Whole first-factor product square and its ordinary native evaluation.
-- Private native-owner helper after ScalarEvaluation.
private
  module FirstFactorSquare {Γ : Context} (P : CAT Γ) {A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) where
    u = Square.source-map s
    v = Square.target-map s
    Hu = productMap u (id P)
    Hl = productMap l (id P)
    Hr = productMap r (id P)
    Hv = productMap v (id P)
    κu = productMap-first-comp {C = P} r u
    κl = productMap-first-comp {C = P} v l
    middle = productMap-cong (Square.cell s) (id₌ (id P))
    value : Cocone Hu Hl (D × P)
    value = record { left = Hr; right = Hv; match = κl ⁻¹ ∙ (middle ∙ κu) }

  module OrdinaryFirstFactorSquareEvaluation {Γ : Context} {P A B C D E : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (g : MAP D (Fun P E)) where
    private
      module H = FirstFactorSquare P s
        using (Hl; Hr; Hu; Hv; middle; u; v; value; κl; κu)
      module O = NativeOrdinaryCocones {P = P} {E = E} H.u l
        using (represented)
      e = funEval {C = P} {D = E}
      module Action = ScalarEvaluation e
        using (composition; inverse)
      k = funUncurry g
      u = H.u
      v = H.v
      σ = Square.cell s
      left-leg = evaluate-restrict e g r
      right-leg = evaluate-restrict e g v
      μu = evaluate-restrict e (g ∘ r) u
      μl = evaluate-restrict e (g ∘ v) l
      Au = comp-assoc H.Hu H.Hr k
      Al = comp-assoc H.Hl H.Hv k
      α = left-leg ▷ H.Hu
      β = right-leg ▷ H.Hl
      left-total = Au ∙ (α ∙ μu)
      right-total = Al ∙ (β ∙ μl)
      assoc-u = comp-assoc u r g
      assoc-l = comp-assoc l v g
      eu = evaluate-cong e assoc-u
      el = evaluate-cong e assoc-l
      em = evaluate-cong e (g ◁ σ)
      κu = k ◁ H.κu
      κl = k ◁ H.κl
      middle = k ◁ H.middle
      ru = evaluate-restrict e g (r ∘ u)
      vl = evaluate-restrict e g (v ∘ l)
      ordinary = cocone-postcompose g (square-cocone s)
      raw = evaluate-cong e (Cocone.match ordinary)
      δ = k ◁ Cocone.match H.value
      raw-normal : raw =₂ (el ⁻¹ ∙ (em ∙ eu))
      raw-normal = comp₌-cong (Action.inverse assoc-l)
        (Action.composition (g ◁ σ) assoc-u) ∙ Action.composition (assoc-l ⁻¹) ((g ◁ σ) ∙ assoc-u)
      product-normal : δ =₂ (κl ⁻¹ ∙ (middle ∙ κu))
      product-normal = comp₌-cong (postWhisker-inverse k H.κl)
        (postWhisker-comp₌ k H.middle H.κu) ∙ postWhisker-comp₌ k (H.κl ⁻¹) (H.middle ∙ H.κu)
      -- SquareCell top bottom left right is right ∙ top = bottom ∙ left.
      left-square : SquareCell₌ eu κu left-total ru
      left-square = evaluate-restrict-assoc e g r u
      right-square : SquareCell₌ el κl right-total vl
      right-square = evaluate-restrict-assoc e g v l
      middle-square : SquareCell₌ em middle ru vl
      middle-square = replace-edges₌ (evaluate⁼-absolute e (g ◁ σ))
        (postWhisker k ◁ productMap-cong₂ (id₌ σ) (const-One (id₌ (id P))))
        (unconst-sides₌ (evaluate-restrict-substitution e g σ))
      raw-square : SquareCell₌ raw δ left-total right-total
      raw-square = replace-edges₌ (raw-normal ⁻¹) (product-normal ⁻¹)
        (inv-comp-square₌ (adjoin-square₌ left-square middle-square) right-square)
    source : Cocone H.Hu H.Hl E
    source = O.represented ordinary
    target : Cocone H.Hu H.Hl E
    target = cocone-postcompose k H.value
    private
      target-normal : changeEndpoints (Au ⁻¹) (Al ⁻¹) δ =₂ Cocone.match target
      target-normal = comp₌-cong (id₌ (Al ⁻¹))
        (comp₌-cong (id₌ δ) (inverse-inverse Au))
    comparison : CoconeIdentification₁ source target
    comparison = record { left = left-leg; right = right-leg
      ; compatible = replace-sides₌ (id₌ (Cocone.match source)) target-normal
          (transport-square μu (Au ⁻¹) μl (Al ⁻¹) raw δ
            left-total right-total α β
            (inv-comp-left Au (α ∙ μu)) (inv-comp-left Al (β ∙ μl))
            (transpose-square₌ raw-square)) }
-- Direct imports: ProductFunctorCoherence.productMap-first-comp,
-- EvaluationSubstitution.evaluate-restrict-assoc,
-- EvaluationRepresentation.evaluate-restrict-substitution.
-- Product-level swap compatibility remains a separate required theorem.


-- Both projections of the actual selected swap restriction cell.
-- Native owner, using its private SwapRestriction definition unchanged.
private
  module SwapRestrictionCoordinates {Γ : Context} {P A B : CAT Γ} (f : MAP A B) where
    private
      module S = SwapRestriction {P = P} f
        using (H; left₁; left₂; pA; right₁; right₂; transpose-cell)
      δ₁ = S.right₁ ⁻¹ ∙ S.left₁
      δ₂ = S.right₂ ⁻¹ ∙ S.left₂
      source₁ = project-pair₁ pr₂ pr₁ S.H
      source₂ = project-pair₂ pr₂ pr₁ S.H
      target₁ = project-pair₁ (id P ∘ pr₁) (f ∘ pr₂) S.pA
      target₂ = project-pair₂ (id P ∘ pr₁) (f ∘ pr₂) S.pA
      remove-id₁ : ((id₌ ((id P ∘ pr₁) ∘ S.pA)) ⁻¹ ∙ δ₁) =₂ δ₁
      remove-id₁ = comp₌-unitˡ-One δ₁ ∙
        comp₌-cong (inverse-identity ((id P ∘ pr₁) ∘ S.pA)) (id₌ δ₁)
      remove-id₂ : ((id₌ ((f ∘ pr₂) ∘ S.pA)) ⁻¹ ∙ δ₂) =₂ δ₂
      remove-id₂ = comp₌-unitˡ-One δ₂ ∙
        comp₌-cong (inverse-identity ((f ∘ pr₂) ∘ S.pA)) (id₌ δ₂)
    projection₁ : SquareCell₌ (pr₁ ◁ S.transpose-cell) δ₁ source₁ target₁
    projection₁ = replace-edges₌ (id₌ (pr₁ ◁ S.transpose-cell)) remove-id₁
      (lies-over-comp pr₁
        (pair-evaluation-over₁-One pr₂ pr₁ S.H δ₁ δ₂)
        (lies-over-inverse pr₁ (pair-pre-over₁-One (id P ∘ pr₁) (f ∘ pr₂) S.pA)))
    projection₂ : SquareCell₌ (pr₂ ◁ S.transpose-cell) δ₂ source₂ target₂
    projection₂ = replace-edges₌ (id₌ (pr₂ ◁ S.transpose-cell)) remove-id₂
      (lies-over-comp pr₂
        (pair-evaluation-over₂-One pr₂ pr₁ S.H δ₁ δ₂)
        (lies-over-inverse pr₂ (pair-pre-over₂-One (id P ∘ pr₁) (f ∘ pr₂) S.pA)))
-- Direct additional imports: PairingRestriction pair-evaluation-over₁-One,
-- pair-pre-over₁-One and pair-pre-over₂-One; Inverses.inverse-identity;
-- Triangles.lies-over-inverse.
-- No independently chosen inverse naturality mate is substituted.


-- Canonical common-base projection frames for the ACTUAL swap cell.
-- Private native-owner client of SwapRestrictionCoordinates.
private
  module SwapRestrictionOverProjections {Γ : Context} {P A B : CAT Γ} (f : MAP A B) where
    private
      module S = SwapRestriction {P = P} f
        using (H; J; left₁; left₂; pA; right₁; right₂; transpose-cell)
      module Images = SwapRestrictionCoordinates {P = P} f
        using (projection₁; projection₂)
      project-source₁ = project-pair₁ pr₂ pr₁ S.H
      project-source₂ = project-pair₂ pr₂ pr₁ S.H
      project-target₁ = project-pair₁ (id P ∘ pr₁) (f ∘ pr₂) S.pA
      project-target₂ = project-pair₂ (id P ∘ pr₁) (f ∘ pr₂) S.pA
      δ = S.transpose-cell
    -- Both varying-coordinate frames land in f ∘ pr₁.
    varying-source = S.left₂ ∙ project-source₂
    varying-target = S.right₂ ∙ project-target₂
    -- Both fixed-coordinate frames land in pr₂.
    fixed-source = (comp-unitˡ pr₂ ∙ S.left₁) ∙ project-source₁
    fixed-target = pair-β₁ pr₂ pr₁ ∙
      restrict-triangle pr₁ S.J
        (comp-unitˡ pr₁ ∙ pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)) S.pA
    private
      close-common : {K Z : CAT Γ} {x y z z′ t : MAP K Z}
        (a : x =₁ t) (b : y =₁ t) (p : z =₁ x) (q : z′ =₁ y)
        (ε : z =₁ z′)
        → SquareCell₌ ε (b ⁻¹ ∙ a) p q
        → ((b ∙ q) ∙ ε) =₂ (a ∙ p)
      close-common a b p q ε square = comp-inv-left b (a ∙ p) ∙
        (comp₌-cong (id₌ b) (comp₌-assoc (b ⁻¹) a p) ∙
          (comp₌-cong (id₌ b) square ∙ comp₌-assoc b q ε))
      fixed-before : ((S.right₁ ∙ project-target₁) ∙ (pr₁ ◁ δ)) =₂
        (S.left₁ ∙ project-source₁)
      fixed-before = close-common S.left₁ S.right₁ project-source₁ project-target₁
        (pr₁ ◁ δ) Images.projection₁
      fixed-unit = comp-unitˡ (pr₂ {C = A} {D = P})
      swapped-unit : (fixed-unit ∙ S.right₁) =₂
        (pair-β₁ pr₂ pr₁ ∙ (comp-unitˡ pr₁ ▷ S.pA))
      swapped-unit = comp₌-cong (id₌ (pair-β₁ pr₂ pr₁)) (left-unitor-comp S.pA pr₁) ∙
        (comp₌-assoc (pair-β₁ pr₂ pr₁) (comp-unitˡ (pr₁ ∘ S.pA))
          (comp-assoc S.pA pr₁ (id P)) ∙
          (comp₌-cong (postWhisker-id-One (pair-β₁ pr₂ pr₁))
            (id₌ (comp-assoc S.pA pr₁ (id P)))) ∙
          (comp₌-assoc fixed-unit (id P ◁ pair-β₁ pr₂ pr₁)
            (comp-assoc S.pA pr₁ (id P))) ⁻¹)
      fixed-target-normal : (fixed-unit ∙ (S.right₁ ∙ project-target₁)) =₂ fixed-target
      fixed-target-normal = comp₌-cong (id₌ (pair-β₁ pr₂ pr₁))
          (comp₌-cong ((preWhisker-comp₌ (comp-unitˡ pr₁)
            (pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)) S.pA) ⁻¹)
            (id₌ ((comp-assoc S.pA S.J pr₁) ⁻¹))) ∙
        (comp₌-cong (id₌ (pair-β₁ pr₂ pr₁))
          ((comp₌-assoc (comp-unitˡ pr₁ ▷ S.pA)
            (pair-β₁ (id P ∘ pr₁) (f ∘ pr₂) ▷ S.pA)
            ((comp-assoc S.pA S.J pr₁) ⁻¹)) ⁻¹) ∙
          (comp₌-assoc (pair-β₁ pr₂ pr₁) (comp-unitˡ pr₁ ▷ S.pA) project-target₁ ∙
            (comp₌-cong swapped-unit (id₌ project-target₁) ∙
              (comp₌-assoc fixed-unit S.right₁ project-target₁) ⁻¹)))
    varying : ((varying-target) ∙ (pr₂ ◁ δ)) =₂ varying-source
    varying = close-common S.left₂ S.right₂ project-source₂ project-target₂
      (pr₂ ◁ δ) Images.projection₂
    fixed : ((fixed-target) ∙ (pr₁ ◁ δ)) =₂ fixed-source
    fixed = (comp₌-assoc fixed-unit S.left₁ project-source₁) ⁻¹ ∙
      (comp₌-cong (id₌ fixed-unit) fixed-before ∙
        (comp₌-assoc fixed-unit (S.right₁ ∙ project-target₁) (pr₁ ◁ δ) ∙
          comp₌-cong (fixed-target-normal ⁻¹) (id₌ (pr₁ ◁ δ))))
-- Direct additional imports: FunctorCoherence.left-unitor-comp and
-- FunctorCoherence.postWhisker-id-One. All chosen swap cells unchanged.


-- Concrete projection-pasting adapter used for the swap compositor proof.
-- All coherence is delegated to the existing OverBase compatible-* calculus.
private
  module SwapProjectionPasting {Γ : Context} {X₀ X₁ X₂ Y₀ Y₁ Y₂ T : CAT Γ}
    (p₀ : MAP X₀ T) (p₁ : MAP X₁ T) (p₂ : MAP X₂ T)
    (q₀ : MAP Y₀ T) (q₁ : MAP Y₁ T) (q₂ : MAP Y₂ T)
    (x₀ : MAP X₀ Y₀) (x₁ : MAP X₁ Y₁) (x₂ : MAP X₂ Y₂)
    (f : MAP X₀ X₁) (g : MAP X₁ X₂) (F : MAP Y₀ Y₁) (G : MAP Y₁ Y₂)
    (bf : (p₁ ∘ f) =₁ p₀) (bg : (p₂ ∘ g) =₁ p₁)
    (bF : (q₁ ∘ F) =₁ q₀) (bG : (q₂ ∘ G) =₁ q₁)
    (bx₀ : (q₀ ∘ x₀) =₁ p₀) (bx₁ : (q₁ ∘ x₁) =₁ p₁)
    (bx₂ : (q₂ ∘ x₂) =₁ p₂)
    (α : (x₁ ∘ f) =₁ (F ∘ x₀)) (β : (x₂ ∘ g) =₁ (G ∘ x₁)) where
    b₀ = OverBase.compose-triangle q₂ x₂ bx₂ (g ∘ f) (OverBase.compose-triangle p₂ g bg f bf)
    b₁ = OverBase.compose-triangle q₂ (x₂ ∘ g) (OverBase.compose-triangle q₂ x₂ bx₂ g bg) f bf
    b₂ = OverBase.compose-triangle q₂ (G ∘ x₁) (OverBase.compose-triangle q₂ G bG x₁ bx₁) f bf
    b₃ = OverBase.compose-triangle q₂ G bG (x₁ ∘ f) (OverBase.compose-triangle q₁ x₁ bx₁ f bf)
    b₄ = OverBase.compose-triangle q₂ G bG (F ∘ x₀) (OverBase.compose-triangle q₁ F bF x₀ bx₀)
    b₅ = OverBase.compose-triangle q₂ (G ∘ F) (OverBase.compose-triangle q₂ G bG F bF) x₀ bx₀
    pasted : (x₂ ∘ (g ∘ f)) =₁ ((G ∘ F) ∘ x₀)
    pasted = Square.cell (comp-square (Squares.square g G β) (Squares.square f F α))
    compatible :
      OverBase.CompatibleOver q₁ (OverBase.compose-triangle q₁ x₁ bx₁ f bf)
        (OverBase.compose-triangle q₁ F bF x₀ bx₀) α
      → OverBase.CompatibleOver q₂ (OverBase.compose-triangle q₂ x₂ bx₂ g bg)
        (OverBase.compose-triangle q₂ G bG x₁ bx₁) β
      → OverBase.CompatibleOver q₂ b₀ b₅ pasted
    compatible first second =
      let e₁ = (comp-assoc f g x₂) ⁻¹
          e₂ = β ▷ f
          e₃ = comp-assoc f x₁ G
          e₄ = G ◁ α
          e₅ = (comp-assoc x₀ F G) ⁻¹
          s₁ = OverBase.compatible-inverse q₂ b₁ b₀ (comp-assoc f g x₂)
            (OverBase.compatible-assoc q₂ x₂ g f bx₂ bg bf)
          s₂ = OverBase.compatible-pre q₂ f
            (OverBase.compose-triangle q₂ x₂ bx₂ g bg) (OverBase.compose-triangle q₂ G bG x₁ bx₁) bf β second
          s₃ = OverBase.compatible-assoc q₂ G x₁ f bG bx₁ bf
          s₄ = OverBase.compatible-post q₂ G bG
            (OverBase.compose-triangle q₁ x₁ bx₁ f bf) (OverBase.compose-triangle q₁ F bF x₀ bx₀) α first
          s₅ = OverBase.compatible-inverse q₂ b₅ b₄ (comp-assoc x₀ F G)
            (OverBase.compatible-assoc q₂ G F x₀ bG bF bx₀)
      in OverBase.compatible-comp q₂ b₀ b₄ b₅ e₅ (e₄ ∙ (e₃ ∙ (e₂ ∙ e₁))) s₅
        (OverBase.compatible-comp q₂ b₀ b₃ b₄ e₄ (e₃ ∙ (e₂ ∙ e₁)) s₄
          (OverBase.compatible-comp q₂ b₀ b₂ b₃ e₃ (e₂ ∙ e₁) s₃
            (OverBase.compatible-comp q₂ b₀ b₁ b₂ e₂ e₁ s₂ s₁)))
-- Direct imports: Identifications.OverBase qualified OverBase;
-- Squares.square and comp-square. No new abstract coherence law.


-- Normalize the identity coordinate of the ACTUAL product compositors.
-- These are the fixed-coordinate inputs to SwapProjectionPasting.
private
  module FixedCompositorNormalization {Γ : Context} {X Y Z P : CAT Γ}
    (πX : MAP X P) (πY : MAP Y P) (πZ : MAP Z P)
    (F : MAP X Y) (G : MAP Y Z) (K : MAP X Z)
    (ξ : (G ∘ F) =₁ K)
    (βF : (πY ∘ F) =₁ (id P ∘ πX))
    (βG : (πZ ∘ G) =₁ (id P ∘ πY))
    (βK : (πZ ∘ K) =₁ (id P ∘ πX))
    (image : SquareCell₌ (πZ ◁ ξ) (βF ∙ (comp-unitˡ πY ▷ F))
      (restrict-triangle πZ G βG F) βK) where
    private
      raw-source = restrict-triangle πZ G βG F
      unitX = comp-unitˡ πX
      unitY = comp-unitˡ πY
      Ainv = (comp-assoc F G πZ) ⁻¹
    source = OverBase.compose-triangle πZ G (unitY ∙ βG) F (unitX ∙ βF)
    target = unitX ∙ βK
    private
      source-normal : source =₂ (unitX ∙ ((βF ∙ (unitY ▷ F)) ∙ raw-source))
      source-normal = reassociateFour unitX βF (unitY ▷ F) raw-source ∙
        (comp₌-cong (id₌ (unitX ∙ βF))
          (comp₌-assoc (unitY ▷ F) (βG ▷ F) Ainv) ∙
          comp₌-cong (id₌ (unitX ∙ βF))
            (comp₌-cong (preWhisker-comp₌ unitY βG F) (id₌ Ainv)))
    compatible : (target ∙ (πZ ◁ ξ)) =₂ source
    compatible = source-normal ⁻¹ ∙
      (comp₌-cong (id₌ unitX) image ∙ comp₌-assoc unitX βK (πZ ◁ ξ))

  module FixedProductCompositorCoordinates {Γ : Context} (P : CAT Γ)
    {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    private
      Jf = product-restriction {P = P} f
      Jg = product-restriction {P = P} g
      Jgf = product-restriction {P = P} (g ∘ f)
      Hf = productMap f (id P)
      Hg = productMap g (id P)
      Hgf = productMap (g ∘ f) (id P)
      βJf = pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)
      βJg = pair-β₁ (id P ∘ pr₁) (g ∘ pr₂)
      βJgf = pair-β₁ (id P ∘ pr₁) ((g ∘ f) ∘ pr₂)
      βHf = pair-β₂ (f ∘ pr₁) (id P ∘ pr₂)
      βHg = pair-β₂ (g ∘ pr₁) (id P ∘ pr₂)
      βHgf = pair-β₂ ((g ∘ f) ∘ pr₁) (id P ∘ pr₂)
      first-coordinate = post-square-cell (id P) pr₁ (id P) pr₁ Jf βJf
      second-coordinate = post-square-cell g pr₂ f pr₂ Jf
        (pair-β₂ (id P ∘ pr₁) (f ∘ pr₂))
      J-image : SquareCell₌ (pr₁ ◁ restriction-compositor {P = P} f g)
        (βJf ∙ (comp-unitˡ pr₁ ▷ Jf))
        (restrict-triangle pr₁ Jg βJg Jf) βJgf
      J-image = replace-edges₌ (id₌ _) (post-square-cell-id pr₁ (id P) pr₁ Jf βJf)
        (lies-over-comp pr₁
          (pair-evaluation-over₁-One (id P ∘ pr₁) (g ∘ pr₂) Jf first-coordinate second-coordinate)
          (unconst-sides₌ (productMap-cong-triangle₁ (comp-unitˡ (id P)) (id₌ (g ∘ f)))))
      H-image : SquareCell₌ (pr₂ ◁ productMap-first-comp {C = P} g f)
        (βHf ∙ (comp-unitˡ pr₂ ▷ Hf))
        (restrict-triangle pr₂ Hg βHg Hf) βHgf
      H-image = replace-edges₌ (id₌ _) (FirstFactor.second-normalization P g f)
        (FirstFactor.Coordinates.projection₂ P g f)
      module J = FixedCompositorNormalization pr₁ pr₁ pr₁ Jf Jg Jgf
        (restriction-compositor f g) βJf βJg βJgf J-image
        using (compatible; source; target)
      module H = FixedCompositorNormalization pr₂ pr₂ pr₂ Hf Hg Hgf
        (productMap-first-comp g f) βHf βHg βHgf H-image
        using (compatible; source; target)
    restriction-source = J.source
    restriction-target = J.target
    first-factor-source = H.source
    first-factor-target = H.target
    restriction : (restriction-target ∙ (pr₁ ◁ restriction-compositor {P = P} f g)) =₂ restriction-source
    restriction = J.compatible
    first-factor : (first-factor-target ∙ (pr₂ ◁ productMap-first-comp {C = P} g f)) =₂ first-factor-source
    first-factor = H.compatible
-- Direct imports: OverBase; FirstFactorSubstitution as FirstFactor;
-- ProductFunctorCoherence.productMap-first-comp;
-- PairingRestriction.pair-evaluation-over₁-One;
-- ProductFunctor.productMap-cong-triangle₁; Triangles.post-square-cell-id.


-- Fixed-coordinate part of the ACTUAL swap compositor comparison.
private
  module SwapCompositorFixedCoordinate {Γ : Context} (P : CAT Γ)
    {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    private
      module Sf = SwapRestriction {P = P} f
        using (H; J; pA; pB; transpose-cell)
      module Sg = SwapRestriction {P = P} g
        using (H; J; pB; transpose-cell)
      module Sgf = SwapRestriction {P = P} (g ∘ f)
        using (transpose-cell)
      module If = SwapRestrictionOverProjections {P = P} f
        using (fixed)
      module Ig = SwapRestrictionOverProjections {P = P} g
        using (fixed)
      module Igf = SwapRestrictionOverProjections {P = P} (g ∘ f)
        using (fixed; fixed-source; fixed-target)
      module K = FixedProductCompositorCoordinates P f g
        using (first-factor; first-factor-source; first-factor-target; restriction; restriction-source; restriction-target)
      κH = productMap-first-comp {C = P} g f
      κJ = restriction-compositor {P = P} f g
      module Paste = SwapProjectionPasting pr₂ pr₂ pr₂ pr₁ pr₁ pr₁
        Sf.pA Sf.pB Sg.pB Sf.H Sg.H Sf.J Sg.J
        (comp-unitˡ pr₂ ∙ pair-β₂ (f ∘ pr₁) (id P ∘ pr₂))
        (comp-unitˡ pr₂ ∙ pair-β₂ (g ∘ pr₁) (id P ∘ pr₂))
        (comp-unitˡ pr₁ ∙ pair-β₁ (id P ∘ pr₁) (f ∘ pr₂))
        (comp-unitˡ pr₁ ∙ pair-β₁ (id P ∘ pr₁) (g ∘ pr₂))
        (pair-β₁ pr₂ pr₁) (pair-β₁ pr₂ pr₁) (pair-β₁ pr₂ pr₁)
        Sf.transpose-cell Sg.transpose-cell
        using (b₀; b₅; compatible; pasted)
    short = Sgf.transpose-cell ∙ (Sg.pB ◁ κH)
    long = (κJ ▷ Sf.pA) ∙ Paste.pasted
    private
      short-compatible : (Igf.fixed-target ∙ (pr₁ ◁ short)) =₂ Paste.b₀
      short-compatible = OverBase.compatible-comp pr₁ Paste.b₀ Igf.fixed-source Igf.fixed-target
        Sgf.transpose-cell (Sg.pB ◁ κH) Igf.fixed
        (OverBase.compatible-post pr₁ Sg.pB (pair-β₁ pr₂ pr₁)
          K.first-factor-source K.first-factor-target κH K.first-factor)
      long-compatible : (Igf.fixed-target ∙ (pr₁ ◁ long)) =₂ Paste.b₀
      long-compatible = OverBase.compatible-comp pr₁ Paste.b₀ Paste.b₅ Igf.fixed-target
        (κJ ▷ Sf.pA) Paste.pasted
        (OverBase.compatible-pre pr₁ Sf.pA K.restriction-source K.restriction-target
          (pair-β₁ pr₂ pr₁) κJ K.restriction)
        (Paste.compatible If.fixed Ig.fixed)
    comparison : (pr₁ ◁ short) =₂ (pr₁ ◁ long)
    comparison = cancel-left Igf.fixed-target (long-compatible ⁻¹ ∙ short-compatible)
-- No equality of the entire swapped cells is claimed from this one coordinate.


-- Varying-coordinate images of the ACTUAL two product compositors.
private
  module VaryingCompositorNormalization {Γ : Context} {X Z T : CAT Γ}
    (π : MAP Z T) {F K : MAP X Z} (ξ : F =₁ K)
    {a b d : MAP X T} (source : (π ∘ F) =₁ a) (target : (π ∘ K) =₁ b)
    (η : b =₁ d) (L : a =₁ d)
    (image : SquareCell₌ (π ◁ ξ) (η ⁻¹ ∙ L) source target) where
    compatible : ((η ∙ target) ∙ (π ◁ ξ)) =₂ (L ∙ source)
    compatible = comp-inv-left η (L ∙ source) ∙
      (comp₌-cong (id₌ η) (comp₌-assoc (η ⁻¹) L source) ∙
        (comp₌-cong (id₌ η) image ∙ comp₌-assoc η target (π ◁ ξ)))

  module VaryingProductCompositorCoordinates {Γ : Context} (P : CAT Γ)
    {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    private
      Jf = product-restriction {P = P} f
      Jg = product-restriction {P = P} g
      Hf = productMap f (id P)
      Hg = productMap g (id P)
      βJf = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)
      βJg = pair-β₂ (id P ∘ pr₁) (g ∘ pr₂)
      βJgf = pair-β₂ (id P ∘ pr₁) ((g ∘ f) ∘ pr₂)
      βHf = pair-β₁ (f ∘ pr₁) (id P ∘ pr₂)
      βHg = pair-β₁ (g ∘ pr₁) (id P ∘ pr₂)
      βHgf = pair-β₁ ((g ∘ f) ∘ pr₁) (id P ∘ pr₂)
      module J = VaryingCompositorNormalization pr₂ (restriction-compositor {P = P} f g)
        (restrict-triangle pr₂ Jg βJg Jf) βJgf
        (comp-assoc pr₂ f g) (post-triangle g pr₂ Jf βJf)
        (ProjectionCompositor.square {P = P} f g)
        using (compatible)
      module H = VaryingCompositorNormalization pr₁ (productMap-first-comp {C = P} g f)
        (restrict-triangle pr₁ Hg βHg Hf) βHgf
        (comp-assoc pr₁ f g) (post-triangle g pr₁ Hf βHf)
        (FirstFactor.Coordinates.projection₁ P g f)
        using (compatible)
    restriction-source = OverBase.compose-triangle pr₂ Jg βJg Jf (post-triangle g pr₂ Jf βJf)
    restriction-target = comp-assoc pr₂ f g ∙ βJgf
    first-factor-source = OverBase.compose-triangle pr₁ Hg βHg Hf (post-triangle g pr₁ Hf βHf)
    first-factor-target = comp-assoc pr₁ f g ∙ βHgf
    restriction : (restriction-target ∙ (pr₂ ◁ restriction-compositor {P = P} f g)) =₂ restriction-source
    restriction = J.compatible
    first-factor : (first-factor-target ∙ (pr₁ ◁ productMap-first-comp {C = P} g f)) =₂ first-factor-source
    first-factor = H.compatible
-- Variable source/target coordinate labels preserve their actual associators.


-- Varying-coordinate part of the ACTUAL swap compositor comparison.
private
  module SwapCompositorVaryingCoordinate {Γ : Context} (P : CAT Γ)
    {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    private
      module Sf = SwapRestriction {P = P} f
        using (H; J; pA; pB; transpose-cell)
      module Sg = SwapRestriction {P = P} g
        using (H; J; pB; transpose-cell)
      module Sgf = SwapRestriction {P = P} (g ∘ f)
        using (H; J; pB; transpose-cell)
      module If = SwapRestrictionOverProjections {P = P} f
        using (varying; varying-source; varying-target)
      module Ig = SwapRestrictionOverProjections {P = P} g
        using (varying)
      module Igf = SwapRestrictionOverProjections {P = P} (g ∘ f)
        using (varying; varying-source; varying-target)
      module K = VaryingProductCompositorCoordinates P f g
        using (first-factor; first-factor-source; first-factor-target; restriction; restriction-source; restriction-target)
      κH = productMap-first-comp {C = P} g f
      κJ = restriction-compositor {P = P} f g
      swapA : ((pr₂ {Γ = Γ} {C = P} {D = A}) ∘ Sf.pA) =₁ (pr₁ {Γ = Γ} {C = A} {D = P})
      swapA = pair-β₂ {Γ = Γ} {P = A × P} {C = P} {D = A}
        (pr₂ {Γ = Γ} {C = A} {D = P}) (pr₁ {Γ = Γ} {C = A} {D = P})
      swapB : ((pr₂ {Γ = Γ} {C = P} {D = B}) ∘ Sf.pB) =₁ (pr₁ {Γ = Γ} {C = B} {D = P})
      swapB = pair-β₂ {Γ = Γ} {P = B × P} {C = P} {D = B}
        (pr₂ {Γ = Γ} {C = B} {D = P}) (pr₁ {Γ = Γ} {C = B} {D = P})
      swapC : ((pr₂ {Γ = Γ} {C = P} {D = C}) ∘ Sg.pB) =₁ (pr₁ {Γ = Γ} {C = C} {D = P})
      swapC = pair-β₂ {Γ = Γ} {P = C × P} {C = P} {D = C}
        (pr₂ {Γ = Γ} {C = C} {D = P}) (pr₁ {Γ = Γ} {C = C} {D = P})
      Hf-base = pair-β₁ (f ∘ pr₁) (id P ∘ pr₂)
      Hg-base = pair-β₁ (g ∘ pr₁) (id P ∘ pr₂)
      Hgf-base = pair-β₁ ((g ∘ f) ∘ pr₁) (id P ∘ pr₂)
      Jf-base = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)
      Jg-base = pair-β₂ (id P ∘ pr₁) (g ∘ pr₂)
      Jgf-base = pair-β₂ (id P ∘ pr₁) ((g ∘ f) ∘ pr₂)
      lifted-swapA = post-triangle f pr₂ Sf.pA swapA
      nested-swapA = post-triangle g (f ∘ pr₂) Sf.pA lifted-swapA
      lifted-swapB = post-triangle g pr₂ Sf.pB swapB
      module Paste = SwapProjectionPasting {Γ = Γ}
        {X₀ = A × P} {X₁ = B × P} {X₂ = C × P}
        {Y₀ = P × A} {Y₁ = P × B} {Y₂ = P × C} {T = C}
        (g ∘ (f ∘ pr₁ {Γ = Γ} {C = A} {D = P})) (g ∘ pr₁ {Γ = Γ} {C = B} {D = P}) (pr₁ {Γ = Γ} {C = C} {D = P})
        (g ∘ (f ∘ pr₂ {Γ = Γ} {C = P} {D = A})) (g ∘ pr₂ {Γ = Γ} {C = P} {D = B}) (pr₂ {Γ = Γ} {C = P} {D = C})
        Sf.pA Sf.pB Sg.pB Sf.H Sg.H Sf.J Sg.J
        (post-triangle g (pr₁ {Γ = Γ} {C = B} {D = P}) Sf.H Hf-base) Hg-base
        (post-triangle g (pr₂ {Γ = Γ} {C = P} {D = B}) Sf.J Jf-base) Jg-base
        nested-swapA lifted-swapB swapC Sf.transpose-cell Sg.transpose-cell
        using (b₀; b₅; compatible; pasted)
      ηH : ((g ∘ f) ∘ pr₁ {Γ = Γ} {C = A} {D = P}) =₁ (g ∘ (f ∘ pr₁ {Γ = Γ} {C = A} {D = P}))
      ηH = comp-assoc {Γ = Γ} {B = A × P} {C = A} {D = B} {E = C}
        (pr₁ {Γ = Γ} {C = A} {D = P}) f g
      ηJ : ((g ∘ f) ∘ pr₂ {Γ = Γ} {C = P} {D = A}) =₁ (g ∘ (f ∘ pr₂ {Γ = Γ} {C = P} {D = A}))
      ηJ = comp-assoc {Γ = Γ} {B = P × A} {C = A} {D = B} {E = C}
        (pr₂ {Γ = Γ} {C = P} {D = A}) f g
      final = OverBase.compose-triangle pr₂ Sgf.J K.restriction-target Sf.pA nested-swapA
      middle = OverBase.compose-triangle pr₂ Sgf.pB swapC Sgf.H K.first-factor-target
      first-source-normal :
        OverBase.compose-triangle (g ∘ pr₂) Sf.pB lifted-swapB Sf.H (post-triangle g pr₁ Sf.H Hf-base)
          =₂ post-triangle g pr₂ (Sf.pB ∘ Sf.H) If.varying-source
      first-source-normal = OverBase.postcompose-compose g pr₂ Sf.pB Sf.H swapB Hf-base
      first-target-normal :
        OverBase.compose-triangle (g ∘ pr₂) Sf.J (post-triangle g pr₂ Sf.J Jf-base) Sf.pA nested-swapA
          =₂ post-triangle g pr₂ (Sf.J ∘ Sf.pA) If.varying-target
      first-target-normal = OverBase.postcompose-compose g pr₂ Sf.J Sf.pA Jf-base lifted-swapA
      first-compatible : OverBase.CompatibleOver (g ∘ pr₂)
        (OverBase.compose-triangle (g ∘ pr₂) Sf.pB lifted-swapB Sf.H (post-triangle g pr₁ Sf.H Hf-base))
        (OverBase.compose-triangle (g ∘ pr₂) Sf.J (post-triangle g pr₂ Sf.J Jf-base) Sf.pA nested-swapA)
        Sf.transpose-cell
      first-compatible = first-source-normal ⁻¹ ∙
        (OverBase.compatible-postcompose g pr₂ If.varying-source If.varying-target Sf.transpose-cell If.varying ∙
          comp₌-cong first-target-normal (id₌ ((g ∘ pr₂) ◁ Sf.transpose-cell)))
      middle-normal : middle =₂ (ηH ∙ Igf.varying-source)
      middle-normal = comp₌-assoc ηH Hgf-base (restrict-triangle pr₂ Sgf.pB swapC Sgf.H)
      lifted-assoc : (ηH ∙ post-triangle (g ∘ f) pr₂ Sf.pA swapA) =₂
        (nested-swapA ∙ (ηJ ▷ Sf.pA))
      lifted-assoc = (comp₌-assoc (g ◁ lifted-swapA)
        (comp-assoc Sf.pA (f ∘ pr₂) g) (ηJ ▷ Sf.pA)) ⁻¹ ∙
        post-triangle-comp g f pr₂ Sf.pA swapA
      change-middle : {X Y Z T : CAT Γ} (π : MAP Z T) (k : MAP Y Z) (j : MAP X Y)
        {a a′ : MAP Y T} {b b′ : MAP X T}
        (base : (π ∘ k) =₁ a) (before : (a ∘ j) =₁ b)
        (α : a =₁ a′) (after : (a′ ∘ j) =₁ b′) (η : b =₁ b′)
        → (η ∙ before) =₂ (after ∙ (α ▷ j))
        → OverBase.compose-triangle π k (α ∙ base) j after =₂
            (η ∙ OverBase.compose-triangle π k base j before)
      change-middle π k j base before α after η compatible =
        let inv-assoc = (comp-assoc j k π) ⁻¹
            tail = (base ▷ j) ∙ inv-assoc
        in comp₌-assoc η before tail ∙
          (comp₌-cong (compatible ⁻¹) (id₌ tail) ∙
            ((comp₌-assoc after (α ▷ j) tail) ⁻¹ ∙
              comp₌-cong (id₌ after)
                (comp₌-assoc (α ▷ j) (base ▷ j) inv-assoc ∙
                  comp₌-cong (preWhisker-comp₌ α base j) (id₌ inv-assoc))))
      final-normal : final =₂ (ηH ∙ Igf.varying-target)
      final-normal = change-middle pr₂ Sgf.J Sf.pA Jgf-base
        (post-triangle (g ∘ f) pr₂ Sf.pA swapA) ηJ nested-swapA ηH lifted-assoc
      composite-compatible : (final ∙ (pr₂ ◁ Sgf.transpose-cell)) =₂ middle
      composite-compatible = middle-normal ⁻¹ ∙
        (comp₌-cong (id₌ ηH) Igf.varying ∙
          (comp₌-assoc ηH Igf.varying-target (pr₂ ◁ Sgf.transpose-cell) ∙
            comp₌-cong final-normal (id₌ (pr₂ ◁ Sgf.transpose-cell))))
    short = Sgf.transpose-cell ∙ (Sg.pB ◁ κH)
    long = (κJ ▷ Sf.pA) ∙ Paste.pasted
    private
      short-compatible : (final ∙ (pr₂ ◁ short)) =₂ Paste.b₀
      short-compatible = OverBase.compatible-comp pr₂ Paste.b₀ middle final
        Sgf.transpose-cell (Sg.pB ◁ κH) composite-compatible
        (OverBase.compatible-post pr₂ Sg.pB swapC
          K.first-factor-source K.first-factor-target κH K.first-factor)
      long-compatible : (final ∙ (pr₂ ◁ long)) =₂ Paste.b₀
      long-compatible = OverBase.compatible-comp pr₂ Paste.b₀ Paste.b₅ final
        (κJ ▷ Sf.pA) Paste.pasted
        (OverBase.compatible-pre pr₂ Sf.pA K.restriction-source K.restriction-target
          nested-swapA κJ K.restriction)
        (Paste.compatible first-compatible Ig.varying)
    comparison : (pr₂ ◁ short) =₂ (pr₂ ◁ long)
    comparison = cancel-left final (long-compatible ⁻¹ ∙ short-compatible)
-- Direct additional imports: OverBase.postcompose-compose/compatible-postcompose;
-- TriangleCoherence.post-triangle-comp. Chosen κ, swap cells and associators retained.


-- Fixed-coordinate action of the ACTUAL productMap-cong cells.
private
  module FixedProductInputCoordinates {Γ : Context} (P : CAT Γ)
    {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g) where
    private
      module Normalization {X Y : CAT Γ} (π : MAP Y P) (ρ : MAP X P)
        {F G : MAP X Y} (δ : F =₁ G)
        (bf : (π ∘ F) =₁ (id P ∘ ρ)) (bg : (π ∘ G) =₁ (id P ∘ ρ))
        (image : SquareCell₌ (π ◁ δ) (id₌ (id P) ▷ ρ) bf bg) where
        raw : (bg ∙ (π ◁ δ)) =₂ bf
        raw = comp₌-unitˡ-One bf ∙
          (comp₌-cong (preWhisker-id₌ (id P) ρ) (id₌ bf) ∙ image)
        compatible : (((comp-unitˡ ρ ∙ bg) ∙ (π ◁ δ))) =₂ (comp-unitˡ ρ ∙ bf)
        compatible = comp₌-cong (id₌ (comp-unitˡ ρ)) raw ∙
          comp₌-assoc (comp-unitˡ ρ) bg (π ◁ δ)
      Jα = productMap-cong (id₌ (id P)) α
      Hα = productMap-cong α (id₌ (id P))
      Jf = product-restriction {P = P} f
      Jg = product-restriction {P = P} g
      Hf = productMap f (id P)
      Hg = productMap g (id P)
      βJf = pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)
      βJg = pair-β₁ (id P ∘ pr₁) (g ∘ pr₂)
      βHf = pair-β₂ (f ∘ pr₁) (id P ∘ pr₂)
      βHg = pair-β₂ (g ∘ pr₁) (id P ∘ pr₂)
      module J = Normalization pr₁ pr₁ Jα βJf βJg
        (unconst-sides₌ (productMap-cong-triangle₁ (id₌ (id P)) α))
        using (compatible)
      module H = Normalization pr₂ pr₂ Hα βHf βHg
        (unconst-sides₌ (productMap-cong-triangle₂ α (id₌ (id P))))
        using (compatible)
    restriction = J.compatible
    first-factor = H.compatible

  module SwapRestrictionInputCompatibility {Γ : Context} (P : CAT Γ)
    {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g) where
    private
      module Sf = SwapRestriction {P = P} f
        using (pA; pB; transpose-cell)
      module Sg = SwapRestriction {P = P} g
        using (transpose-cell)
      module If = SwapRestrictionOverProjections {P = P} f
        using (fixed; fixed-source; fixed-target; varying; varying-source; varying-target)
      module Ig = SwapRestrictionOverProjections {P = P} g
        using (fixed; fixed-source; fixed-target; varying; varying-source; varying-target)
      module Fixed = FixedProductInputCoordinates P α
        using (first-factor; restriction)
      Jα = productMap-cong (id₌ (id P)) α
      Hα = productMap-cong α (id₌ (id P))
      βJf₁ = pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)
      βJg₁ = pair-β₁ (id P ∘ pr₁) (g ∘ pr₂)
      βHf₂ = pair-β₂ (f ∘ pr₁) (id P ∘ pr₂)
      βHg₂ = pair-β₂ (g ∘ pr₁) (id P ∘ pr₂)
      βJf₂ = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)
      βJg₂ = pair-β₂ (id P ∘ pr₁) (g ∘ pr₂)
      βHf₁ = pair-β₁ (f ∘ pr₁) (id P ∘ pr₂)
      βHg₁ = pair-β₁ (g ∘ pr₁) (id P ∘ pr₂)
    left-route = Sg.transpose-cell ∙ (Sf.pB ◁ Hα)
    right-route = (Jα ▷ Sf.pA) ∙ Sf.transpose-cell
    private
      left-fixed : (Ig.fixed-target ∙ (pr₁ ◁ left-route)) =₂ If.fixed-source
      left-fixed = OverBase.compatible-comp pr₁ If.fixed-source Ig.fixed-source Ig.fixed-target
        Sg.transpose-cell (Sf.pB ◁ Hα) Ig.fixed
        (OverBase.compatible-post pr₁ Sf.pB (pair-β₁ pr₂ pr₁)
          (comp-unitˡ pr₂ ∙ βHf₂) (comp-unitˡ pr₂ ∙ βHg₂) Hα Fixed.first-factor)
      right-fixed : (Ig.fixed-target ∙ (pr₁ ◁ right-route)) =₂ If.fixed-source
      right-fixed = OverBase.compatible-comp pr₁ If.fixed-source If.fixed-target Ig.fixed-target
        (Jα ▷ Sf.pA) Sf.transpose-cell
        (OverBase.compatible-pre pr₁ Sf.pA
          (comp-unitˡ pr₁ ∙ βJf₁) (comp-unitˡ pr₁ ∙ βJg₁)
          (pair-β₁ pr₂ pr₁) Jα Fixed.restriction) If.fixed
      fixed : (pr₁ ◁ left-route) =₂ (pr₁ ◁ right-route)
      fixed = cancel-left Ig.fixed-target (right-fixed ⁻¹ ∙ left-fixed)
      H-variable : SquareCell₌ (pr₁ ◁ Hα) (α ▷ pr₁) βHf₁ βHg₁
      H-variable = unconst-sides₌ (productMap-cong-triangle₁ α (id₌ (id P)))
      J-variable : SquareCell₌ (pr₂ ◁ Jα) (α ▷ pr₂) βJf₂ βJg₂
      J-variable = unconst-sides₌ (productMap-cong-triangle₂ (id₌ (id P)) α)
      post-variable : SquareCell₌ (pr₂ ◁ (Sf.pB ◁ Hα)) (α ▷ pr₁)
        If.varying-source Ig.varying-source
      post-variable = paste-square₌
        (restrict-change-square-One pr₂ Sf.pB pr₁ (pair-β₂ pr₂ pr₁) Hα) H-variable
      pre-variable : SquareCell₌ (pr₂ ◁ (Jα ▷ Sf.pA)) (α ▷ pr₁)
        If.varying-target Ig.varying-target
      pre-variable = paste-square₌
        (restrict-square-One pr₂ Jα (α ▷ pr₂) βJf₂ βJg₂ Sf.pA J-variable)
        (unconst-sides₌ (post-triangle-outer α pr₂ Sf.pA (pair-β₂ pr₂ pr₁)))
      left-variable : SquareCell₌ (pr₂ ◁ left-route) (α ▷ pr₁) If.varying-source Ig.varying-target
      left-variable = replace-edges₌ (id₌ _) (comp₌-unitˡ-One (α ▷ pr₁))
        (lies-over-comp pr₂ post-variable
          ((comp₌-unitˡ-One Ig.varying-source) ⁻¹ ∙ Ig.varying))
      right-variable : SquareCell₌ (pr₂ ◁ right-route) (α ▷ pr₁) If.varying-source Ig.varying-target
      right-variable = replace-edges₌ (id₌ _) (comp₌-unitʳ-One (α ▷ pr₁))
        (lies-over-comp pr₂ ((comp₌-unitˡ-One If.varying-source) ⁻¹ ∙ If.varying) pre-variable)
      varying : (pr₂ ◁ left-route) =₂ (pr₂ ◁ right-route)
      varying = cancel-left Ig.varying-target (right-variable ⁻¹ ∙ left-variable)
    comparison : left-route =₂ right-route
    comparison = pair₌-extensionality fixed varying
-- Direct imports: Pairing.pair₌-extensionality; Triangles.restrict-change-square-One,
-- restrict-square-One, post-triangle-outer; productMap-cong-triangle₁/₂.


-- Whole actual swap compatibility of the supplied J/H product square.
private
  module SwapCompositorCompatibility {Γ : Context} (P : CAT Γ)
    {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
    private
      module F = SwapRestriction {P = P} f
        using (H; J; pA; transpose-cell)
      module G = SwapRestriction {P = P} g
        using (H; J; pB; transpose-cell)
      module GF = SwapRestriction {P = P} (g ∘ f)
        using (transpose-cell)
      module Fixed = SwapCompositorFixedCoordinate P f g
        using (comparison)
      module Variable = SwapCompositorVaryingCoordinate P f g
        using (comparison)
    pasted = Square.cell (comp-square (Squares.square G.H G.J G.transpose-cell) (Squares.square F.H F.J F.transpose-cell))
    comparison : (GF.transpose-cell ∙ (G.pB ◁ productMap-first-comp {C = P} g f)) =₂
      ((restriction-compositor {P = P} f g ▷ F.pA) ∙ pasted)
    comparison = pair₌-extensionality Fixed.comparison Variable.comparison

  module ProductSquareSwap {Γ : Context} (P : CAT Γ) {A B C D : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) where
    private
      u = Square.source-map s
      v = Square.target-map s
      module U = SwapRestriction {P = P} u
        using (H; J; pA; pB; transpose-cell)
      module L = SwapRestriction {P = P} l
        using (H; J; pB; transpose-cell)
      module R = SwapRestriction {P = P} r
        using (H; J; pB; transpose-cell)
      module V = SwapRestriction {P = P} v
        using (H; J; pB; transpose-cell)
      module RU = SwapRestriction {P = P} (r ∘ u)
        using (transpose-cell)
      module VL = SwapRestriction {P = P} (v ∘ l)
        using (transpose-cell)
      module H = FirstFactorSquare P s
        using (middle; value; κl; κu)
      module Change = ChangeSpan {E = P × D} U.J L.J U.H L.H U.pA U.pB L.pB
        U.transpose-cell L.transpose-cell
        using (value; module L; module R)
      ρr = Change.L.ρ R.J
      ρv = Change.R.ρ V.J
      Ar = comp-assoc U.H R.H R.pB
      Av = comp-assoc L.H V.H V.pB
      α = R.transpose-cell ⁻¹ ▷ U.H
      β = V.transpose-cell ⁻¹ ▷ L.H
      left-total = Ar ∙ (α ∙ ρr ⁻¹)
      right-total = Av ∙ (β ∙ ρv ⁻¹)
      source-cell = Square.cell (product-square {P = P} s) ▷ U.pA
      target-cell = R.pB ◁ Cocone.match H.value
      κJu = restriction-compositor {P = P} u r ▷ U.pA
      κJl = restriction-compositor {P = P} l v ▷ U.pA
      κHu = R.pB ◁ H.κu
      κHl = R.pB ◁ H.κl
      σJ = productMap-cong (id₌ (id P)) (Square.cell s) ▷ U.pA
      σH = R.pB ◁ H.middle
      module CompositorLeg {X Y Z : CAT Γ} (f : MAP X Y) (g : MAP Y Z) where
        private
          module F = SwapRestriction {P = P} f
            using (H; J; pA; pB; transpose-cell)
          module G = SwapRestriction {P = P} g
            using (H; J; pB; transpose-cell)
          module GF = SwapRestriction {P = P} (g ∘ f)
            using (transpose-cell)
          module K = SwapCompositorCompatibility P f g
            using (comparison; pasted)
          ρ = (comp-assoc F.pA F.J G.J) ⁻¹ ∙
            ((G.J ◁ F.transpose-cell) ∙ comp-assoc F.H F.pB G.J)
          outer-assoc = comp-assoc F.H G.H G.pB
          middle-assoc = comp-assoc F.H F.pB G.J
          input-assoc-inverse = (comp-assoc F.pA F.J G.J) ⁻¹
          middle = G.J ◁ F.transpose-cell
          tail = (G.transpose-cell ▷ F.H) ∙ outer-assoc ⁻¹
          group : K.pasted =₂ (ρ ∙ tail)
          group = (comp₌-assoc input-assoc-inverse (middle ∙ middle-assoc) tail) ⁻¹ ∙
            comp₌-cong (id₌ input-assoc-inverse) ((comp₌-assoc middle middle-assoc tail) ⁻¹)
        frame : (K.pasted ⁻¹) =₂ (outer-assoc ∙ ((G.transpose-cell ⁻¹ ▷ F.H) ∙ ρ ⁻¹))
        frame = comp₌-assoc outer-assoc (G.transpose-cell ⁻¹ ▷ F.H) (ρ ⁻¹) ∙
          (comp₌-cong
            (comp₌-cong (inverse-inverse outer-assoc) ((preWhisker-inverse G.transpose-cell F.H) ⁻¹) ∙
              inverse-composite (G.transpose-cell ▷ F.H) (outer-assoc ⁻¹)) (id₌ (ρ ⁻¹)) ∙
            (inverse-composite ρ tail ∙ (inv₌ ◁ group)))
        square : SquareCell₌ (restriction-compositor {P = P} f g ▷ F.pA)
          (G.pB ◁ productMap-first-comp {C = P} g f)
          (outer-assoc ∙ ((G.transpose-cell ⁻¹ ▷ F.H) ∙ ρ ⁻¹)) (GF.transpose-cell ⁻¹)
        square = replace-sides₌ frame (id₌ (GF.transpose-cell ⁻¹))
          (inverse-square₌ K.comparison)
      left-square : SquareCell₌ κJu κHu left-total (RU.transpose-cell ⁻¹)
      left-square = CompositorLeg.square u r
      right-square : SquareCell₌ κJl κHl right-total (VL.transpose-cell ⁻¹)
      right-square = CompositorLeg.square l v
      middle-square : SquareCell₌ σJ σH (RU.transpose-cell ⁻¹) (VL.transpose-cell ⁻¹)
      middle-square = inverse-square₌ (SwapRestrictionInputCompatibility.comparison P (Square.cell s))
      source-normal : source-cell =₂ (κJl ⁻¹ ∙ (σJ ∙ κJu))
      source-normal = comp₌-cong (preWhisker-inverse (restriction-compositor {P = P} l v) U.pA)
        (preWhisker-comp₌ (productMap-cong (id₌ (id P)) (Square.cell s))
          (restriction-compositor {P = P} u r) U.pA) ∙
          preWhisker-comp₌ ((restriction-compositor {P = P} l v) ⁻¹)
            (productMap-cong (id₌ (id P)) (Square.cell s) ∙ restriction-compositor {P = P} u r) U.pA
      target-normal : target-cell =₂ (κHl ⁻¹ ∙ (σH ∙ κHu))
      target-normal = comp₌-cong (postWhisker-inverse R.pB H.κl)
        (postWhisker-comp₌ R.pB H.middle H.κu) ∙
        postWhisker-comp₌ R.pB (H.κl ⁻¹) (H.middle ∙ H.κu)
      raw-square : SquareCell₌ source-cell target-cell left-total right-total
      raw-square = replace-edges₌ (source-normal ⁻¹) (target-normal ⁻¹)
        (inv-comp-square₌ (adjoin-square₌ left-square middle-square) right-square)
    source : Cocone U.H L.H (P × D)
    source = Change.value (square-cocone (product-square {P = P} s))
    target : Cocone U.H L.H (P × D)
    target = cocone-postcompose R.pB H.value
    private
      source-frame-normal : changeEndpoints (ρr ⁻¹) (ρv ⁻¹) source-cell =₂ Cocone.match source
      source-frame-normal = comp₌-cong (id₌ (ρv ⁻¹))
        (comp₌-cong (id₌ source-cell) (inverse-inverse ρr))
      target-frame-normal : changeEndpoints (Ar ⁻¹) (Av ⁻¹) target-cell =₂ Cocone.match target
      target-frame-normal = comp₌-cong (id₌ (Av ⁻¹))
        (comp₌-cong (id₌ target-cell) (inverse-inverse Ar))
    comparison : CoconeIdentification₁ source target
    comparison = record { left = R.transpose-cell ⁻¹; right = V.transpose-cell ⁻¹
      ; compatible = replace-sides₌ source-frame-normal target-frame-normal
          (transport-square (ρr ⁻¹) (Ar ⁻¹) (ρv ⁻¹) (Av ⁻¹) source-cell target-cell
            left-total right-total α β
            (inv-comp-left Ar (α ∙ ρr ⁻¹)) (inv-comp-left Av (β ∙ ρv ⁻¹))
            (transpose-square₌ raw-square)) }
-- Direct imports additionally: Pairing.pair₌-extensionality; Squares.square/comp-square.
-- No equality with independently chosen inverse mates is asserted.


-- Complete evaluated supplied-square comparison, carrying the actual swap choice.
module _ {Γ : Context} where
  module TransposedOrdinarySquareEvaluation {P A B C D E : CAT Γ}
    {l : MAP A C} {r : MAP B D} (s : Square l r) (g : MAP D (Fun P E)) where
    private
      u = Square.source-map s
      module Product = ProductSquareSwap P s
        using (comparison; source; target)
      module H = FirstFactorSquare P s
        using (value)
      module T = TransposedRestrictionCocones {P = P} {E = E} u l
        using (Hl; Hu; transposed)
      module O = NativeOrdinaryCocones {P = P} {E = E} u l
        using (represented)
      product = square-cocone (product-square {P = P} s)
      ordinary = square-cocone s
      e = funUncurry g
      pD : MAP (D × P) (P × D)
      pD = swap
      qD : MAP (P × D) (D × P)
      qD = swap
    transposed-map : MAP (P × D) E
    transposed-map = e ∘ qD
    source : Cocone T.Hu T.Hl E
    source = T.transposed (cocone-postcompose transposed-map product)
    target : Cocone T.Hu T.Hl E
    target = O.represented (cocone-postcompose g ordinary)
    private
      commuting : CoconeIdentification₁ source (cocone-postcompose transposed-map Product.source)
      commuting = change-span-postcomposition
        (product-restriction {P = P} u) (product-restriction {P = P} l)
        (productMap u (id P)) (productMap l (id P))
        (SwapRestriction.pA {P = P} u) (SwapRestriction.pB {P = P} u) (SwapRestriction.pB {P = P} l)
        (SwapRestriction.transpose-cell {P = P} u) (SwapRestriction.transpose-cell {P = P} l)
        transposed-map product
      swapped : CoconeIdentification₁
        (cocone-postcompose transposed-map Product.source)
        (cocone-postcompose transposed-map Product.target)
      swapped = fixed-postcomposition transposed-map Product.comparison
      associated : CoconeIdentification₁
        (cocone-postcompose transposed-map Product.target)
        (cocone-postcompose (transposed-map ∘ pD) H.value)
      associated = inverse-cocone₁ (postcompose-assoc H.value pD transposed-map)
      swap-beta : (transposed-map ∘ pD) =₁ e
      swap-beta = comp-unitʳ e ∙ ((e ◁ swap-swap D P) ∙ comp-assoc pD qD e)
      restored : CoconeIdentification₁ (cocone-postcompose (transposed-map ∘ pD) H.value)
        (cocone-postcompose e H.value)
      restored = postcomposition-cong₁ H.value swap-beta
    comparison : CoconeIdentification₁ source target
    comparison = compose-cocone₁
      (inverse-cocone₁ (OrdinaryFirstFactorSquareEvaluation.comparison s g))
      (compose-cocone₁ restored (compose-cocone₁ associated (compose-cocone₁ swapped commuting)))
-- Requires private ProductSquareSwap/FirstFactorSquare/ordinary evaluation,
-- and the already reviewed concrete postcomposition-cong₁ helper.
-- The source keeps e∘swap, before native currying's beta; no equality of mates.


-- Full independent family reflection for ordinary cocones evaluated natively.
module NativeOrdinaryReflectedCocone {Γ : Context} {X P A B C E : CAT Γ}
  (u : MAP A B) (l : MAP A C) (s t : Cocone u l (Fun P E))
  (Φ : CoconeIdentification X
    (NativeOrdinaryCocones.represented {P = P} {E = E} u l s)
    (NativeOrdinaryCocones.represented {P = P} {E = E} u l t)) where
  private
    e = funEval {C = P} {D = E}
    Ju = productMap u (id P)
    Jl = productMap l (id P)
  open Terms.Equalities X using (_＝_)
  left : Cocone.left s ＝ Cocone.left t
  left = reflect e (funUniversal P E) (Cocone.left s) (Cocone.left t) (CoconeIdentification.left Φ)
  right : Cocone.right s ＝ Cocone.right t
  right = reflect e (funUniversal P E) (Cocone.right s) (Cocone.right t) (CoconeIdentification.right Φ)
  left-image : evaluate⁼ e left =₁ CoconeIdentification.left Φ
  left-image = reflect-β e (funUniversal P E) (Cocone.left s) (Cocone.left t) (CoconeIdentification.left Φ)
  right-image : evaluate⁼ e right =₁ CoconeIdentification.right Φ
  right-image = reflect-β e (funUniversal P E) (Cocone.right s) (Cocone.right t) (CoconeIdentification.right Φ)
  private
    left-square : SquareCell₌ (evaluate⁼ e (left ▷ u)) (CoconeIdentification.left Φ ▷ Ju)
      (const (evaluate-restrict e (Cocone.left s) u)) (const (evaluate-restrict e (Cocone.left t) u))
    left-square = replace-edges₌ (id₌ (evaluate⁼ e (left ▷ u)))
      (preWhisker Ju ◁ left-image) (evaluate-restrict-inputs e left u)
    right-square : SquareCell₌ (evaluate⁼ e (right ▷ l)) (CoconeIdentification.right Φ ▷ Jl)
      (const (evaluate-restrict e (Cocone.right s) l)) (const (evaluate-restrict e (Cocone.right t) l))
    right-square = replace-edges₌ (id₌ (evaluate⁼ e (right ▷ l)))
      (preWhisker Jl ◁ right-image) (evaluate-restrict-inputs e right l)
  source-boundary = const {P = X} (Cocone.match t) ∙ (left ▷ u)
  target-boundary = (right ▷ l) ∙ const {P = X} (Cocone.match s)
  native-action = evaluation-action e (Cocone.left s ∘ u) (Cocone.right t ∘ l)
  wanted-image : (native-action ∘ source-boundary) =₁ (native-action ∘ target-boundary)
  wanted-image = framed-matching-image e (Cocone.match s) (Cocone.match t) (left ▷ u) (right ▷ l)
    (evaluate-restrict e (Cocone.left s) u) (evaluate-restrict e (Cocone.right s) l)
    (evaluate-restrict e (Cocone.left t) u) (evaluate-restrict e (Cocone.right t) l)
    left-square right-square (CoconeIdentification.compatible Φ)
  matching-factor : Fact.Factorization (postWhisker native-action) wanted-image
  matching-factor = evaluation-reflection₂ e (funUniversal P E)
    source-boundary target-boundary wanted-image
  compatible : SquareCell₌ (left ▷ u) (right ▷ l) (const (Cocone.match s)) (const (Cocone.match t))
  compatible = Fact.factor matching-factor
  matching-image : (postWhisker native-action ∘ compatible) =₁ wanted-image
  matching-image = Fact.triangle matching-factor
  value : CoconeIdentification X s t
  value = record { left = left; right = right; compatible = compatible }

-- This is the existing native restriction-reflection calculation with the
-- ordinary evaluation-restrict endpoint squares. No anima hypothesis on P.

```
