# Substitution of a represented precomposition

A supplied evaluation triangle defines the indexed precomposition comparison.
Its compatibility with parameter restriction follows from the actual product
separation and evaluation substitution calculations. A complete finite square
for a selected compositor induces its indexed square, retaining both beta
comparisons, the evaluated associator, and the product restriction compositor.
The crossing calculation and intermediate routes are private.

```agda
{-# OPTIONS --without-K --lossy-unification #-}
module SCT.VolumeI.Chapter01.Section07.PreEvaluationSubstitution where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary hiding (_＝_)
import SCT.VolumeI.Chapter01.Section01.Terms as Terms
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.Whiskering using (preWhisker-id; postWhisker-id)
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap; productMap-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong₂; productMap-cong-triangle₁; productMap-cong-triangle₂;
    productMap-cong-comp; productMap-cong-id-One; productMap-cong-square)
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square; comp-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (inverse-unique; inverse-composite; inverse-inverse; postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; comp₌-inverseˡ-One; cancel-left; cancel-right)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (pentagon-whiskered-right; whisker-mixed-One; postWhisker-comp-One; preWhisker-comp-One;
    triangle-whiskered; identity-unitors; right-unitor-comp; left-unitor-comp; postWhisker-id-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-triangle; post-square-cell; post-square-cell-id; post-square-cell-comp;
    lies-over-comp; restrict-triangle; restrict-triangle-assoc; restrict-change-square-One; restrict-square-One)
open import SCT.VolumeI.Chapter01.Section02.Products using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate; productMap-first-comp; productMap-comp-natural-outer-One; productMap-comp-natural-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-unique)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; square-to-changeEndpoints; transport-square; reflect-transported-square; changeEndpoints-extend-square)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
open import SCT.VolumeI.Chapter01.Section07.Evaluation
open import SCT.VolumeI.Chapter01.Section07.EvaluationRepresentation using (evaluate-restrict-inputs)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution using (evaluate-restrict-assoc)

private
  module CrossingEvaluationCalculation where
    module _ {Γ : Context} where
      -- Two adjacent commuting crossings compare f/g with F/G through
      -- s₀/s₁/s₂. Supplied evaluation triangles at the two target functors
      -- and the outer parameter changes induce evaluation of their COMPLETE
      -- five-factor paste. The premise is the entire outer evaluation square;
      -- the result retains the induced input/output triangles and action.
      module EvaluatedCrossingPaste {A₀ A₁ A₂ B₀ B₁ B₂ E : CAT Γ}
        (f : MAP A₀ A₁) (g : MAP A₁ A₂) (F : MAP B₀ B₁) (G : MAP B₁ B₂)
        (s₀ : MAP A₀ B₀) (s₁ : MAP A₁ B₁) (s₂ : MAP A₂ B₂)
        (π : MAP B₂ E) (ρ : MAP A₂ E) (u : MAP B₁ E) (v : MAP A₁ E)
        (q : (π ∘ s₂) =₁ ρ) (b : (π ∘ G) =₁ u) (B : (ρ ∘ g) =₁ v)
        (β : (s₂ ∘ g) =₁ (G ∘ s₁)) (α : (s₁ ∘ f) =₁ (F ∘ s₀))
        (ν : v =₁ (u ∘ s₁)) where
        source = restrict-triangle ρ g B f ∙ restrict-triangle π s₂ q (g ∘ f)
        first = restrict-triangle π (s₂ ∘ g) (B ∙ restrict-triangle π s₂ q g) f
        second = restrict-triangle π (G ∘ s₁) (restrict-triangle π G b s₁) f
        third = restrict-triangle π G b (s₁ ∘ f)
        fourth = restrict-triangle π G b (F ∘ s₀)
        target = restrict-triangle π (G ∘ F) (restrict-triangle π G b F) s₀
        action = (comp-assoc s₀ F u) ⁻¹ ∙
          ((u ◁ α) ∙ (comp-assoc f s₁ u ∙ (ν ▷ f)))
        r₁ = (comp-assoc f g s₂) ⁻¹
        r₂ = β ▷ f
        r₃ = comp-assoc f s₁ G
        r₄ = G ◁ α
        r₅ = (comp-assoc s₀ F G) ⁻¹
        chain = r₅ ∙ (r₄ ∙ (r₃ ∙ (r₂ ∙ r₁)))

        private
          composite-triangle : {X Y Z T : CAT Γ} (e : MAP Z T)
            (z : MAP Y Z) {x y : MAP Y T} (a : (e ∘ z) =₁ x) (c : x =₁ y)
            (r : MAP X Y) → restrict-triangle e z (c ∙ a) r =₂
              ((c ▷ r) ∙ restrict-triangle e z a r)
          composite-triangle e z a c r =
            comp₌-assoc (c ▷ r) (a ▷ r) ((comp-assoc r z e) ⁻¹) ∙
              comp₌-cong (preWhisker-comp₌ c a r) (id₌ ((comp-assoc r z e) ⁻¹))
          nested : (source ∙ (π ◁ comp-assoc f g s₂)) =₂ first
          nested = (composite-triangle π (s₂ ∘ g) (restrict-triangle π s₂ q g) B f) ⁻¹ ∙
            (comp₌-cong (id₌ (B ▷ f))
              (inv-comp-left (comp-assoc f g ρ)
                (restrict-triangle π (s₂ ∘ g) (restrict-triangle π s₂ q g) f)) ∙
              (comp₌-assoc (B ▷ f) ((comp-assoc f g ρ) ⁻¹)
                (comp-assoc f g ρ ∙ restrict-triangle π (s₂ ∘ g) (restrict-triangle π s₂ q g) f) ∙
                (comp₌-cong (id₌ (restrict-triangle ρ g B f))
                  (restrict-triangle-assoc π s₂ q g f) ∙
                    comp₌-assoc (restrict-triangle ρ g B f)
                      (restrict-triangle π s₂ q (g ∘ f)) (π ◁ comp-assoc f g s₂))))
          first-square : SquareCell₌ (π ◁ r₁) (id₌ (v ∘ f)) source first
          first-square = (comp₌-unitˡ-One source) ⁻¹ ∙
            (comp-inv-right source (π ◁ comp-assoc f g s₂) ∙
              (comp₌-cong (nested ⁻¹) (id₌ ((π ◁ comp-assoc f g s₂) ⁻¹)) ∙
                comp₌-cong (id₌ first) (postWhisker-inverse π (comp-assoc f g s₂))))
          third-square : SquareCell₌ (π ◁ r₃) (comp-assoc f s₁ u) second third
          third-square = restrict-triangle-assoc π G b s₁ f
          fourth-square : SquareCell₌ (π ◁ r₄) (u ◁ α) third fourth
          fourth-square = restrict-change-square-One π G u b α
          fifth-square : SquareCell₌ (π ◁ r₅) ((comp-assoc s₀ F u) ⁻¹) fourth target
          fifth-square = replace-edges₌ ((postWhisker-inverse π (comp-assoc s₀ F G)) ⁻¹) (id₌ _)
            (transpose-square₌ (inverse-square₌
              (transpose-square₌ (restrict-triangle-assoc π G b F s₀))))

        compatibility : SquareCell₌ (π ◁ β) ν
          (B ∙ restrict-triangle π s₂ q g) (restrict-triangle π G b s₁)
          → SquareCell₌ (π ◁ chain) action source target
        compatibility square =
          let second-square = restrict-square-One π β ν
                (B ∙ restrict-triangle π s₂ q g) (restrict-triangle π G b s₁) f square
              first-two = replace-edges₌ (id₌ _) (comp₌-unitʳ-One (ν ▷ f))
                (lies-over-comp π first-square second-square)
          in lies-over-comp π
            (lies-over-comp π (lies-over-comp π first-two third-square) fourth-square) fifth-square

private
  module _ {Γ : Context} where
    inverse-three : {X Y : CAT Γ} {a₀ a₁ a₂ a₃ : MAP X Y}
      (c : a₂ =₁ a₃) (b : a₁ =₁ a₂) (a : a₀ =₁ a₁)
      → ((c ∙ (b ∙ a)) ⁻¹) =₂ (a ⁻¹ ∙ (b ⁻¹ ∙ c ⁻¹))
    inverse-three c b a = comp₌-assoc (a ⁻¹) (b ⁻¹) (c ⁻¹) ∙
      (comp₌-cong (inverse-composite b a) (id₌ (c ⁻¹)) ∙ inverse-composite c (b ∙ a))
    inverse-five : {X Y : CAT Γ} {a₀ a₁ a₂ a₃ a₄ a₅ : MAP X Y}
      (e : a₄ =₁ a₅) (d : a₃ =₁ a₄) (c : a₂ =₁ a₃)
      (b : a₁ =₁ a₂) (a : a₀ =₁ a₁)
      → ((e ∙ (d ∙ (c ∙ (b ∙ a)))) ⁻¹) =₂
        (a ⁻¹ ∙ (b ⁻¹ ∙ (c ⁻¹ ∙ (d ⁻¹ ∙ e ⁻¹))))
    inverse-five e d c b a = comp₌-cong (id₌ (a ⁻¹))
      (comp₌-assoc (b ⁻¹) (c ⁻¹) (d ⁻¹ ∙ e ⁻¹)) ∙
      (comp₌-assoc (a ⁻¹) (b ⁻¹ ∙ c ⁻¹) (d ⁻¹ ∙ e ⁻¹) ∙
        (comp₌-cong (inverse-three c b a) (id₌ (d ⁻¹ ∙ e ⁻¹)) ∙
          inverse-three e d (c ∙ (b ∙ a))))

    inverse-four : {X Y : CAT Γ} {a₀ a₁ a₂ a₃ a₄ : MAP X Y}
      (d : a₃ =₁ a₄) (c : a₂ =₁ a₃) (b : a₁ =₁ a₂) (a : a₀ =₁ a₁)
      → ((d ∙ (c ∙ (b ∙ a))) ⁻¹) =₂ (a ⁻¹ ∙ (b ⁻¹ ∙ (c ⁻¹ ∙ d ⁻¹)))
    inverse-four d c b a = comp₌-cong (id₌ (a ⁻¹))
      (comp₌-assoc (b ⁻¹) (c ⁻¹) (d ⁻¹)) ∙
      (comp₌-assoc (a ⁻¹) (b ⁻¹ ∙ c ⁻¹) (d ⁻¹) ∙
        (comp₌-cong (inverse-three c b a) (id₌ (d ⁻¹)) ∙ inverse-composite d (c ∙ (b ∙ a))))
    solve-square : {X Y : CAT Γ} {a₀ a₁ a₂ a₃ : MAP X Y}
      (a : a₂ =₁ a₃) (b : a₁ =₁ a₃) (c : a₀ =₁ a₂) (d : a₀ =₁ a₁)
      → (a ∙ c) =₂ (b ∙ d) → (a ⁻¹ ∙ b) =₂ (c ∙ d ⁻¹)
    solve-square a b c d square = comp₌-cong (inv-comp-left a c) (id₌ (d ⁻¹)) ∙
      ((comp₌-assoc (a ⁻¹) (a ∙ c) (d ⁻¹)) ⁻¹ ∙
        comp₌-cong (id₌ (a ⁻¹))
          (comp₌-cong (square ⁻¹) (id₌ (d ⁻¹)) ∙ (comp-inv-right b d) ⁻¹))

private
  module _ {Γ : Context} {F C E : CAT Γ} (e : MAP (F × C) E) where
    scalar-restrict-inputs : {S T : CAT Γ} {h k : MAP T F}
      (α : h =₁ k) (r : MAP S T)
      → SquareCell₌ (evaluate-cong e (α ▷ r))
          (evaluate-cong e α ▷ productMap r (id C))
          (evaluate-restrict e h r) (evaluate-restrict e k r)
    scalar-restrict-inputs α r = replace-edges₌
      (evaluate⁼-absolute e (α ▷ r))
      (preWhisker (productMap r (id C)) ◁ evaluate⁼-absolute e α)
      (unconst-sides₌ (evaluate-restrict-inputs e α r))


module RepresentedPrecomposition {Γ : Context} {FA FB A B E : CAT Γ}
  (eA : MAP (FA × A) E) (eB : MAP (FB × B) E)
  (f : MAP A B) (H : MAP FB FA)
  (triangle : evaluate eA H =₁ (eB ∘ product-restriction {P = FB} f)) where

  comparison : {T : CAT Γ} (k : MAP T FB)
    → evaluate eA (H ∘ k) =₁
        (evaluate eB k ∘ product-restriction {P = T} f)
  comparison {T} k =
    (comp-assoc (product-restriction {P = T} f) (productMap k (id B)) eB) ⁻¹ ∙
      ((eB ◁ productMap-separate k f) ∙
        (comp-assoc (productMap k (id A)) (product-restriction {P = FB} f) eB ∙
          ((triangle ▷ productMap k (id A)) ∙ evaluate-restrict eA H k)))

  private
    module Calculation {X Y : CAT Γ} (k : MAP Y FB) (h : MAP X Y) where
      private
        Z : CAT Γ
        Z = FB
        HA = productMap h (id A)
        HB = productMap h (id B)
        KA = productMap k (id A)
        KB = productMap k (id B)
        LX = product-restriction {P = X} f
        LY = product-restriction {P = Y} f
        LZ = product-restriction {P = Z} f
        Sh = productMap-separate h f
        Sk = productMap-separate k f
        β = triangle
        uk = evaluate-restrict eA H k
        qk = comparison k
        e : MAP (Z × B) E
        e = eB
        module P = CrossingEvaluationCalculation.EvaluatedCrossingPaste HA KA HB KB LX LY LZ
          e (evaluate eA H) (evaluate eB k) (evaluate eA (H ∘ k))
          (β ⁻¹) (id₌ (evaluate eB k)) (uk ⁻¹) Sk Sh qk
          using (action; chain; compatibility; source; target)
        out = (comp-assoc LY KB e) ⁻¹
        inn = comp-assoc KA LZ e
        βk = β ▷ KA
        prefix = inn ∙ (βk ∙ uk)
        tail = uk ⁻¹ ∙ restrict-triangle e LZ (β ⁻¹) KA
        middle = out ∙ (e ◁ Sk)
        tail-normal : tail =₂ prefix ⁻¹
        tail-normal = (inverse-three inn βk uk) ⁻¹ ∙
          comp₌-cong (id₌ (uk ⁻¹))
            (comp₌-cong (preWhisker-inverse β KA) (id₌ (inn ⁻¹)))
        normalize-left : (restrict-triangle e KB (id₌ (evaluate eB k)) LY ∙ (e ◁ Sk)) =₂ middle
        normalize-left = comp₌-cong
          (comp₌-unitˡ-One out ∙ comp₌-cong (preWhisker-id₌ (evaluate eB k) LY) (id₌ out))
          (id₌ (e ◁ Sk))
        normalize-right : (qk ∙ tail) =₂ middle
        normalize-right = comp-inv-right middle prefix ∙
          comp₌-cong ((comp₌-assoc out (e ◁ Sk) prefix) ⁻¹) tail-normal
        outer-square : SquareCell₌ (e ◁ Sk) qk
          (uk ⁻¹ ∙ restrict-triangle e LZ (β ⁻¹) KA)
          (restrict-triangle e KB (id₌ (evaluate eB k)) LY)
        outer-square = normalize-right ⁻¹ ∙ normalize-left
        module M = ParameterSeparationComposition h k f
          using (compatibility; inverse-chain)
        V = comp-assoc HA KA LZ
        U = comp-assoc HA LY KB
        T = comp-assoc LX HB KB
        post-inverse-inverse = (postWhisker KB ◁ inverse-inverse Sh) ∙
          (postWhisker-inverse KB (Sh ⁻¹)) ⁻¹
        pre-inverse-inverse = (preWhisker HA ◁ inverse-inverse Sk) ∙
          (preWhisker-inverse (Sk ⁻¹) HA) ⁻¹

      chain = P.chain
      chain-bridge : (M.inverse-chain ⁻¹) =₂ chain
      chain-bridge = comp₌-cong (id₌ (T ⁻¹))
        (comp₌-cong post-inverse-inverse
          (comp₌-cong (inverse-inverse U)
            (comp₌-cong pre-inverse-inverse (id₌ (V ⁻¹))))) ∙
        inverse-five V (Sk ⁻¹ ▷ HA) (U ⁻¹) (KB ◁ Sh ⁻¹) T

      -- The complete pasted evaluation, with the original source/target triangles.
      pasted-evaluation : SquareCell₌ (e ◁ chain) P.action P.source P.target
      pasted-evaluation = P.compatibility outer-square

      -- Complete actual first-parameter compositor/separation rectangle after
      -- evaluation, using a proved bridge to the literal crossing paste.
      mixed-evaluation : SquareCell₌
        (e ◁ (LZ ◁ productMap-first-comp {C = A} k h))
        (e ◁ (productMap-first-comp {C = B} k h ▷ LX))
        (e ◁ chain) (e ◁ productMap-separate (k ∘ h) f)
      mixed-evaluation = post-square₌ e
        (replace-sides₌ chain-bridge (id₌ (productMap-separate (k ∘ h) f)) M.compatibility)

      private
        uncurriedPre = evaluate eA H
        KHA = productMap (k ∘ h) (id A)
        KHB = productMap (k ∘ h) (id B)
        κA = productMap-first-comp {C = A} k h
        κB = productMap-first-comp {C = B} k h
        u₀ = evaluate-restrict eA (H ∘ k) h
        v₀ = evaluate-restrict eA H (k ∘ h)
        τ = evaluate-cong eA (comp-assoc h k H)
        w = evaluate-restrict eB k h
        a₁ = uk ▷ HA
        a₂ = comp-assoc HA KA uncurriedPre
        a₃ = β ▷ (KA ∘ HA)
        a₄ = comp-assoc (KA ∘ HA) LZ e
        prefix₀ = a₄ ∙ (a₃ ∙ (a₂ ∙ a₁))
        z = prefix₀ ∙ u₀
        source-normal : P.source =₂ prefix₀ ⁻¹
        source-normal = ((comp₌-assoc (a₁ ⁻¹) (a₂ ⁻¹) (a₃ ⁻¹ ∙ a₄ ⁻¹)) ⁻¹ ∙
            inverse-four a₄ a₃ a₂ a₁) ⁻¹ ∙
          comp₌-cong
            (comp₌-cong (preWhisker-inverse uk HA) (id₌ (a₂ ⁻¹)))
            (comp₌-cong (preWhisker-inverse β (KA ∘ HA)) (id₌ (a₄ ⁻¹)))
        source-endpoint : (P.source ∙ z) =₂ u₀
        source-endpoint = inv-comp-left prefix₀ u₀ ∙ comp₌-cong source-normal (id₌ z)
        input-action = e ◁ (LZ ◁ κA)
        output-action = e ◁ (κB ▷ LX)
        output-associator = (comp-assoc LX KHB e) ⁻¹
        composite-input = comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (v₀ ∙ τ))
        input-square : (comp-assoc KHA LZ e ∙ ((β ▷ KHA) ∙ (uncurriedPre ◁ κA))) =₂
          (input-action ∙ (a₄ ∙ a₃))
        input-square = comp₌-assoc input-action a₄ a₃ ∙
          (comp₌-cong (postWhisker-comp-One κA LZ e) (id₌ a₃) ∙
            ((comp₌-assoc (comp-assoc KHA LZ e) ((e ∘ LZ) ◁ κA) a₃) ⁻¹ ∙
              comp₌-cong (id₌ (comp-assoc KHA LZ e)) (interchange β κA)))
        input-endpoint : composite-input =₂ (input-action ∙ z)
        input-endpoint =
          let inn₀ = comp-assoc KHA LZ e
              β₀ = β ▷ KHA
              act = uncurriedPre ◁ κA
              tail₀ = a₂ ∙ (a₁ ∙ u₀)
              regroup = comp₌-cong (comp₌-assoc a₄ a₃ (a₂ ∙ a₁)) (id₌ u₀) ∙
                ((comp₌-assoc (a₄ ∙ a₃) (a₂ ∙ a₁) u₀) ⁻¹ ∙
                  comp₌-cong (id₌ (a₄ ∙ a₃)) ((comp₌-assoc a₂ a₁ u₀) ⁻¹))
          in comp₌-cong (id₌ input-action) regroup ∙
            (comp₌-assoc input-action (a₄ ∙ a₃) tail₀ ∙
              (comp₌-cong input-square (id₌ tail₀) ∙
                ((comp₌-assoc inn₀ (β₀ ∙ act) tail₀) ⁻¹ ∙
                  (comp₌-cong (id₌ inn₀) ((comp₌-assoc β₀ act tail₀) ⁻¹) ∙
                    comp₌-cong (id₌ inn₀) (comp₌-cong (id₌ β₀) (evaluate-restrict-assoc eA H k h))))))
        output-endpoint : ((w ▷ LX) ∙ (output-associator ∙ output-action)) =₂ P.target
        output-endpoint =
          let before = (comp-assoc HB KB e) ⁻¹
              final = (comp-assoc LX (KB ∘ HB) e) ⁻¹
              image = e ◁ κB
              cancel = inv-comp-right before image ∙
                comp₌-cong (comp₌-cong (id₌ before) (postWhisker-inverse e κB)) (id₌ image)
              restricted = (preWhisker LX ◁ cancel) ∙ (preWhisker-comp₌ w image LX) ⁻¹
              target-normal = comp₌-cong
                (preWhisker LX ◁ (comp₌-unitˡ-One before ∙
                  comp₌-cong (preWhisker-id₌ (evaluate eB k) HB) (id₌ before))) (id₌ final)
              move = solve-square (comp-assoc LX KHB e) output-action
                (image ▷ LX) (comp-assoc LX (KB ∘ HB) e) (whisker-mixed-One κB LX e)
          in target-normal ⁻¹ ∙
            (comp₌-cong restricted (id₌ final) ∙
              ((comp₌-assoc (w ▷ LX) (image ▷ LX) final) ⁻¹ ∙
                comp₌-cong (id₌ (w ▷ LX)) move))
        normalize-input : (comparison (k ∘ h) ∙ τ) =₂
          (output-associator ∙ ((e ◁ productMap-separate (k ∘ h) f) ∙ composite-input))
        normalize-input =
          let S = e ◁ productMap-separate (k ∘ h) f
              a = comp-assoc KHA LZ e
              b = β ▷ KHA
          in comp₌-cong (id₌ output-associator)
            (comp₌-cong (id₌ S)
              (comp₌-cong (id₌ a) (comp₌-assoc b v₀ τ) ∙ comp₌-assoc a (b ∙ v₀) τ) ∙
                comp₌-assoc S (a ∙ (b ∙ v₀)) τ) ∙
                  comp₌-assoc output-associator (S ∙ (a ∙ (b ∙ v₀))) τ
        move-product : ((e ◁ productMap-separate (k ∘ h) f) ∙ (input-action ∙ z)) =₂
          (output-action ∙ ((e ◁ chain) ∙ z))
        move-product = comp₌-assoc output-action (e ◁ chain) z ∙
          (comp₌-cong mixed-evaluation (id₌ z) ∙
            (comp₌-assoc (e ◁ productMap-separate (k ∘ h) f) input-action z) ⁻¹)
        close : ((w ▷ LX) ∙ (output-associator ∙ (output-action ∙ ((e ◁ chain) ∙ z)))) =₂
          (P.action ∙ u₀)
        close = comp₌-cong (id₌ P.action) source-endpoint ∙
          (comp₌-assoc P.action P.source z ∙
            (comp₌-cong pasted-evaluation (id₌ z) ∙
              ((comp₌-assoc P.target (e ◁ chain) z) ⁻¹ ∙
                (comp₌-cong output-endpoint (id₌ ((e ◁ chain) ∙ z)) ∙
                  ((comp₌-assoc (w ▷ LX) (output-associator ∙ output-action) ((e ◁ chain) ∙ z)) ⁻¹ ∙
                    comp₌-cong (id₌ (w ▷ LX))
                      ((comp₌-assoc output-associator output-action ((e ◁ chain) ∙ z)) ⁻¹))))))

      substitution-calculation : ((evaluate-restrict eB k h ▷ product-restriction {P = X} f) ∙
        (comparison (k ∘ h) ∙ evaluate-cong eA (comp-assoc h k H))) =₂
        (P.action ∙ evaluate-restrict eA (H ∘ k) h)
      substitution-calculation = close ∙
        (comp₌-cong (id₌ (w ▷ LX)) (comp₌-cong (id₌ output-associator) move-product) ∙
          (comp₌-cong (id₌ (w ▷ LX))
            (comp₌-cong (id₌ output-associator)
              (comp₌-cong (id₌ (e ◁ productMap-separate (k ∘ h) f)) input-endpoint)) ∙
                comp₌-cong (id₌ (w ▷ LX)) normalize-input))

  private
    parameter-action : {S T : CAT Γ} (k : MAP T FB) (σ : MAP S T)
      → (evaluate eA (H ∘ k) ∘ productMap σ (id A)) =₁
          ((evaluate eB k ∘ productMap σ (id B)) ∘ product-restriction {P = S} f)
    parameter-action {S} {T} k σ =
      (comp-assoc (product-restriction {P = S} f)
        (productMap σ (id B)) (evaluate eB k)) ⁻¹ ∙
        ((evaluate eB k ◁ productMap-separate σ f) ∙
          (comp-assoc (productMap σ (id A))
            (product-restriction {P = T} f) (evaluate eB k) ∙
            (comparison k ▷ productMap σ (id A))))

  substitution : {S T : CAT Γ} (k : MAP T FB) (σ : MAP S T)
    → ((evaluate-restrict eB k σ ▷ product-restriction {P = S} f) ∙
        (comparison (k ∘ σ) ∙ evaluate-cong eA (comp-assoc σ k H))) =₂
      (parameter-action k σ ∙ evaluate-restrict eA (H ∘ k) σ)
  substitution k σ = Calculation.substitution-calculation k σ

module PrecompositionCompositor {Γ : Context} {FA FB FC A B C E : CAT Γ}
  (eA : MAP (FA × A) E) (eB : MAP (FB × B) E) (eC : MAP (FC × C) E)
  (f : MAP A B) (g : MAP B C)
  (Hf : MAP FB FA) (Hg : MAP FC FB) (Hgf : MAP FC FA)
  (βf : evaluate eA Hf =₁ (eB ∘ product-restriction {P = FB} f))
  (βg : evaluate eB Hg =₁ (eC ∘ product-restriction {P = FC} g))
  (βgf : evaluate eA Hgf =₁ (eC ∘ product-restriction {P = FC} (g ∘ f)))
  (δ : (Hf ∘ Hg) =₁ Hgf) where

  private
    module F = RepresentedPrecomposition eA eB f Hf βf
      using (comparison; substitution)
    module G = RepresentedPrecomposition eB eC g Hg βg
      using (comparison)
    module GF = RepresentedPrecomposition eA eC (g ∘ f) Hgf βgf
      using (comparison)
    Jf = product-restriction {P = FC} f
    Jg = product-restriction {P = FC} g
    base-before = (βg ▷ Jf) ∙ F.comparison Hg
    base-after = βgf
    base-route = (eC ◁ restriction-compositor {P = FC} f g) ∙ comp-assoc Jf Jg eC

  module _ (base-square : SquareCell₌ (evaluate-cong eA δ) base-route base-before base-after) where
    private
      module Base where
        before = base-before
        after = base-after
        product-route = base-route
        square = base-square

      module Calculation {P : CAT Γ} (h : MAP P FC) where
        private
          Q : CAT Γ
          Q = FC
          e : MAP (Q × C) E
          e = eC
          U = evaluate eC h
          Ff = Hf
          Fg = Hg
          Uf = evaluate eB Fg
          RA = productMap h (id A)
          RB = productMap h (id B)
          RC = productMap h (id C)
          JPf = product-restriction {P = P} f
          JPg = product-restriction {P = P} g
          JQf = product-restriction {P = Q} f
          JQg = product-restriction {P = Q} g
          JQgf = product-restriction {P = Q} (g ∘ f)
          κP = restriction-compositor {P = P} f g
          κQ = restriction-compositor {P = Q} f g
          β = βg
          qg = G.comparison h
          νg = evaluate-restrict eB Fg h
          Sf = productMap-separate h f
          Sg = productMap-separate h g
          Sgf = productMap-separate h (g ∘ f)
          module Default = Base
          module Paste = CrossingEvaluationCalculation.EvaluatedCrossingPaste
            JPf JPg JQf JQg RA RB RC e U Uf (evaluate eB (Fg ∘ h))
            (id₌ U) (β ⁻¹) (qg ⁻¹) (Sg ⁻¹) (Sf ⁻¹) νg
            using (action; chain; compatibility; source; target)
          ain = comp-assoc RB JQg e
          aout = comp-assoc JPg RC e
          βpre = β ▷ RB
          qprefix = e ◁ Sg ∙ (ain ∙ (βpre ∙ νg))
          qinverse-normal : (qg ⁻¹) =₂
            ((νg ⁻¹ ∙ (βpre ⁻¹ ∙ (ain ⁻¹ ∙ (e ◁ Sg) ⁻¹))) ∙ aout)
          qinverse-normal = comp₌-cong (inverse-four (e ◁ Sg) ain βpre νg) (inverse-inverse aout) ∙
            inverse-composite (aout ⁻¹) qprefix
          source-triangle-normal : restrict-triangle e RC (id₌ U) JPg =₂ (aout ⁻¹)
          source-triangle-normal = comp₌-unitˡ-One (aout ⁻¹) ∙
            comp₌-cong (preWhisker-id₌ U JPg) (id₌ (aout ⁻¹))
          outer-right-normal : (νg ∙ ((qg ⁻¹) ∙ restrict-triangle e RC (id₌ U) JPg)) =₂
            (βpre ⁻¹ ∙ (ain ⁻¹ ∙ (e ◁ Sg) ⁻¹))
          outer-right-normal = comp-inv-left νg (βpre ⁻¹ ∙ (ain ⁻¹ ∙ (e ◁ Sg) ⁻¹)) ∙
            comp₌-cong (id₌ νg)
              (comp-inv-right (νg ⁻¹ ∙ (βpre ⁻¹ ∙ (ain ⁻¹ ∙ (e ◁ Sg) ⁻¹))) aout ∙
                comp₌-cong qinverse-normal source-triangle-normal)
          outer-left-normal : (restrict-triangle e JQg (β ⁻¹) RB ∙ (e ◁ Sg ⁻¹)) =₂
            (βpre ⁻¹ ∙ (ain ⁻¹ ∙ (e ◁ Sg) ⁻¹))
          outer-left-normal = comp₌-assoc (βpre ⁻¹) (ain ⁻¹) ((e ◁ Sg) ⁻¹) ∙
            comp₌-cong (comp₌-cong (preWhisker-inverse β RB) (id₌ (ain ⁻¹)))
              (postWhisker-inverse e Sg)
          outer-square : SquareCell₌ (e ◁ Sg ⁻¹) νg
            (qg ⁻¹ ∙ restrict-triangle e RC (id₌ U) JPg)
            (restrict-triangle e JQg (β ⁻¹) RB)
          outer-square = outer-right-normal ⁻¹ ∙ outer-left-normal
          pasted-evaluation = Paste.compatibility outer-square
          chain = Paste.chain
          T = comp-assoc RA JQf JQg
          V = comp-assoc JPf JPg RC
          W = comp-assoc JPf RB JQg
          forward-chain = V ∙ ((Sg ▷ JPf) ∙ (W ⁻¹ ∙ ((JQg ◁ Sf) ∙ T)))
          chain-normal : (forward-chain ⁻¹) =₂ chain
          chain-normal = comp₌-cong (id₌ (T ⁻¹))
            (comp₌-cong ((postWhisker-inverse JQg Sf) ⁻¹)
              (comp₌-cong (inverse-inverse W)
                (comp₌-cong ((preWhisker-inverse Sg JPf) ⁻¹) (id₌ (V ⁻¹))))) ∙
            inverse-five V (Sg ▷ JPf) (W ⁻¹) (JQg ◁ Sf) T

          r = F.comparison (Fg ∘ h) ∙ evaluate-cong eA (comp-assoc h Fg Ff)
          ν₀ = evaluate-restrict eA (Ff ∘ Fg) h
          tail₀ = (F.comparison Fg ▷ RA) ∙ ν₀
          am = comp-assoc JPf RB Uf
          bm = Uf ◁ Sf
          cm = comp-assoc RA JQf Uf
          mate = am ⁻¹ ∙ (bm ∙ cm)
          parameter-action = am ⁻¹ ∙ (bm ∙ (cm ∙ (F.comparison Fg ▷ RA)))
          parameter-action-normal : parameter-action =₂ (mate ∙ (F.comparison Fg ▷ RA))
          parameter-action-normal = (comp₌-assoc (am ⁻¹) (bm ∙ cm) (F.comparison Fg ▷ RA)) ⁻¹ ∙
            comp₌-cong (id₌ (am ⁻¹)) ((comp₌-assoc bm cm (F.comparison Fg ▷ RA)) ⁻¹)
          parameter-comparison : ((νg ▷ JPf) ∙ r) =₂ (mate ∙ tail₀)
          parameter-comparison = comp₌-assoc mate (F.comparison Fg ▷ RA) ν₀ ∙
            (comp₌-cong parameter-action-normal (id₌ ν₀) ∙ F.substitution Hg h)
          action-normal : Paste.action =₂ (mate ⁻¹ ∙ (νg ▷ JPf))
          action-normal = comp₌-cong ((inverse-three (am ⁻¹) bm cm) ⁻¹)
              (id₌ (νg ▷ JPf)) ∙
            (comp₌-cong (comp₌-cong (id₌ (cm ⁻¹)) (comp₌-cong (id₌ (bm ⁻¹)) ((inverse-inverse am) ⁻¹)))
              (id₌ (νg ▷ JPf)) ∙
              ((comp₌-assoc (cm ⁻¹) (bm ⁻¹ ∙ am) (νg ▷ JPf)) ⁻¹ ∙
                (comp₌-cong (id₌ (cm ⁻¹)) ((comp₌-assoc (bm ⁻¹) am (νg ▷ JPf)) ⁻¹) ∙
                  comp₌-cong (id₌ (cm ⁻¹))
                    (comp₌-cong (postWhisker-inverse Uf Sf) (id₌ (am ∙ (νg ▷ JPf)))))))
          core : (Paste.action ∙ r) =₂ tail₀
          core = inv-comp-left mate tail₀ ∙
            (comp₌-cong (id₌ (mate ⁻¹)) parameter-comparison ∙
              (comp₌-assoc (mate ⁻¹) (νg ▷ JPf) r ∙ comp₌-cong action-normal (id₌ r)))

          r₁ = qg ▷ JPf
          r₂ = comp-assoc JPf JPg U
          r₃ = comp-assoc (JPg ∘ JPf) RC e
          prefix₀ = r₃ ∙ (r₂ ∙ r₁)
          z = prefix₀ ∙ r
          source-normal : Paste.source =₂ prefix₀ ⁻¹
          source-normal = ((comp₌-assoc (r₁ ⁻¹) (r₂ ⁻¹) (r₃ ⁻¹)) ⁻¹ ∙
              inverse-three r₃ r₂ r₁) ⁻¹ ∙
            comp₌-cong (comp₌-cong (preWhisker-inverse qg JPf) (id₌ (r₂ ⁻¹)))
              (comp₌-unitˡ-One (r₃ ⁻¹) ∙
                comp₌-cong (preWhisker-id₌ U (JPg ∘ JPf)) (id₌ (r₃ ⁻¹)))
          source-endpoint : (Paste.source ∙ z) =₂ r
          source-endpoint = inv-comp-left prefix₀ r ∙ comp₌-cong source-normal (id₌ z)
          aQ = comp-assoc JQf JQg e
          βQ = β ▷ JQf
          pair-prefix = aQ ∙ βQ
          leading-prefix = (e ◁ κQ) ∙ pair-prefix
          leading = leading-prefix ∙ F.comparison Fg
          base-target-inverse = restrict-triangle e JQg (β ⁻¹) JQf
          base-target-normal : base-target-inverse =₂ pair-prefix ⁻¹
          base-target-normal = (inverse-composite aQ βQ) ⁻¹ ∙
            comp₌-cong (preWhisker-inverse β JQf) (id₌ (aQ ⁻¹))
          prefix-cancel : (leading-prefix ∙ base-target-inverse) =₂ (e ◁ κQ)
          prefix-cancel = comp-inv-right (e ◁ κQ) pair-prefix ∙
            comp₌-cong (id₌ leading-prefix) base-target-normal
          ain-gf = comp-assoc RA JQgf e
          projected-prefix = ain-gf ⁻¹ ∙ (e ◁ (κQ ▷ RA))
          prefix-endpoint : projected-prefix =₂ ((leading-prefix ▷ RA) ∙ Paste.target)
          prefix-endpoint =
            let final = (comp-assoc RA (JQg ∘ JQf) e) ⁻¹
                normalized = comp₌-cong
                  ((preWhisker RA ◁ prefix-cancel) ∙
                    (preWhisker-comp₌ leading-prefix base-target-inverse RA) ⁻¹) (id₌ final) ∙
                      (comp₌-assoc (leading-prefix ▷ RA) (base-target-inverse ▷ RA) final) ⁻¹
            in normalized ⁻¹ ∙ solve-square ain-gf (e ◁ (κQ ▷ RA))
              ((e ◁ κQ) ▷ RA) (comp-assoc RA (JQg ∘ JQf) e) (whisker-mixed-One κQ RA e)
          leading-transfer : ((projected-prefix ∙ (e ◁ chain)) ∙ z) =₂
            ((leading ▷ RA) ∙ ν₀)
          leading-transfer = comp₌-cong ((preWhisker-comp₌ leading-prefix (F.comparison Fg) RA) ⁻¹)
              (id₌ ν₀) ∙
            ((comp₌-assoc (leading-prefix ▷ RA) (F.comparison Fg ▷ RA) ν₀) ⁻¹ ∙
              (comp₌-cong (id₌ (leading-prefix ▷ RA)) core ∙
                (comp₌-cong (id₌ (leading-prefix ▷ RA))
                  (comp₌-cong (id₌ Paste.action) source-endpoint) ∙
                  (comp₌-cong (id₌ (leading-prefix ▷ RA))
                    (comp₌-assoc Paste.action Paste.source z ∙
                      (comp₌-cong pasted-evaluation (id₌ z) ∙
                        (comp₌-assoc Paste.target (e ◁ chain) z) ⁻¹)) ∙
                    (comp₌-assoc (leading-prefix ▷ RA) Paste.target ((e ◁ chain) ∙ z) ∙
                      (comp₌-cong prefix-endpoint (id₌ ((e ◁ chain) ∙ z)) ∙
                        comp₌-assoc projected-prefix (e ◁ chain) z))))))

          raw = evaluate-cong eA (δ ▷ h)
          ν-before = evaluate-restrict eA (Ff ∘ Fg) h
          ν-after = evaluate-restrict eA Hgf h
          lifted-before = (Default.before ▷ RA) ∙ ν-before
          lifted-after = (Default.after ▷ RA) ∙ ν-after
          lifted-square : SquareCell₌ raw (Default.product-route ▷ RA) lifted-before lifted-after
          lifted-square = paste-square₌
            (scalar-restrict-inputs eA δ h)
            (pre-square₌ RA Default.square)
          out-gf = (comp-assoc (product-restriction {P = P} (g ∘ f)) RC e) ⁻¹
          sep-gf = e ◁ Sgf
          image-prefix = out-gf ∙ (sep-gf ∙ ain-gf)
          after-normal : (image-prefix ∙ lifted-after) =₂ GF.comparison h
          after-normal = comp₌-cong (id₌ out-gf) (comp₌-assoc sep-gf ain-gf lifted-after) ∙
            comp₌-assoc out-gf (sep-gf ∙ ain-gf) lifted-after
          lifted-image : (GF.comparison h ∙ raw) =₂
            (image-prefix ∙ ((Default.product-route ▷ RA) ∙ lifted-before))
          lifted-image = comp₌-cong (id₌ image-prefix) lifted-square ∙
            (comp₌-assoc image-prefix lifted-after raw ∙ comp₌-cong (after-normal ⁻¹) (id₌ raw))
          leading-normal : (Default.product-route ∙ Default.before) =₂ leading
          leading-normal = (comp₌-assoc (e ◁ κQ) pair-prefix (F.comparison Fg)) ⁻¹ ∙
            (comp₌-cong (id₌ (e ◁ κQ)) ((comp₌-assoc aQ βQ (F.comparison Fg)) ⁻¹) ∙
              comp₌-assoc (e ◁ κQ) aQ (βQ ∙ F.comparison Fg))
          leading-restrict : ((Default.product-route ▷ RA) ∙ lifted-before) =₂ ((leading ▷ RA) ∙ ν₀)
          leading-restrict = comp₌-cong (preWhisker RA ◁ leading-normal) (id₌ ν₀) ∙
            (comp₌-cong ((preWhisker-comp₌ Default.product-route Default.before RA) ⁻¹) (id₌ ν₀) ∙
              (comp₌-assoc (Default.product-route ▷ RA) (Default.before ▷ RA) ν₀) ⁻¹)
          product-image : (sep-gf ∙ ((e ◁ (κQ ▷ RA)) ∙ (e ◁ chain))) =₂ (e ◁ (RC ◁ κP))
          product-image =
            let Dimage = e ◁ forward-chain
                Cinverse = postWhisker-inverse e forward-chain ∙
                  (postWhisker e ◁ chain-normal ⁻¹)
                whole = post-square₌ e (parameter-separation-composition h f g)
                cancel = comp-inv-right (e ◁ (RC ◁ κP)) Dimage ∙
                  comp₌-cong (id₌ ((e ◁ (RC ◁ κP)) ∙ Dimage)) Cinverse
            in cancel ∙
              (comp₌-cong whole (id₌ (e ◁ chain)) ∙
                (comp₌-assoc sep-gf (e ◁ (κQ ▷ RA)) (e ◁ chain)) ⁻¹)
          remove-prefix : (image-prefix ∙ (projected-prefix ∙ (e ◁ chain))) =₂
            (out-gf ∙ (e ◁ (RC ◁ κP)))
          remove-prefix = comp₌-cong (id₌ out-gf) product-image ∙
            (comp₌-cong (id₌ out-gf)
              (comp₌-cong (id₌ sep-gf) (comp-inv-left ain-gf ((e ◁ (κQ ▷ RA)) ∙ (e ◁ chain))) ∙
                comp₌-assoc sep-gf ain-gf (ain-gf ⁻¹ ∙ ((e ◁ (κQ ▷ RA)) ∙ (e ◁ chain)))) ∙
              (comp₌-cong (id₌ out-gf)
                (comp₌-cong (id₌ (sep-gf ∙ ain-gf)) (comp₌-assoc (ain-gf ⁻¹) (e ◁ (κQ ▷ RA)) (e ◁ chain))) ∙
                  comp₌-assoc out-gf (sep-gf ∙ ain-gf) (projected-prefix ∙ (e ◁ chain))))
          outer-move : (out-gf ∙ (e ◁ (RC ◁ κP))) =₂ ((U ◁ κP) ∙ (r₃ ⁻¹))
          outer-move = solve-square (comp-assoc (product-restriction {P = P} (g ∘ f)) RC e)
            (e ◁ (RC ◁ κP)) (U ◁ κP) r₃ (postWhisker-comp-One κP RC e)
          finish : ((out-gf ∙ (e ◁ (RC ◁ κP))) ∙ z) =₂
            (((U ◁ κP) ∙ r₂) ∙ (r₁ ∙ r))
          finish = (comp₌-assoc (U ◁ κP) r₂ (r₁ ∙ r)) ⁻¹ ∙
            (comp₌-cong (id₌ (U ◁ κP)) (comp₌-assoc r₂ r₁ r) ∙
              (comp₌-cong (id₌ (U ◁ κP))
                (inv-comp-left r₃ ((r₂ ∙ r₁) ∙ r) ∙
                  comp₌-cong (id₌ (r₃ ⁻¹)) (comp₌-assoc r₃ (r₂ ∙ r₁) r)) ∙
                    (comp₌-assoc (U ◁ κP) (r₃ ⁻¹) z ∙ comp₌-cong outer-move (id₌ z))))

        before : evaluate eA ((Ff ∘ Fg) ∘ h) =₁ ((evaluate eC h ∘ JPg) ∘ JPf)
        before = (G.comparison h ▷ JPf) ∙
          (F.comparison (Fg ∘ h) ∙ evaluate-cong eA (comp-assoc h Fg Ff))
        after : evaluate eA (Hgf ∘ h) =₁ (evaluate eC h ∘ product-restriction (g ∘ f))
        after = GF.comparison h
        product-route = (evaluate eC h ◁ κP) ∙ comp-assoc JPf JPg (evaluate eC h)
        comparison-calculation : SquareCell₌ (evaluate-cong eA (δ ▷ h)) product-route before after
        comparison-calculation = finish ∙
          (comp₌-cong remove-prefix (id₌ z) ∙
            ((comp₌-assoc image-prefix (projected-prefix ∙ (e ◁ chain)) z) ⁻¹ ∙
              (comp₌-cong (id₌ image-prefix) (leading-transfer ⁻¹) ∙
                (comp₌-cong (id₌ image-prefix) leading-restrict ∙ lifted-image))))

    comparison : {P : CAT Γ} (h : MAP P FC)
      → SquareCell₌ (evaluate-cong eA (δ ▷ h))
          ((evaluate eC h ◁ restriction-compositor {P = P} f g) ∙
            comp-assoc (product-restriction {P = P} f)
              (product-restriction {P = P} g) (evaluate eC h))
          ((G.comparison h ▷ product-restriction {P = P} f) ∙
            (F.comparison (Hg ∘ h) ∙ evaluate-cong eA (comp-assoc h Hg Hf)))
          (GF.comparison h)
    comparison h = Calculation.comparison-calculation h
```
