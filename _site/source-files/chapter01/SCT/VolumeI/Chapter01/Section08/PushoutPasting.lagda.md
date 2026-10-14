# Pasting actual pushout squares

The complete mapping-out comparison transports the actual pullback pasting
theorem while preserving both directions and the specified square cells.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section08.PushoutPasting where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; comp-assoc; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Squares using (Square; comp-square)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae using (Map)
open import SCT.VolumeI.Chapter01.Section04.Functoriality using (mapPre; mapPre⁼; mapPre-comp)
open import SCT.VolumeI.Chapter01.Section06.Cones
open import SCT.VolumeI.Chapter01.Section06.ConePasting using (module PasteCones)
open import SCT.VolumeI.Chapter01.Section06.ConeTransport using (cone-change-left; cone-change-left-matching)
open import SCT.VolumeI.Chapter01.Section06.ConeIdentifications using (cone-inverse)
open import SCT.VolumeI.Chapter01.Section06.ConeUniversality using (isPullback-cone-identification)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares using (IsPullback)
open import SCT.VolumeI.Chapter01.Section06.PullbackArrowChange using (module ChangeLeftArrow)
import SCT.VolumeI.Chapter01.Section06.PastingLemma as PullbackPasting
open import SCT.VolumeI.Chapter01.Section08.PushoutSquares using (mappingOut; IsPushout)
open import SCT.VolumeI.Chapter01.Section08.MappingOutEvaluation
```
## Complete mapped-cone pasting

The five factors of the supplied pasted square give five compatibility
squares for the actual precomposition action. Their composite compares
both specified cone matchings. Left-arrow change retains its actual
symmetry-based witness, normalized by its proved matching law. The cone
identification has the prescribed identity and compositor as its legs.

```agda
private
  module MappedConePastingCalculation where
    module _ {Γ : Context} where
      module At (E : CAT Γ) where
        private
          J : {A B : CAT Γ} → MAP A B → MAP (Map B E) (Map A E)
          J = mapPre {D = E}
          R : {A B : CAT Γ} {f g : MAP A B} → f =₁ g → J f =₁ J g
          R = mapPre⁼ {D = E}
          K : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) → (J f ∘ J g) =₁ J (g ∘ f)
          K = mapPre-comp {D = E}
          R-comp : {A B : CAT Γ} {f g h : MAP A B}
            (β : g =₁ h) (α : f =₁ g) → R (β ∙ α) =₂ (R β ∙ R α)
          R-comp = precomposition-action-composition
          R-inverse : {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g) → R (α ⁻¹) =₂ (R α) ⁻¹
          R-inverse = precomposition-action-inverse

        module _ {A B C D : CAT Γ} (f : MAP A B) (g : MAP B C) (h : MAP C D) where
          private
            am = comp-assoc (J h) (J g) (J f)
            original = comp-assoc f g h
            source-frame = K (g ∘ f) h ∙ (K f g ▷ J h)
            target-frame = K f (h ∘ g) ∙ (J f ◁ K g h)
            normal : source-frame =₂ (R original ∙ (target-frame ∙ am))
            normal = comp₌-cong (id₌ (R original))
                ((comp₌-assoc (K f (h ∘ g)) (J f ◁ K g h) am) ⁻¹) ∙
              precomposition-compositor-associativity f g h
            inverse-square : SquareCell₌ am ((R original) ⁻¹) source-frame target-frame
            inverse-square = (comp₌-cong (id₌ ((R original) ⁻¹)) normal) ⁻¹ ∙
              (inv-comp-left (R original) (target-frame ∙ am)) ⁻¹
          inverse-associativity : SquareCell₌ am (R (original ⁻¹)) source-frame target-frame
          inverse-associativity = replace-edges₌ (id₌ am) ((R-inverse original) ⁻¹) inverse-square
          associativity : SquareCell₌ (am ⁻¹) (R original) target-frame source-frame
          associativity = replace-edges₌ (id₌ (am ⁻¹)) (inverse-inverse (R original))
            (transpose-square₌ (inverse-square₌ (transpose-square₌ inverse-square)))

        module Pasting {A₁ A₂ A₃ B₁ B₂ B₃ : CAT Γ}
          {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
          (L : Square f₁ f₂) (Q : Square f₂ f₃) where
          g₁ = Square.source-map L
          g₂ = Square.source-map Q
          h₁ = Square.target-map L
          h₂ = Square.target-map Q
          α = Square.cell L
          β = Square.cell Q
          outer = comp-square Q L
          Ω = Square.cell outer
          inner-cone = mappingOut L E
          outer-cone = mappingOut Q E
          module Paste = PasteCones (J g₂) (J g₁) inner-cone
          pasted-cone = Paste.paste outer-cone
          changed = cone-change-left (K g₁ g₂) pasted-cone
          target = mappingOut outer E
          α′ = Cone.match inner-cone
          β′ = Cone.match outer-cone
          mapped = Cone.match target
          d₀ = comp-assoc (J f₃) (J g₂) (J g₁)
          d₁ = J g₁ ◁ β′
          d₂ = (comp-assoc (J h₂) (J f₂) (J g₁)) ⁻¹
          d₃ = α′ ▷ J h₂
          d₄ = comp-assoc (J h₂) (J h₁) (J f₁)
          chain = d₄ ∙ (d₃ ∙ (d₂ ∙ (d₁ ∙ d₀)))
          a₀ = (comp-assoc g₁ g₂ f₃) ⁻¹
          a₁ = β ▷ g₁
          a₂ = comp-assoc g₁ f₂ h₂
          a₃ = h₂ ◁ α
          a₄ = (comp-assoc f₁ h₁ h₂) ⁻¹
          ρ₀ = K (g₂ ∘ g₁) f₃ ∙ (K g₁ g₂ ▷ J f₃)
          ρ₁ = K g₁ (f₃ ∘ g₂) ∙ (J g₁ ◁ K g₂ f₃)
          ρ₂ = K g₁ (h₂ ∘ f₂) ∙ (J g₁ ◁ K f₂ h₂)
          ρ₃ = K (f₂ ∘ g₁) h₂ ∙ (K g₁ f₂ ▷ J h₂)
          ρ₄ = K (h₁ ∘ f₁) h₂ ∙ (K f₁ h₁ ▷ J h₂)
          ρ₅ = K f₁ (h₂ ∘ h₁) ∙ (J f₁ ◁ K h₁ h₂)
          private
            triangle : {A B C D : CAT Γ} {l : MAP A C} {r : MAP B D} (s : Square l r)
              → (K l (Square.target-map s) ∙ Cone.match (mappingOut s E)) =₂
                  (R (Square.cell s) ∙ K (Square.source-map s) r)
            triangle {l = l} s = comp-inv-left (K l (Square.target-map s))
              (R (Square.cell s) ∙ K (Square.source-map s) _)

            step₀ : SquareCell₌ d₀ (R a₀) ρ₀ ρ₁
            step₀ = inverse-associativity g₁ g₂ f₃
            step₁ : SquareCell₌ d₁ (R a₁) ρ₁ ρ₂
            step₁ = paste-square₌ (post-square₌ (J g₁) (triangle Q))
              (precomposition-compositor-outer g₁ β)
            step₂ : SquareCell₌ d₂ (R a₂) ρ₂ ρ₃
            step₂ = associativity g₁ f₂ h₂
            step₃ : SquareCell₌ d₃ (R a₃) ρ₃ ρ₄
            step₃ = paste-square₌ (pre-square₌ (J h₂) (triangle L))
              (precomposition-compositor-inner α h₂)
            step₄ : SquareCell₌ d₄ (R a₄) ρ₄ ρ₅
            step₄ = inverse-associativity f₁ h₁ h₂
            expand : R Ω =₂ (R a₄ ∙ (R a₃ ∙ (R a₂ ∙ (R a₁ ∙ R a₀))))
            expand = comp₌-cong (id₌ (R a₄))
              (comp₌-cong (id₌ (R a₃))
                (comp₌-cong (id₌ (R a₂)) (R-comp a₁ a₀) ∙ R-comp a₂ (a₁ ∙ a₀)) ∙
                R-comp a₃ (a₂ ∙ (a₁ ∙ a₀))) ∙ R-comp a₄ (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀)))
            whole : SquareCell₌ chain (R Ω) ρ₀ ρ₅
            whole = replace-edges₌ (id₌ chain) (expand ⁻¹)
              (adjoin-square₌ (adjoin-square₌ (adjoin-square₌ (adjoin-square₌ step₀ step₁) step₂) step₃) step₄)
            pasted-normal : Cone.match pasted-cone =₂ chain
            pasted-normal = comp₌-cong (id₌ d₄) (comp₌-assoc d₃ d₂ (d₁ ∙ d₀)) ∙
              comp₌-assoc d₄ (d₃ ∙ d₂) (d₁ ∙ d₀)
            matching : SquareCell₌ (K g₁ g₂ ▷ J f₃) (J f₁ ◁ K h₁ h₂) chain mapped
            matching = cancel-left (K f₁ (h₂ ∘ h₁))
              (comp₌-assoc (K f₁ (h₂ ∘ h₁)) (J f₁ ◁ K h₁ h₂) chain ∙
                (whole ⁻¹ ∙
                  (comp₌-assoc (R Ω) (K (g₂ ∘ g₁) f₃) (K g₁ g₂ ▷ J f₃) ∙
                    (comp₌-cong (triangle outer) (id₌ (K g₁ g₂ ▷ J f₃)) ∙
                      (comp₌-assoc (K f₁ (h₂ ∘ h₁)) mapped (K g₁ g₂ ▷ J f₃)) ⁻¹))))
            changed-normal : Cone.match changed =₂ (chain ∙ (K g₁ g₂ ▷ J f₃) ⁻¹)
            changed-normal = comp₌-cong pasted-normal (id₌ ((K g₁ g₂ ▷ J f₃) ⁻¹)) ∙
              cone-change-left-matching (K g₁ g₂) pasted-cone
          abstract
            compatible : SquareCell₌ (J (g₂ ∘ g₁) ◁ id₌ (J f₃)) (J f₁ ◁ K h₁ h₂)
              (Cone.match changed) (Cone.match target)
            compatible = comp₌-cong (id₌ (J f₁ ◁ K h₁ h₂)) (changed-normal ⁻¹) ∙
              (comp₌-assoc (J f₁ ◁ K h₁ h₂) chain ((K g₁ g₂ ▷ J f₃) ⁻¹) ∙
                (comp₌-cong matching (id₌ ((K g₁ g₂ ▷ J f₃) ⁻¹)) ∙
                  ((comp-inv-right mapped (K g₁ g₂ ▷ J f₃)) ⁻¹ ∙
                    (comp₌-unitʳ-One mapped ∙
                      comp₌-cong (id₌ mapped) (postWhisker-id₌ (J (g₂ ∘ g₁)) (J f₃))))))
          identification : ConeIdentification₁ changed target
          identification = record
            { left = id₌ (J f₃); right = K h₁ h₂; compatible = compatible }


module _ {Γ : Context} {A1 A2 A3 B1 B2 B3 : CAT Γ}
  {f1 : MAP A1 B1} {f2 : MAP A2 B2} {f3 : MAP A3 B3}
  (L : Square f1 f2) (R : Square f2 f3) where

  module MappedPaste (E : CAT Γ) where
    private
      g1 = Square.source-map L
      g2 = Square.source-map R
      inner = mappingOut L E
      outer = mappingOut R E
    module Paste = PasteCones (mapPre {D = E} g2) (mapPre g1) inner
    pasted = Paste.paste outer
    κsource = mapPre-comp {D = E} g1 g2
    changed = cone-change-left κsource pasted
    target = mappingOut (comp-square R L) E

    cone-comparison : ConeIdentification₁ changed target
    cone-comparison = MappedConePastingCalculation.At.Pasting.identification E L R

  module DirectPushoutPasting (left-isPushout : IsPushout L) where
    module At (E : CAT Γ) where
      private
        module M = MappedPaste E
        g1 = Square.source-map L
        g2 = Square.source-map R
        module PB = PullbackPasting.Pasting (mapPre {D = E} g2) (mapPre g1) (mapPre f1)
          (mappingOut L E) (left-isPushout E)
        module Arrow = ChangeLeftArrow M.κsource (mapPre {D = E} f1)

      preserve : IsPullback (mappingOut R E) → IsPullback (mappingOut (comp-square R L) E)
      preserve e = isPullback-cone-identification M.cone-comparison
        (Arrow.preserve-pullback M.pasted (PB.paste-isPullback (mappingOut R E) e))

      reflect : IsPullback (mappingOut (comp-square R L) E) → IsPullback (mappingOut R E)
      reflect e = PB.unpaste-isPullback (mappingOut R E)
        (Arrow.reflect-pullback M.pasted
          (isPullback-cone-identification (cone-inverse M.cone-comparison) e))

    paste-isPushout : IsPushout R → IsPushout (comp-square R L)
    paste-isPushout e E = At.preserve E (e E)
    unpaste-isPushout : IsPushout (comp-square R L) → IsPushout R
    unpaste-isPushout e E = At.reflect E (e E)

```

For each categorical target E, the complete cone identification transports
universality after pullback pasting and the chosen left-arrow change.
Applying these operations in reverse reflects universality of the outer
square. Both directions therefore hold for the actual supplied squares.
