# Restriction of products and its parameter changes

The fixed first coordinate retains the chosen product compositor and unit
normalization. Actual square and parameter changes keep their full routes.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction where

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
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence using (productMap-separate; productMap-first-comp; productMap-comp-natural-outer-One; productMap-comp-natural-inner-One; productMap-comp-associativity)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing using (pair₌-unique)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
  using (changeEndpoints; square-to-changeEndpoints; transport-square; reflect-transported-square; changeEndpoints-extend-square)

open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence using (post-triangle-change)

module _ {Γ : Context} where
  product-restriction : {P A B : CAT Γ} → MAP A B → MAP (P × A) (P × B)
  product-restriction {P} f = productMap (id P) f

  restriction-compositor : {P A B C : CAT Γ} (f : MAP A B) (g : MAP B C) →
    (product-restriction {P = P} g ∘ product-restriction f) =₁ product-restriction (g ∘ f)
  restriction-compositor {P} f g =
    productMap-cong (comp-unitˡ (id P)) (id₌ (g ∘ f)) ∙
      productMap-comp (id P) (id P) f g

  -- Image of an actual supplied square on the fixed-first product span.
  -- Its cell uses the two actual selected compositors, not an assumed action.
  product-square : {P A B C D : CAT Γ} {l : MAP A C} {r : MAP B D} →
    Square l r → Square (product-restriction {P = P} l) (product-restriction r)
  product-square {P} {l = l} {r} s = record
    { source-map = product-restriction (Square.source-map s)
    ; target-map = product-restriction (Square.target-map s)
    ; cell = (restriction-compositor l (Square.target-map s)) ⁻¹ ∙
        (productMap-cong (id₌ (id P)) (Square.cell s) ∙
          restriction-compositor (Square.source-map s) r) }
```
## Associativity of the selected product restriction

The actual compositor is computed on both projections. The fixed coordinate
uses the supplied unit comparison; the varying coordinate uses the ambient
pentagon in the framed postcomposition calculation. Pairing reflection
assembles the two computations. No coherence of an external action is
assumed.

```agda
private
  module ProductRestrictionCalculation where
    module _ {Γ : Context} where
      module FixedFirst (P : CAT Γ) where
        J : {A B : CAT Γ} → MAP A B → MAP (P × A) (P × B)
        J f = product-restriction {P = P} f

        chosen-compositor : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) → (J g ∘ J f) =₁ J (g ∘ f)
        chosen-compositor f g = restriction-compositor {P = P} f g

        q : {A : CAT Γ} → MAP (P × A) P
        q = id P ∘ pr₁

        b₁ : {A B : CAT Γ} (f : MAP A B) → (pr₁ ∘ J f) =₁ q
        b₁ f = pair-β₁ (id P ∘ pr₁) (f ∘ pr₂)

        b₂ : {A B : CAT Γ} (f : MAP A B) → (pr₂ ∘ J f) =₁ (f ∘ pr₂)
        b₂ f = pair-β₂ (id P ∘ pr₁) (f ∘ pr₂)

        N : {A B : CAT Γ} (f : MAP A B) → (q ∘ J f) =₁ q
        N f = b₁ f ∙ (comp-unitˡ pr₁ ▷ J f)

        D : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C)
          → ((g ∘ pr₂) ∘ J f) =₁ ((g ∘ f) ∘ pr₂)
        D f g = post-square-cell g pr₂ f pr₂ (J f) (b₂ f)

        module Images {A B C : CAT Γ} (f : MAP A B) (g : MAP B C) where
          first = post-square-cell (id P) pr₁ (id P) pr₁ (J f) (b₁ f)
          second = D f g

          first-image : SquareCell₌ (pr₁ ◁ chosen-compositor f g) (N f)
            (restrict-triangle pr₁ (J g) (b₁ g) (J f)) (b₁ (g ∘ f))
          first-image = replace-edges₌ (id₌ _)
            (post-square-cell-id pr₁ (id P) pr₁ (J f) (b₁ f))
            (lies-over-comp pr₁
              (pair-evaluation-over₁-One (id P ∘ pr₁) (g ∘ pr₂) (J f) first second)
              (unconst-sides₌
                (productMap-cong-triangle₁ (comp-unitˡ (id P)) (id₌ (g ∘ f)))))

          second-image : SquareCell₌ (pr₂ ◁ chosen-compositor f g) (D f g)
            (restrict-triangle pr₂ (J g) (b₂ g) (J f)) (b₂ (g ∘ f))
          second-image = replace-edges₌ (id₌ _)
            (comp₌-unitˡ-One second ∙
              comp₌-cong (preWhisker-id₌ (g ∘ f) pr₂) (id₌ second))
            (lies-over-comp pr₂
              (pair-evaluation-over₂-One (id P ∘ pr₁) (g ∘ pr₂) (J f) first second)
              (unconst-sides₌
                (productMap-cong-triangle₂ (comp-unitˡ (id P)) (id₌ (g ∘ f)))))

        module Associativity {A B C E : CAT Γ}
          (f : MAP A B) (g : MAP B C) (h : MAP C E) where
          Jf = J f
          Jg = J g
          Jh = J h
          Jgf = J (g ∘ f)
          κfg = chosen-compositor f g

          L : ((Jh ∘ Jg) ∘ Jf) =₁ J (h ∘ (g ∘ f))
          L = chosen-compositor (g ∘ f) h ∙ ((Jh ◁ κfg) ∙ comp-assoc Jf Jg Jh)

          R : ((Jh ∘ Jg) ∘ Jf) =₁ J (h ∘ (g ∘ f))
          R = productMap-cong (id₌ (id P)) (comp-assoc f g h) ∙
            (chosen-compositor f (h ∘ g) ∙ (chosen-compositor g h ▷ Jf))

          fixed-coordinate :
            (N (g ∘ f) ∙ ((q ◁ κfg) ∙ comp-assoc Jf Jg q)) =₂
            ((id₌ (id P) ▷ pr₁) ∙ (N f ∙ (N g ▷ Jf)))
          fixed-coordinate =
            let v = comp-unitˡ pr₁
                bst = b₁ (g ∘ f)
                b = b₁ g
                Aq = comp-assoc Jf Jg q
                Aπ = comp-assoc Jf Jg pr₁
                vv = (v ▷ Jg) ▷ Jf
                sourceFrame = v ▷ (Jg ∘ Jf)
                leftStart =
                  (comp₌-assoc bst (pr₁ ◁ κfg) (sourceFrame ∙ Aq)) ⁻¹ ∙
                  (comp₌-cong (id₌ bst)
                    (comp₌-assoc (pr₁ ◁ κfg) sourceFrame Aq ∙
                      (comp₌-cong (interchange v κfg) (id₌ Aq) ∙
                        (comp₌-assoc (v ▷ Jgf) (q ◁ κfg) Aq) ⁻¹)) ∙
                    comp₌-assoc bst (v ▷ Jgf) ((q ◁ κfg) ∙ Aq))
                middle = comp₌-cong (Images.first-image f g)
                  ((preWhisker-comp-One v Jg Jf) ⁻¹)
                cancellation = comp₌-cong (id₌ (N f))
                  (comp₌-cong (id₌ (b ▷ Jf)) (inv-comp-left Aπ vv) ∙
                    comp₌-assoc (b ▷ Jf) (Aπ ⁻¹) (Aπ ∙ vv)) ∙
                  comp₌-assoc (N f) ((b ▷ Jf) ∙ Aπ ⁻¹) (Aπ ∙ vv)
                finish = comp₌-cong (id₌ (N f))
                  ((preWhisker-comp₌ b (v ▷ Jg) Jf) ⁻¹)
                insertIdentity =
                  (comp₌-unitˡ-One (N f ∙ (N g ▷ Jf)) ∙
                    comp₌-cong (preWhisker-id₌ (id P) pr₁) (id₌ (N f ∙ (N g ▷ Jf)))) ⁻¹
            in insertIdentity ∙ (finish ∙ (cancellation ∙ (middle ∙ leftStart)))

          -- The previously unprovided varying-coordinate equation, now explicit.
          varying-coordinate :
            (D (g ∘ f) h ∙ (((h ∘ pr₂) ◁ κfg) ∙ comp-assoc Jf Jg (h ∘ pr₂))) =₂
            ((comp-assoc f g h ▷ pr₂) ∙ (D f (h ∘ g) ∙ (D g h ▷ Jf)))
          varying-coordinate =
            let outside = (comp-assoc pr₂ (g ∘ f) h) ⁻¹
                leftImage = h ◁ b₂ (g ∘ f)
                inputA = comp-assoc Jgf pr₂ h
                change = (h ∘ pr₂) ◁ κfg
                sourceA = comp-assoc Jf Jg (h ∘ pr₂)
                normalizeShort = comp₌-cong (id₌ outside)
                  (post-triangle-change h pr₂ Jg Jf Jgf κfg
                    (b₂ g) (b₂ (g ∘ f)) (D f g) (Images.second-image f g)) ∙
                  comp₌-assoc outside (leftImage ∙ inputA) (change ∙ sourceA)
                η = comp-assoc f g h ▷ pr₂
                sourceCorner = comp-assoc pr₂ g h
                imageBefore = (h ◁ b₂ g) ∙ comp-assoc Jg pr₂ h
                nextCoordinate = post-square-cell h pr₂ (g ∘ f) (g ∘ pr₂) Jf (D f g)
                -- SquareCell gives nextCoordinate∙corner = η∙D; use its inverse.
                outerSquare = (post-square-cell-comp pr₂ f pr₂ Jf (b₂ f) g h) ⁻¹
                simplifyCorner = (preWhisker Jf ◁ comp-inv-left sourceCorner imageBefore) ∙
                  (preWhisker-comp₌ sourceCorner (D g h) Jf) ⁻¹
                normalizeLong = comp₌-cong (id₌ outside)
                  (comp₌-assoc (h ◁ D f g) (comp-assoc Jf (g ∘ pr₂) h) (imageBefore ▷ Jf)) ∙
                  (comp₌-assoc outside
                    ((h ◁ D f g) ∙ comp-assoc Jf (g ∘ pr₂) h) (imageBefore ▷ Jf) ∙
                  (comp₌-cong (id₌ nextCoordinate) simplifyCorner ∙
                  (comp₌-assoc nextCoordinate (sourceCorner ▷ Jf) (D g h ▷ Jf) ∙
                  (comp₌-cong outerSquare (id₌ (D g h ▷ Jf)) ∙
                    (comp₌-assoc η (D f (h ∘ g)) (D g h ▷ Jf)) ⁻¹))))
            in normalizeLong ⁻¹ ∙ normalizeShort

          private
            short₁ = lies-over-comp pr₁
              (lies-over-comp pr₁
                (restrict-triangle-assoc pr₁ Jh (b₁ h) Jg Jf)
                (restrict-change-square-One pr₁ Jh q (b₁ h) κfg))
              (Images.first-image (g ∘ f) h)

            short₂ = lies-over-comp pr₂
              (lies-over-comp pr₂
                (restrict-triangle-assoc pr₂ Jh (b₂ h) Jg Jf)
                (restrict-change-square-One pr₂ Jh (h ∘ pr₂) (b₂ h) κfg))
              (Images.second-image (g ∘ f) h)

            long₁ = lies-over-comp pr₁
              (lies-over-comp pr₁
                (restrict-square-One pr₁ (chosen-compositor g h) (N g)
                  (restrict-triangle pr₁ Jh (b₁ h) Jg) (b₁ (h ∘ g)) Jf (Images.first-image g h))
                (Images.first-image f (h ∘ g)))
              (unconst-sides₌ (productMap-cong-triangle₁ (id₌ (id P)) (comp-assoc f g h)))

            long₂ = lies-over-comp pr₂
              (lies-over-comp pr₂
                (restrict-square-One pr₂ (chosen-compositor g h) (D g h)
                  (restrict-triangle pr₂ Jh (b₂ h) Jg) (b₂ (h ∘ g)) Jf (Images.second-image g h))
                (Images.second-image f (h ∘ g)))
              (unconst-sides₌ (productMap-cong-triangle₂ (id₌ (id P)) (comp-assoc f g h)))

          compatibility : L =₂ R
          compatibility = pair₌-unique short₁ short₂
            (replace-edges₌ (id₌ _) (fixed-coordinate ⁻¹) long₁)
            (replace-edges₌ (id₌ _) (varying-coordinate ⁻¹) long₂)

module _ {Γ : Context} where
  restriction-associativity : {P A B C D : CAT Γ}
    (f : MAP A B) (g : MAP B C) (h : MAP C D) →
    (restriction-compositor {P = P} (g ∘ f) h ∙
      ((product-restriction h ◁ restriction-compositor f g) ∙
        comp-assoc (product-restriction f) (product-restriction g) (product-restriction h))) =₂
    (productMap-cong (id₌ (id P)) (comp-assoc f g h) ∙
      (restriction-compositor f (h ∘ g) ∙
        (restriction-compositor g h ▷ product-restriction f)))
  restriction-associativity {P = P} f g h = Proof.compatibility
    where
    module Proof = ProductRestrictionCalculation.FixedFirst.Associativity P f g h
```


## The actual parameter separation on both projections

Precomposition evaluation uses the specified separation between a parameter
change and a change of the second input. Both normalized composite routes
are computed on the projections. Their common endpoint supplies the two
projection squares of the actual separation, rather than a replacement
witness. These are the inputs for its mixed composition compatibility.

```agda
module _ {Γ : Context} where
  module ParameterSeparation {P Q A B : CAT Γ} (h : MAP P Q) (f : MAP A B) where
    RA : MAP (P × A) (Q × A)
    RA = productMap h (id A)
    RB : MAP (P × B) (Q × B)
    RB = productMap h (id B)
    JP : MAP (P × A) (P × B)
    JP = product-restriction f
    JQ : MAP (Q × A) (Q × B)
    JQ = product-restriction f

    separate : (JQ ∘ RA) =₁ (RB ∘ JP)
    separate = productMap-separate h f

    private
      front₁ = post-square-cell (id Q) pr₁ h pr₁ RA (pair-β₁ (h ∘ pr₁) (id A ∘ pr₂))
      front₂ = post-square-cell f pr₂ (id A) pr₂ RA (pair-β₂ (h ∘ pr₁) (id A ∘ pr₂))
      back₁ = post-square-cell h pr₁ (id P) pr₁ JP (pair-β₁ (id P ∘ pr₁) (f ∘ pr₂))
      back₂ = post-square-cell (id B) pr₂ f pr₂ JP (pair-β₂ (id P ∘ pr₁) (f ∘ pr₂))
      front-normal = productMap-cong (comp-unitˡ h) (comp-unitʳ f)
      back-normal = productMap-cong (comp-unitʳ h) (comp-unitˡ f)
      front-comp = productMap-comp h (id Q) (id A) f
      back-comp = productMap-comp (id P) h f (id B)

    front : (JQ ∘ RA) =₁ productMap h f
    front = front-normal ∙ front-comp
    back : (RB ∘ JP) =₁ productMap h f
    back = back-normal ∙ back-comp

    first-before : (pr₁ ∘ (JQ ∘ RA)) =₁ ((id Q ∘ pr₁) ∘ RA)
    first-before = restrict-triangle pr₁ JQ (pair-β₁ (id Q ∘ pr₁) (f ∘ pr₂)) RA
    first-after : (pr₁ ∘ (RB ∘ JP)) =₁ ((h ∘ pr₁) ∘ JP)
    first-after = restrict-triangle pr₁ RB (pair-β₁ (h ∘ pr₁) (id B ∘ pr₂)) JP
    second-before : (pr₂ ∘ (JQ ∘ RA)) =₁ ((f ∘ pr₂) ∘ RA)
    second-before = restrict-triangle pr₂ JQ (pair-β₂ (id Q ∘ pr₁) (f ∘ pr₂)) RA
    second-after : (pr₂ ∘ (RB ∘ JP)) =₁ ((id B ∘ pr₂) ∘ JP)
    second-after = restrict-triangle pr₂ RB (pair-β₂ (h ∘ pr₁) (id B ∘ pr₂)) JP

    first-front : ((id Q ∘ pr₁) ∘ RA) =₁ (h ∘ pr₁)
    first-front = (comp-unitˡ h ▷ pr₁) ∙ front₁
    first-back : ((h ∘ pr₁) ∘ JP) =₁ (h ∘ pr₁)
    first-back = (comp-unitʳ h ▷ pr₁) ∙ back₁
    second-front : ((f ∘ pr₂) ∘ RA) =₁ (f ∘ pr₂)
    second-front = (comp-unitʳ f ▷ pr₂) ∙ front₂
    second-back : ((id B ∘ pr₂) ∘ JP) =₁ (f ∘ pr₂)
    second-back = (comp-unitˡ f ▷ pr₂) ∙ back₂

    private
      front-image₁ : SquareCell₌ (pr₁ ◁ front) first-front first-before (pair-β₁ (h ∘ pr₁) (f ∘ pr₂))
      front-image₁ = lies-over-comp pr₁
        (pair-evaluation-over₁-One (id Q ∘ pr₁) (f ∘ pr₂) RA front₁ front₂)
        (unconst-sides₌ (productMap-cong-triangle₁ (comp-unitˡ h) (comp-unitʳ f)))
      front-image₂ : SquareCell₌ (pr₂ ◁ front) second-front second-before (pair-β₂ (h ∘ pr₁) (f ∘ pr₂))
      front-image₂ = lies-over-comp pr₂
        (pair-evaluation-over₂-One (id Q ∘ pr₁) (f ∘ pr₂) RA front₁ front₂)
        (unconst-sides₌ (productMap-cong-triangle₂ (comp-unitˡ h) (comp-unitʳ f)))
      back-image₁ : SquareCell₌ (pr₁ ◁ back) first-back first-after (pair-β₁ (h ∘ pr₁) (f ∘ pr₂))
      back-image₁ = lies-over-comp pr₁
        (pair-evaluation-over₁-One (h ∘ pr₁) (id B ∘ pr₂) JP back₁ back₂)
        (unconst-sides₌ (productMap-cong-triangle₁ (comp-unitʳ h) (comp-unitˡ f)))
      back-image₂ : SquareCell₌ (pr₂ ◁ back) second-back second-after (pair-β₂ (h ∘ pr₁) (f ∘ pr₂))
      back-image₂ = lies-over-comp pr₂
        (pair-evaluation-over₂-One (h ∘ pr₁) (id B ∘ pr₂) JP back₁ back₂)
        (unconst-sides₌ (productMap-cong-triangle₂ (comp-unitʳ h) (comp-unitˡ f)))

    separate-normal : separate =₂ (back ⁻¹ ∙ front)
    separate-normal = comp₌-cong ((inverse-composite back-normal back-comp) ⁻¹) (id₌ front) ∙
      (comp₌-assoc (back-comp ⁻¹) (back-normal ⁻¹) front) ⁻¹

    private
      projected-normal : {T : CAT Γ} (π : MAP (Q × B) T) →
        (π ◁ separate) =₂ ((π ◁ back) ⁻¹ ∙ (π ◁ front))
      projected-normal π = comp₌-cong (postWhisker-inverse π back) (id₌ (π ◁ front)) ∙
        (postWhisker-comp₌ π (back ⁻¹) front ∙ (postWhisker π ◁ separate-normal))

    abstract
      first-image : SquareCell₌ (pr₁ ◁ separate) (first-back ⁻¹ ∙ first-front) first-before first-after
      first-image = replace-edges₌ ((projected-normal pr₁) ⁻¹) (id₌ (first-back ⁻¹ ∙ first-front))
        (inv-comp-square₌ front-image₁ back-image₁)
      second-image : SquareCell₌ (pr₂ ◁ separate) (second-back ⁻¹ ∙ second-front) second-before second-after
      second-image = replace-edges₌ ((projected-normal pr₂) ⁻¹) (id₌ (second-back ⁻¹ ∙ second-front))
        (inv-comp-square₌ front-image₂ back-image₂)
```


## The complete product-square pasting comparison

The calculation retains all five literal factors of square composition. The
product action and the selected compositor are compared on each factor,
including both compositor input squares and the derived associativity.
Pasting those squares and cancelling the shared final compositor gives the
whole matching square with the prescribed changes of the two horizontal
arrows.

```agda
private
  module ProductSquarePastingCalculation where
    module _ {Γ : Context} where
      module ProductSquarePasting (P : CAT Γ) where
        I = id P
        i = id₌ I
        λI = comp-unitˡ I
        J : {A B : CAT Γ} → MAP A B → MAP (P × A) (P × B)
        J = product-restriction {P = P}
        K : {A B C : CAT Γ} (f : MAP A B) (g : MAP B C)
          → (J g ∘ J f) =₁ J (g ∘ f)
        K = restriction-compositor {P = P}

        R : {A B : CAT Γ} {f g : MAP A B} → f =₁ g → J f =₁ J g
        R α = productMap-cong i α

        R₂ : {A B : CAT Γ} {f g : MAP A B} {α β : f =₁ g}
          → α =₂ β → R α =₂ R β
        R₂ p = productMap-cong₂ (id₌ i) p

        R-comp : {A B : CAT Γ} {f g h : MAP A B}
          (β : g =₁ h) (α : f =₁ g) → R (β ∙ α) =₂ (R β ∙ R α)
        R-comp β α = productMap-cong-comp i i β α ∙
          productMap-cong₂ ((comp₌-unitˡ-One i) ⁻¹) (id₌ (β ∙ α))

        R-id : {A B : CAT Γ} (f : MAP A B) → R (id₌ f) =₂ id₌ (J f)
        R-id f = productMap-cong-id-One I f

        R-inverse : {A B : CAT Γ} {f g : MAP A B} (α : f =₁ g)
          → R (α ⁻¹) =₂ ((R α) ⁻¹)
        R-inverse {f = f} α = cancel-right (R α)
          ((comp₌-inverseˡ-One (R α)) ⁻¹ ∙
            (R-id f ∙ (R₂ (comp₌-inverseˡ-One α) ∙ (R-comp (α ⁻¹) α) ⁻¹)))

        normalization-square : {A B : CAT Γ} {f g : MAP A B}
          (α : f =₁ g) (u : (I ∘ I) =₁ (I ∘ I))
          → u =₂ id₌ (I ∘ I)
          → SquareCell₌ (productMap-cong u α) (R α)
              (productMap-cong λI (id₌ f)) (productMap-cong λI (id₌ g))
        normalization-square α u p = productMap-cong-square
          (replace-edges₌ (p ⁻¹) (id₌ i)
            (transpose-square₌ (unconst-sides₌ (identity-square₌ λI))))
          (unconst-sides₌ (identity-square₌ α))

        outer-natural : {A B C : CAT Γ} (f : MAP A B)
          {g h : MAP B C} (α : g =₁ h)
          → SquareCell₌ (R α ▷ J f) (R (α ▷ f)) (K f g) (K f h)
        outer-natural f {g} {h} α = paste-square₌
          (productMap-comp-natural-outer-One I f i α)
          (normalization-square (α ▷ f) (i ▷ I) (preWhisker-id₌ I I))

        inner-natural : {A B C : CAT Γ} {f g : MAP A B}
          (α : f =₁ g) (h : MAP B C)
          → SquareCell₌ (J h ◁ R α) (R (h ◁ α)) (K f h) (K g h)
        inner-natural α h = paste-square₌
          (productMap-comp-natural-inner-One i α I h)
          (normalization-square (h ◁ α) (I ◁ i) (postWhisker-id₌ I I))

        triangle : {A B C D : CAT Γ} {f : MAP A B} {f′ : MAP C D}
          (s : Square f f′)
          → SquareCell₌ (Square.cell (product-square {P = P} s)) (R (Square.cell s))
              (K (Square.source-map s) f′) (K f (Square.target-map s))
        triangle {f = f} {f′ = f′} s = comp-inv-left (K f (Square.target-map s))
          (R (Square.cell s) ∙ K (Square.source-map s) f′)

        associativity : {A B C D : CAT Γ}
          (f : MAP A B) (g : MAP B C) (h : MAP C D)
          → SquareCell₌ (comp-assoc (J f) (J g) (J h)) (R (comp-assoc f g h))
              (K f (h ∘ g) ∙ (K g h ▷ J f))
              (K (g ∘ f) h ∙ (J h ◁ K f g))
        associativity f g h = restriction-associativity {P = P} f g h ∙
          comp₌-assoc (K (g ∘ f) h) (J h ◁ K f g) (comp-assoc (J f) (J g) (J h))

        inverse-assoc : {A B C D : CAT Γ}
          (f : MAP A B) (g : MAP B C) (h : MAP C D)
          → SquareCell₌ ((comp-assoc (J f) (J g) (J h)) ⁻¹)
              (R ((comp-assoc f g h) ⁻¹))
              (K (g ∘ f) h ∙ (J h ◁ K f g))
              (K f (h ∘ g) ∙ (K g h ▷ J f))
        inverse-assoc f g h = replace-edges₌ (id₌ _) ((R-inverse (comp-assoc f g h)) ⁻¹)
          (transpose-square₌ (inverse-square₌ (transpose-square₌ (associativity f g h))))

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
          α′ = Square.cell (product-square {P = P} L)
          β′ = Square.cell (product-square {P = P} Q)
          pasted = Square.cell (comp-square (product-square {P = P} Q) (product-square {P = P} L))
          mapped = Square.cell (product-square {P = P} outer)
          d₀ = (comp-assoc (J g₁) (J g₂) (J f₃)) ⁻¹
          d₁ = β′ ▷ J g₁
          d₂ = comp-assoc (J g₁) (J f₂) (J h₂)
          d₃ = J h₂ ◁ α′
          d₄ = (comp-assoc (J f₁) (J h₁) (J h₂)) ⁻¹
          a₀ = (comp-assoc g₁ g₂ f₃) ⁻¹
          a₁ = β ▷ g₁
          a₂ = comp-assoc g₁ f₂ h₂
          a₃ = h₂ ◁ α
          a₄ = (comp-assoc f₁ h₁ h₂) ⁻¹
          ρ₀ = K (g₂ ∘ g₁) f₃ ∙ (J f₃ ◁ K g₁ g₂)
          ρ₁ = K g₁ (f₃ ∘ g₂) ∙ (K g₂ f₃ ▷ J g₁)
          ρ₂ = K g₁ (h₂ ∘ f₂) ∙ (K f₂ h₂ ▷ J g₁)
          ρ₃ = K (f₂ ∘ g₁) h₂ ∙ (J h₂ ◁ K g₁ f₂)
          ρ₄ = K (h₁ ∘ f₁) h₂ ∙ (J h₂ ◁ K f₁ h₁)
          ρ₅ = K f₁ (h₂ ∘ h₁) ∙ (K h₁ h₂ ▷ J f₁)

          step₀ : SquareCell₌ d₀ (R a₀) ρ₀ ρ₁
          step₀ = inverse-assoc g₁ g₂ f₃

          step₁ : SquareCell₌ d₁ (R a₁) ρ₁ ρ₂
          step₁ = paste-square₌ (pre-square₌ (J g₁) (triangle Q)) (outer-natural g₁ β)

          step₂ : SquareCell₌ d₂ (R a₂) ρ₂ ρ₃
          step₂ = associativity g₁ f₂ h₂

          step₃ : SquareCell₌ d₃ (R a₃) ρ₃ ρ₄
          step₃ = paste-square₌ (post-square₌ (J h₂) (triangle L)) (inner-natural α h₂)

          step₄ : SquareCell₌ d₄ (R a₄) ρ₄ ρ₅
          step₄ = inverse-assoc f₁ h₁ h₂

          expand : R Ω =₂ (R a₄ ∙ (R a₃ ∙ (R a₂ ∙ (R a₁ ∙ R a₀))))
          expand = comp₌-cong (id₌ (R a₄))
            (comp₌-cong (id₌ (R a₃))
              (comp₌-cong (id₌ (R a₂)) (R-comp a₁ a₀) ∙ R-comp a₂ (a₁ ∙ a₀)) ∙
              R-comp a₃ (a₂ ∙ (a₁ ∙ a₀))) ∙ R-comp a₄ (a₃ ∙ (a₂ ∙ (a₁ ∙ a₀)))

          whole : SquareCell₌ pasted (R Ω) ρ₀ ρ₅
          whole = replace-edges₌ (id₌ pasted) (expand ⁻¹)
            (adjoin-square₌ (adjoin-square₌ (adjoin-square₌ (adjoin-square₌ step₀ step₁) step₂) step₃) step₄)

          matching : SquareCell₌ (J f₃ ◁ K g₁ g₂) (K h₁ h₂ ▷ J f₁) pasted mapped
          matching = cancel-left (K f₁ (h₂ ∘ h₁))
            (comp₌-assoc (K f₁ (h₂ ∘ h₁)) (K h₁ h₂ ▷ J f₁) pasted ∙
              ((whole ⁻¹) ∙
                (comp₌-assoc (R Ω) (K (g₂ ∘ g₁) f₃) (J f₃ ◁ K g₁ g₂) ∙
                  (comp₌-cong (triangle outer) (id₌ (J f₃ ◁ K g₁ g₂)) ∙
                    (comp₌-assoc (K f₁ (h₂ ∘ h₁)) mapped (J f₃ ◁ K g₁ g₂)) ⁻¹))))


module _ {Γ : Context} where
  product-square-pasting : {P A₁ A₂ A₃ B₁ B₂ B₃ : CAT Γ}
    {f₁ : MAP A₁ B₁} {f₂ : MAP A₂ B₂} {f₃ : MAP A₃ B₃}
    (Q : Square f₂ f₃) (L : Square f₁ f₂)
    → SquareCell₌ (product-restriction {P = P} f₃ ◁
        restriction-compositor (Square.source-map L) (Square.source-map Q))
        (restriction-compositor (Square.target-map L) (Square.target-map Q) ▷ product-restriction {P = P} f₁)
        (Square.cell (comp-square (product-square {P = P} Q) (product-square {P = P} L)))
        (Square.cell (product-square {P = P} (comp-square Q L)))
  product-square-pasting {P = P} Q L = ProductSquarePastingCalculation.ProductSquarePasting.Pasting.matching P L Q
```


## Mixed product association

The three literal mixed routes instantiate the actual raw compositor law.

```agda
module _ {Γ : Context} where
  module MixedProductAssociativity {P Q A B C : CAT Γ}
    (h : MAP P Q) (f : MAP A B) (g : MAP B C) where

    first-left : ((product-restriction {P = Q} g ∘ product-restriction f) ∘ productMap h (id A)) =₁
      productMap (id Q ∘ (id Q ∘ h)) (g ∘ (f ∘ id A))
    first-left = productMap-comp ((id Q) ∘ (h)) (id Q) ((f) ∘ (id A)) (g) ∙
      (((productMap (id Q) (g)) ◁ productMap-comp (h) (id Q) (id A) (f)) ∙ comp-assoc (productMap (h) (id A)) (productMap (id Q) (f)) (productMap (id Q) (g)))
    first-right : ((product-restriction {P = Q} g ∘ product-restriction f) ∘ productMap h (id A)) =₁
      productMap (id Q ∘ (id Q ∘ h)) (g ∘ (f ∘ id A))
    first-right = productMap-cong (comp-assoc (h) (id Q) (id Q)) (comp-assoc (id A) (f) (g)) ∙
      (productMap-comp (h) ((id Q) ∘ (id Q)) (id A) ((g) ∘ (f)) ∙
        (productMap-comp (id Q) (id Q) (f) (g) ▷ productMap (h) (id A)))
    first : first-left =₂ first-right
    first = productMap-comp-associativity (h) (id Q) (id Q) (id A) (f) (g)

    middle-left : ((product-restriction {P = Q} g ∘ productMap h (id B)) ∘ product-restriction f) =₁
      productMap (id Q ∘ (h ∘ id P)) (g ∘ (id B ∘ f))
    middle-left = productMap-comp ((h) ∘ (id P)) (id Q) ((id B) ∘ (f)) (g) ∙
      (((productMap (id Q) (g)) ◁ productMap-comp (id P) (h) (f) (id B)) ∙ comp-assoc (productMap (id P) (f)) (productMap (h) (id B)) (productMap (id Q) (g)))
    middle-right : ((product-restriction {P = Q} g ∘ productMap h (id B)) ∘ product-restriction f) =₁
      productMap (id Q ∘ (h ∘ id P)) (g ∘ (id B ∘ f))
    middle-right = productMap-cong (comp-assoc (id P) (h) (id Q)) (comp-assoc (f) (id B) (g)) ∙
      (productMap-comp (id P) ((id Q) ∘ (h)) (f) ((g) ∘ (id B)) ∙
        (productMap-comp (h) (id Q) (id B) (g) ▷ productMap (id P) (f)))
    middle : middle-left =₂ middle-right
    middle = productMap-comp-associativity (id P) (h) (id Q) (f) (id B) (g)

    last-left : ((productMap h (id C) ∘ product-restriction g) ∘ product-restriction {P = P} f) =₁
      productMap (h ∘ (id P ∘ id P)) (id C ∘ (g ∘ f))
    last-left = productMap-comp ((id P) ∘ (id P)) (h) ((g) ∘ (f)) (id C) ∙
      (((productMap (h) (id C)) ◁ productMap-comp (id P) (id P) (f) (g)) ∙ comp-assoc (productMap (id P) (f)) (productMap (id P) (g)) (productMap (h) (id C)))
    last-right : ((productMap h (id C) ∘ product-restriction g) ∘ product-restriction {P = P} f) =₁
      productMap (h ∘ (id P ∘ id P)) (id C ∘ (g ∘ f))
    last-right = productMap-cong (comp-assoc (id P) (id P) (h)) (comp-assoc (f) (g) (id C)) ∙
      (productMap-comp (id P) ((h) ∘ (id P)) (f) ((id C) ∘ (g)) ∙
        (productMap-comp (id P) (h) (g) (id C) ▷ productMap (id P) (f)))
    last : last-left =₂ last-right
    last = productMap-comp-associativity (id P) (id P) (h) (f) (g) (id C)
```


## Composition and input naturality of parameter separation

The full composition rectangle retains the selected product compositors and
the actual separation. Its proof normalizes the three raw mixed associativity
equations by the coordinate unitors. Input naturality uses the same front and
back factorization, with the literal product-action squares.

```agda
private
  module SeparationCompositionCalculation where
    module _ {Γ : Context} where
      -- Each normalization equation below is proved from literal coordinate
      -- squares and raw product compositor associativity, not assumed globally.
      module NormalizeProductAssociativity
        {X₀ X₁ X₂ X₃ A₀ A₁ A₂ A₃ : CAT Γ}
        (f : MAP X₀ X₁) (g : MAP X₁ X₂) (h : MAP X₂ X₃)
        (u : MAP A₀ A₁) (v : MAP A₁ A₂) (w : MAP A₂ A₃)
        {gf : MAP X₀ X₂} {vu : MAP A₀ A₂}
        {hg : MAP X₁ X₃} {wv : MAP A₁ A₃}
        {t : MAP X₀ X₃} {z : MAP A₀ A₃}
        (p : (g ∘ f) =₁ gf) (q : (v ∘ u) =₁ vu)
        (r : (h ∘ g) =₁ hg) (s : (w ∘ v) =₁ wv)
        (a : (h ∘ gf) =₁ t) (b : (w ∘ vu) =₁ z)
        (c : (hg ∘ f) =₁ t) (d : (wv ∘ u) =₁ z) where
        F = productMap f u
        G = productMap g v
        H = productMap h w
        μfg = productMap-comp f g u v
        μgh = productMap-comp g h v w
        μf-hg = productMap-comp f (h ∘ g) u (w ∘ v)
        μgf-h = productMap-comp (g ∘ f) h (v ∘ u) w
        μf-hg′ = productMap-comp f hg u wv
        μgf′-h = productMap-comp gf h vu w
        Np = productMap-cong p q
        Nr = productMap-cong r s
        Na = productMap-cong a b
        Nc = productMap-cong c d
        Hp = productMap-cong (h ◁ p) (w ◁ q)
        rF = productMap-cong (r ▷ f) (s ▷ u)
        inner = Np ∙ μfg
        outer = Nr ∙ μgh
        before = Na ∙ μgf′-h
        after = Nc ∙ μf-hg′
        aF = comp-assoc F G H
        rawBefore = μgf-h ∙ (H ◁ μfg)
        rawAfter = μf-hg ∙ (μgh ▷ F)
        leftCoord = productMap-cong (a ∙ (h ◁ p)) (b ∙ (w ◁ q))
        rightCoord = productMap-cong (c ∙ (r ▷ f)) (d ∙ (s ▷ u))

        fold-left : (leftCoord ∙ rawBefore) =₂ (before ∙ (H ◁ inner))
        fold-left = (comp₌-assoc Na μgf′-h (H ◁ inner)) ⁻¹ ∙
          (comp₌-cong (id₌ Na)
            (comp₌-cong (id₌ μgf′-h) ((postWhisker-comp₌ H Np μfg) ⁻¹) ∙
              (comp₌-assoc μgf′-h (H ◁ Np) (H ◁ μfg) ∙
                comp₌-cong ((productMap-comp-natural-inner-One p q h w) ⁻¹) (id₌ (H ◁ μfg)))) ∙
            (reassociateFour Na Hp μgf-h (H ◁ μfg) ∙
              comp₌-cong (productMap-cong-comp a (h ◁ p) b (w ◁ q)) (id₌ rawBefore)))

        fold-right : (rightCoord ∙ rawAfter) =₂ (after ∙ (outer ▷ F))
        fold-right = (comp₌-assoc Nc μf-hg′ (outer ▷ F)) ⁻¹ ∙
          (comp₌-cong (id₌ Nc)
            (comp₌-cong (id₌ μf-hg′) ((preWhisker-comp₌ Nr μgh F) ⁻¹) ∙
              (comp₌-assoc μf-hg′ (Nr ▷ F) (μgh ▷ F) ∙
                comp₌-cong ((productMap-comp-natural-outer-One f u r s) ⁻¹) (id₌ (μgh ▷ F)))) ∙
            (reassociateFour Nc rF μf-hg (μgh ▷ F) ∙
              comp₌-cong (productMap-cong-comp c (r ▷ f) d (s ▷ u)) (id₌ rawAfter)))

        compatibility :
          (μgf-h ∙ ((H ◁ μfg) ∙ aF)) =₂
            (productMap-cong (comp-assoc f g h) (comp-assoc u v w) ∙ rawAfter)
          → (a ∙ ((h ◁ p) ∙ comp-assoc f g h)) =₂ (c ∙ (r ▷ f))
          → (b ∙ ((w ◁ q) ∙ comp-assoc u v w)) =₂ (d ∙ (s ▷ u))
          → (before ∙ ((H ◁ inner) ∙ aF)) =₂ (after ∙ (outer ▷ F))
        compatibility raw first second =
          let firstSquare = (comp₌-unitˡ-One (c ∙ (r ▷ f))) ⁻¹ ∙
                (first ∙ comp₌-assoc a (h ◁ p) (comp-assoc f g h))
              secondSquare = (comp₌-unitˡ-One (d ∙ (s ▷ u))) ⁻¹ ∙
                (second ∙ comp₌-assoc b (w ◁ q) (comp-assoc u v w))
              coordinateSquare = replace-edges₌ (id₌ _)
                (productMap-cong-id-One t z) (productMap-cong-square firstSquare secondSquare)
              rawSquare = raw ∙ comp₌-assoc μgf-h (H ◁ μfg) aF
              wholeSquare = replace-sides₌ fold-right fold-left (paste-square₌ rawSquare coordinateSquare)
          in comp₌-unitˡ-One (after ∙ (outer ▷ F)) ∙
            (wholeSquare ∙ (comp₌-assoc before (H ◁ inner) aF) ⁻¹)

      module MixedRectangle {P Q A B C : CAT Γ}
        (h : MAP P Q) (f : MAP A B) (g : MAP B C) where
        RA = productMap h (id A)
        RB = productMap h (id B)
        RC = productMap h (id C)
        JPf = product-restriction {P = P} f
        JPg = product-restriction {P = P} g
        JQf = product-restriction {P = Q} f
        JQg = product-restriction {P = Q} g
        κP = restriction-compositor {P = P} f g
        κQ = restriction-compositor {P = Q} f g
        module Ff = ParameterSeparation h f
        module Fg = ParameterSeparation h g
        module Fgf = ParameterSeparation h (g ∘ f)
        module Raw = MixedProductAssociativity h f g
        M = productMap-cong (comp-unitˡ h) (id₌ (g ∘ f)) ∙ productMap-comp h (id Q) f g
        N = productMap-cong (comp-unitʳ h) (id₌ (g ∘ f)) ∙ productMap-comp (id P) h f g
        T = comp-assoc RA JQf JQg
        U = comp-assoc JPf RB JQg
        V = comp-assoc JPf JPg RC

        private
          module First = NormalizeProductAssociativity h (id Q) (id Q) (id A) f g
            (comp-unitˡ h) (comp-unitʳ f) (comp-unitˡ (id Q)) (id₌ (g ∘ f))
            (comp-unitˡ h) (id₌ (g ∘ f)) (comp-unitˡ h) (comp-unitʳ (g ∘ f))
          module Middle = NormalizeProductAssociativity (id P) h (id Q) f (id B) g
            (comp-unitʳ h) (comp-unitˡ f) (comp-unitˡ h) (comp-unitʳ g)
            (comp-unitˡ h) (id₌ (g ∘ f)) (comp-unitʳ h) (id₌ (g ∘ f))
          module Last = NormalizeProductAssociativity (id P) (id P) h f g (id C)
            (comp-unitˡ (id P)) (id₌ (g ∘ f)) (comp-unitʳ h) (comp-unitˡ g)
            (comp-unitʳ h) (comp-unitˡ (g ∘ f)) (comp-unitʳ h) (id₌ (g ∘ f))

          first₁ : (comp-unitˡ h ∙ ((id Q ◁ comp-unitˡ h) ∙ comp-assoc h (id Q) (id Q))) =₂
            (comp-unitˡ h ∙ (comp-unitˡ (id Q) ▷ h))
          first₁ = comp₌-cong (id₌ (comp-unitˡ h))
            ((preWhisker h ◁ identity-unitors Q) ∙ (triangle-whiskered h (id Q)) ⁻¹)

          first₂ : (id₌ (g ∘ f) ∙ ((g ◁ comp-unitʳ f) ∙ comp-assoc (id A) f g)) =₂
            (comp-unitʳ (g ∘ f) ∙ (id₌ (g ∘ f) ▷ id A))
          first₂ = comp₌-cong (id₌ (comp-unitʳ (g ∘ f))) ((preWhisker-id₌ (g ∘ f) (id A)) ⁻¹) ∙
            ((comp₌-unitʳ-One (comp-unitʳ (g ∘ f))) ⁻¹ ∙
              ((right-unitor-comp f g) ⁻¹ ∙
                comp₌-unitˡ-One ((g ◁ comp-unitʳ f) ∙ comp-assoc (id A) f g)))

          middle₁ : (comp-unitˡ h ∙ ((id Q ◁ comp-unitʳ h) ∙ comp-assoc (id P) h (id Q))) =₂
            (comp-unitʳ h ∙ (comp-unitˡ h ▷ id P))
          middle₁ = comp₌-cong (id₌ (comp-unitʳ h)) (left-unitor-comp (id P) h) ∙
            (comp₌-assoc (comp-unitʳ h) (comp-unitˡ (h ∘ id P)) (comp-assoc (id P) h (id Q)) ∙
              (comp₌-cong (postWhisker-id-One (comp-unitʳ h)) (id₌ (comp-assoc (id P) h (id Q))) ∙
                (comp₌-assoc (comp-unitˡ h) (id Q ◁ comp-unitʳ h) (comp-assoc (id P) h (id Q))) ⁻¹))

          middle₂ : (id₌ (g ∘ f) ∙ ((g ◁ comp-unitˡ f) ∙ comp-assoc f (id B) g)) =₂
            (id₌ (g ∘ f) ∙ (comp-unitʳ g ▷ f))
          middle₂ = comp₌-cong (id₌ (id₌ (g ∘ f))) ((triangle-whiskered f g) ⁻¹)

          last₁ : (comp-unitʳ h ∙ ((h ◁ comp-unitˡ (id P)) ∙ comp-assoc (id P) (id P) h)) =₂
            (comp-unitʳ h ∙ (comp-unitʳ h ▷ id P))
          last₁ = comp₌-cong (id₌ (comp-unitʳ h)) ((triangle-whiskered (id P) h) ⁻¹)

          last₂ : (comp-unitˡ (g ∘ f) ∙ ((id C ◁ id₌ (g ∘ f)) ∙ comp-assoc f g (id C))) =₂
            (id₌ (g ∘ f) ∙ (comp-unitˡ g ▷ f))
          last₂ = (comp₌-unitˡ-One (comp-unitˡ g ▷ f)) ⁻¹ ∙
            (left-unitor-comp f g ∙
              comp₌-cong (id₌ (comp-unitˡ (g ∘ f)))
                (comp₌-unitˡ-One (comp-assoc f g (id C)) ∙
                  comp₌-cong (postWhisker-id₌ (id C) (g ∘ f)) (id₌ (comp-assoc f g (id C)))))

        first-normal : (Fgf.front ∙ (κQ ▷ RA)) =₂ (M ∙ ((JQg ◁ Ff.front) ∙ T))
        first-normal = (First.compatibility Raw.first first₁ first₂) ⁻¹

        middle-normal : (M ∙ ((JQg ◁ Ff.back) ∙ U)) =₂ (N ∙ (Fg.front ▷ JPf))
        middle-normal = Middle.compatibility Raw.middle middle₁ middle₂

        last-normal : (Fgf.back ∙ ((RC ◁ κP) ∙ V)) =₂ (N ∙ (Fg.back ▷ JPf))
        last-normal = Last.compatibility Raw.last last₁ last₂

        -- The chosen separation is exactly the normalized inverse composite.
        separation-triangle : {X Y : CAT Γ} (k : MAP X Y)
          → (ParameterSeparation.back h k ∙ productMap-separate h k) =₂ ParameterSeparation.front h k
        separation-triangle {Y = Y} k =
          let front = ParameterSeparation.front h k
              back = ParameterSeparation.back h k
              bn = productMap-cong (comp-unitʳ h) (comp-unitˡ k)
              bc = productMap-comp (id P) h k (id Y)
              normal = comp₌-cong ((inverse-composite bn bc) ⁻¹) (id₌ front) ∙
                (comp₌-assoc (bc ⁻¹) (bn ⁻¹) front) ⁻¹
          in comp-inv-left back front ∙ comp₌-cong (id₌ back) normal

        left : ((JQg ∘ JQf) ∘ RA) =₁ (RC ∘ product-restriction {P = P} (g ∘ f))
        left = productMap-separate h (g ∘ f) ∙ (κQ ▷ RA)
        tail = (productMap-separate h g ▷ JPf) ∙
          (U ⁻¹ ∙ ((JQg ◁ productMap-separate h f) ∙ T))
        right : ((JQg ∘ JQf) ∘ RA) =₁ (RC ∘ product-restriction {P = P} (g ∘ f))
        right = (RC ◁ κP) ∙ (V ∙ tail)
        common = M ∙ ((JQg ◁ Ff.front) ∙ T)

        normalize-left : (Fgf.back ∙ left) =₂ common
        normalize-left = first-normal ∙
          (comp₌-cong (separation-triangle (g ∘ f)) (id₌ (κQ ▷ RA)) ∙
            (comp₌-assoc Fgf.back (productMap-separate h (g ∘ f)) (κQ ▷ RA)) ⁻¹)

        normalize-right : (Fgf.back ∙ right) =₂ common
        normalize-right =
          let Sf = productMap-separate h f
              Sg = productMap-separate h g
              rem = U ⁻¹ ∙ ((JQg ◁ Sf) ∙ T)
              bg = Fg.back ▷ JPf
              sg = Sg ▷ JPf
              split = (comp₌-assoc Fgf.back ((RC ◁ κP) ∙ V) tail) ⁻¹ ∙
                comp₌-cong (id₌ Fgf.back) ((comp₌-assoc (RC ◁ κP) V tail) ⁻¹)
              combine = comp₌-cong (id₌ N)
                (comp₌-cong ((preWhisker JPf ◁ separation-triangle g) ∙
                    (preWhisker-comp₌ Fg.back Sg JPf) ⁻¹) (id₌ rem) ∙
                  (comp₌-assoc bg sg rem) ⁻¹) ∙
                comp₌-assoc N bg (sg ∙ rem)
              transfer = comp₌-cong (middle-normal ⁻¹) (id₌ rem) ∙
                (comp₌-assoc N (Fg.front ▷ JPf) rem) ⁻¹
              reduce = comp₌-cong (id₌ M)
                (comp₌-cong (comp-inv-right (JQg ◁ Ff.back) U) (id₌ ((JQg ◁ Sf) ∙ T))) ∙
                  reassociateFour M ((JQg ◁ Ff.back) ∙ U) (U ⁻¹) ((JQg ◁ Sf) ∙ T)
              finish = comp₌-cong (id₌ M)
                (comp₌-cong ((postWhisker JQg ◁ separation-triangle f) ∙
                    (postWhisker-comp₌ JQg Ff.back Sf) ⁻¹) (id₌ T) ∙
                  (comp₌-assoc (JQg ◁ Ff.back) (JQg ◁ Sf) T) ⁻¹)
          in finish ∙ (reduce ∙ (transfer ∙ (combine ∙
            (comp₌-cong last-normal (id₌ tail) ∙ split))))

        compatibility : left =₂ right
        compatibility = cancel-left Fgf.back (normalize-right ⁻¹ ∙ normalize-left)


module _ {Γ : Context} where
  parameter-separation-composition : {P Q A B C : CAT Γ}
    (h : MAP P Q) (f : MAP A B) (g : MAP B C)
    → (productMap-separate h (g ∘ f) ∙
        (restriction-compositor {P = Q} f g ▷ productMap h (id A))) =₂
      ((productMap h (id C) ◁ restriction-compositor {P = P} f g) ∙
        (comp-assoc (product-restriction {P = P} f) (product-restriction g) (productMap h (id C)) ∙
          ((productMap-separate h g ▷ product-restriction {P = P} f) ∙
            ((comp-assoc (product-restriction {P = P} f) (productMap h (id B)) (product-restriction {P = Q} g)) ⁻¹ ∙
              ((product-restriction {P = Q} g ◁ productMap-separate h f) ∙
                comp-assoc (productMap h (id A)) (product-restriction {P = Q} f) (product-restriction g))))))
  parameter-separation-composition h f g = SeparationCompositionCalculation.MixedRectangle.compatibility h f g

module _ {Γ : Context} where
  private
    identity-frame-square : {A B : CAT Γ} {x y : MAP A B}
      (δ : x =₁ y) (ε : x =₁ x) → ε =₂ id₌ x → SquareCell₌ ε (id₌ y) δ δ
    identity-frame-square δ ε p = replace-edges₌ (p ⁻¹) (id₌ (id₌ _))
      (transpose-square₌ (unconst-sides₌ (identity-square₌ δ)))

  module SeparationSecondInput {P Q A B : CAT Γ} (h : MAP P Q)
    {f g : MAP A B} (α : f =₁ g) where
    private
      module F = ParameterSeparation h f
      module G = ParameterSeparation h g
      source-action = productMap-cong (id₌ (id Q)) α ▷ F.RA
      target-action = F.RB ◁ productMap-cong (id₌ (id P)) α
      middle = productMap-cong (id₌ h) α
      front-square : SquareCell₌ source-action middle F.front G.front
      front-square = paste-square₌
        (productMap-comp-natural-outer-One h (id A) (id₌ (id Q)) α)
        (productMap-cong-square
          (identity-frame-square (comp-unitˡ h) (id₌ (id Q) ▷ h) (preWhisker-id₌ (id Q) h))
          (unconst-sides₌ (preWhisker-id α)))
      back-square : SquareCell₌ target-action middle F.back G.back
      back-square = paste-square₌
        (productMap-comp-natural-inner-One (id₌ (id P)) α h (id B))
        (productMap-cong-square
          (identity-frame-square (comp-unitʳ h) (h ◁ id₌ (id P)) (postWhisker-id₌ h (id P)))
          (unconst-sides₌ (postWhisker-id α)))

    compatibility : SquareCell₌
      (productMap-cong (id₌ (id Q)) α ▷ F.RA)
      (F.RB ◁ productMap-cong (id₌ (id P)) α) F.separate G.separate
    compatibility = replace-sides₌ (F.separate-normal ⁻¹) (G.separate-normal ⁻¹)
      (paste-square₌ front-square (inverse-square₌ back-square))
```


## Composition in the parameter variable

The comparison uses the existing first-factor compositor. Its full crossing
chain is retained before inversion; the forward square keeps the original
separation at the composite parameter.

```agda
module _ {Γ : Context} where
  private
    module ParameterRectangle {P Q R A B : CAT Γ}
      (h : MAP P Q) (k : MAP Q R) (f : MAP A B) where
      RA = product-restriction {P = P} f
      RB = product-restriction {P = Q} f
      RC = product-restriction {P = R} f
      JPf = productMap h (id A)
      JPg = productMap k (id A)
      JQf = productMap h (id B)
      JQg = productMap k (id B)
      κP = productMap-first-comp {C = A} k h
      κQ = productMap-first-comp {C = B} k h
      module InverseSeparation {X Y : CAT Γ} (i : MAP X Y) where
        front = ParameterSeparation.back i f
        back = ParameterSeparation.front i f
      module Ff = InverseSeparation h
      module Fg = InverseSeparation k
      module Fgf = InverseSeparation (k ∘ h)
      crossing : {X Y : CAT Γ} (i : MAP X Y)
        → (productMap i (id B) ∘ product-restriction {P = X} f) =₁
          (product-restriction {P = Y} f ∘ productMap i (id A))
      crossing i = (productMap-separate i f) ⁻¹
      M = productMap-cong (id₌ (k ∘ h)) (comp-unitˡ f) ∙ productMap-comp h k f (id B)
      N = productMap-cong (id₌ (k ∘ h)) (comp-unitʳ f) ∙ productMap-comp h k (id A) f
      T = comp-assoc RA JQf JQg
      U = comp-assoc JPf RB JQg
      V = comp-assoc JPf JPg RC

      private
        module First = SeparationCompositionCalculation.NormalizeProductAssociativity (id P) h k f (id B) (id B)
          (comp-unitʳ h) (comp-unitˡ f) (id₌ (k ∘ h)) (comp-unitˡ (id B))
          (id₌ (k ∘ h)) (comp-unitˡ f) (comp-unitʳ (k ∘ h)) (comp-unitˡ f)
        module Middle = SeparationCompositionCalculation.NormalizeProductAssociativity h (id Q) k (id A) f (id B)
          (comp-unitˡ h) (comp-unitʳ f) (comp-unitʳ k) (comp-unitˡ f)
          (id₌ (k ∘ h)) (comp-unitˡ f) (id₌ (k ∘ h)) (comp-unitʳ f)
        module Last = SeparationCompositionCalculation.NormalizeProductAssociativity h k (id R) (id A) (id A) f
          (id₌ (k ∘ h)) (comp-unitˡ (id A)) (comp-unitˡ k) (comp-unitʳ f)
          (comp-unitˡ (k ∘ h)) (comp-unitʳ f) (id₌ (k ∘ h)) (comp-unitʳ f)

        first₁ : (comp-unitˡ f ∙ ((id B ◁ comp-unitˡ f) ∙ comp-assoc f (id B) (id B))) =₂
          (comp-unitˡ f ∙ (comp-unitˡ (id B) ▷ f))
        first₁ = comp₌-cong (id₌ (comp-unitˡ f))
          ((preWhisker f ◁ identity-unitors B) ∙ (triangle-whiskered f (id B)) ⁻¹)

        first₂ : (id₌ (k ∘ h) ∙ ((k ◁ comp-unitʳ h) ∙ comp-assoc (id P) h k)) =₂
          (comp-unitʳ (k ∘ h) ∙ (id₌ (k ∘ h) ▷ id P))
        first₂ = comp₌-cong (id₌ (comp-unitʳ (k ∘ h))) ((preWhisker-id₌ (k ∘ h) (id P)) ⁻¹) ∙
          ((comp₌-unitʳ-One (comp-unitʳ (k ∘ h))) ⁻¹ ∙
            ((right-unitor-comp h k) ⁻¹ ∙
              comp₌-unitˡ-One ((k ◁ comp-unitʳ h) ∙ comp-assoc (id P) h k)))

        middle₁ : (comp-unitˡ f ∙ ((id B ◁ comp-unitʳ f) ∙ comp-assoc (id A) f (id B))) =₂
          (comp-unitʳ f ∙ (comp-unitˡ f ▷ id A))
        middle₁ = comp₌-cong (id₌ (comp-unitʳ f)) (left-unitor-comp (id A) f) ∙
          (comp₌-assoc (comp-unitʳ f) (comp-unitˡ (f ∘ id A)) (comp-assoc (id A) f (id B)) ∙
            (comp₌-cong (postWhisker-id-One (comp-unitʳ f)) (id₌ (comp-assoc (id A) f (id B))) ∙
              (comp₌-assoc (comp-unitˡ f) (id B ◁ comp-unitʳ f) (comp-assoc (id A) f (id B))) ⁻¹))

        middle₂ : (id₌ (k ∘ h) ∙ ((k ◁ comp-unitˡ h) ∙ comp-assoc h (id Q) k)) =₂
          (id₌ (k ∘ h) ∙ (comp-unitʳ k ▷ h))
        middle₂ = comp₌-cong (id₌ (id₌ (k ∘ h))) ((triangle-whiskered h k) ⁻¹)

        last₁ : (comp-unitʳ f ∙ ((f ◁ comp-unitˡ (id A)) ∙ comp-assoc (id A) (id A) f)) =₂
          (comp-unitʳ f ∙ (comp-unitʳ f ▷ id A))
        last₁ = comp₌-cong (id₌ (comp-unitʳ f)) ((triangle-whiskered (id A) f) ⁻¹)

        last₂ : (comp-unitˡ (k ∘ h) ∙ ((id R ◁ id₌ (k ∘ h)) ∙ comp-assoc h k (id R))) =₂
          (id₌ (k ∘ h) ∙ (comp-unitˡ k ▷ h))
        last₂ = (comp₌-unitˡ-One (comp-unitˡ k ▷ h)) ⁻¹ ∙
          (left-unitor-comp h k ∙
            comp₌-cong (id₌ (comp-unitˡ (k ∘ h)))
              (comp₌-unitˡ-One (comp-assoc h k (id R)) ∙
                comp₌-cong (postWhisker-id₌ (id R) (k ∘ h)) (id₌ (comp-assoc h k (id R)))))

      first-normal : (Fgf.front ∙ (κQ ▷ RA)) =₂ (M ∙ ((JQg ◁ Ff.front) ∙ T))
      first-normal = (First.compatibility (productMap-comp-associativity (id P) h k f (id B) (id B)) first₂ first₁) ⁻¹

      middle-normal : (M ∙ ((JQg ◁ Ff.back) ∙ U)) =₂ (N ∙ (Fg.front ▷ JPf))
      middle-normal = Middle.compatibility (productMap-comp-associativity h (id Q) k (id A) f (id B)) middle₂ middle₁

      last-normal : (Fgf.back ∙ ((RC ◁ κP) ∙ V)) =₂ (N ∙ (Fg.back ▷ JPf))
      last-normal = Last.compatibility (productMap-comp-associativity h k (id R) (id A) (id A) f) last₂ last₁

      -- Reverse the existing separation triangle, retaining its witness.
      separation-triangle : {X Y : CAT Γ} (i : MAP X Y)
        → (InverseSeparation.back i ∙ crossing i) =₂ InverseSeparation.front i
      separation-triangle i =
        let front = ParameterSeparation.front i f
            back = ParameterSeparation.back i f
            S = productMap-separate i f
            triangle = comp-inv-left back front ∙
              comp₌-cong (id₌ back) (ParameterSeparation.separate-normal i f)
        in comp-inv-right back S ∙ comp₌-cong (triangle ⁻¹) (id₌ (S ⁻¹))

      left : ((JQg ∘ JQf) ∘ RA) =₁ (RC ∘ productMap (k ∘ h) (id A))
      left = crossing (k ∘ h) ∙ (κQ ▷ RA)
      tail = (crossing k ▷ JPf) ∙
        (U ⁻¹ ∙ ((JQg ◁ crossing h) ∙ T))
      right : ((JQg ∘ JQf) ∘ RA) =₁ (RC ∘ productMap (k ∘ h) (id A))
      right = (RC ◁ κP) ∙ (V ∙ tail)
      common = M ∙ ((JQg ◁ Ff.front) ∙ T)

      normalize-left : (Fgf.back ∙ left) =₂ common
      normalize-left = first-normal ∙
        (comp₌-cong (separation-triangle (k ∘ h)) (id₌ (κQ ▷ RA)) ∙
          (comp₌-assoc Fgf.back (crossing (k ∘ h)) (κQ ▷ RA)) ⁻¹)

      normalize-right : (Fgf.back ∙ right) =₂ common
      normalize-right =
        let Sf = crossing h
            Sg = crossing k
            rem = U ⁻¹ ∙ ((JQg ◁ Sf) ∙ T)
            bg = Fg.back ▷ JPf
            sg = Sg ▷ JPf
            split = (comp₌-assoc Fgf.back ((RC ◁ κP) ∙ V) tail) ⁻¹ ∙
              comp₌-cong (id₌ Fgf.back) ((comp₌-assoc (RC ◁ κP) V tail) ⁻¹)
            combine = comp₌-cong (id₌ N)
              (comp₌-cong ((preWhisker JPf ◁ separation-triangle k) ∙
                  (preWhisker-comp₌ Fg.back Sg JPf) ⁻¹) (id₌ rem) ∙
                (comp₌-assoc bg sg rem) ⁻¹) ∙
              comp₌-assoc N bg (sg ∙ rem)
            transfer = comp₌-cong (middle-normal ⁻¹) (id₌ rem) ∙
              (comp₌-assoc N (Fg.front ▷ JPf) rem) ⁻¹
            reduce = comp₌-cong (id₌ M)
              (comp₌-cong (comp-inv-right (JQg ◁ Ff.back) U) (id₌ ((JQg ◁ Sf) ∙ T))) ∙
                reassociateFour M ((JQg ◁ Ff.back) ∙ U) (U ⁻¹) ((JQg ◁ Sf) ∙ T)
            finish = comp₌-cong (id₌ M)
              (comp₌-cong ((postWhisker JQg ◁ separation-triangle h) ∙
                  (postWhisker-comp₌ JQg Ff.back Sf) ⁻¹) (id₌ T) ∙
                (comp₌-assoc (JQg ◁ Ff.back) (JQg ◁ Sf) T) ⁻¹)
        in finish ∙ (reduce ∙ (transfer ∙ (combine ∙
          (comp₌-cong last-normal (id₌ tail) ∙ split))))

      compatibility : left =₂ right
      compatibility = cancel-left Fgf.back (normalize-right ⁻¹ ∙ normalize-left)

  module ParameterSeparationComposition {P Q R A B : CAT Γ}
    (h : MAP P Q) (k : MAP Q R) (f : MAP A B) where
    private
      module M = ParameterRectangle h k f
    inverse-chain : ((productMap k (id B) ∘ productMap h (id B)) ∘ product-restriction {P = P} f) =₁
      (product-restriction {P = R} f ∘ (productMap k (id A) ∘ productMap h (id A)))
    inverse-chain = M.V ∙ M.tail
    -- Both sides of this square use the original forward separation.
    -- Its left side is the inverse of the displayed full crossing chain.
    compatibility : SquareCell₌
      (product-restriction {P = R} f ◁ productMap-first-comp {C = A} k h)
      (productMap-first-comp {C = B} k h ▷ product-restriction {P = P} f)
      (inverse-chain ⁻¹) (productMap-separate (k ∘ h) f)
    compatibility = replace-sides₌ (id₌ (inverse-chain ⁻¹))
      (inverse-inverse (productMap-separate (k ∘ h) f))
      (inverse-square₌ M.compatibility)
```


## The concrete restriction action laws

The proof namespace remains private; only the actual normalized laws used
by precomposition evaluation cross this module boundary.

```agda
module _ {Γ : Context} where
  restriction-action-composition : {P A B : CAT Γ} {f g h : MAP A B}
    (β : g =₁ h) (α : f =₁ g)
    → productMap-cong (id₌ (id P)) (β ∙ α) =₂
        (productMap-cong (id₌ (id P)) β ∙ productMap-cong (id₌ (id P)) α)
  restriction-action-composition {P = P} = ProductSquarePastingCalculation.ProductSquarePasting.R-comp P

  restriction-compositor-outer-natural : {P A B C : CAT Γ} (f : MAP A B)
    {g h : MAP B C} (α : g =₁ h)
    → SquareCell₌ (productMap-cong (id₌ (id P)) α ▷ product-restriction f)
        (productMap-cong (id₌ (id P)) (α ▷ f))
        (restriction-compositor f g) (restriction-compositor f h)
  restriction-compositor-outer-natural {P = P} = ProductSquarePastingCalculation.ProductSquarePasting.outer-natural P

  restriction-compositor-inner-natural : {P A B C : CAT Γ} {f g : MAP A B}
    (α : f =₁ g) (h : MAP B C)
    → SquareCell₌ (product-restriction h ◁ productMap-cong (id₌ (id P)) α)
        (productMap-cong (id₌ (id P)) (h ◁ α))
        (restriction-compositor f h) (restriction-compositor g h)
  restriction-compositor-inner-natural {P = P} = ProductSquarePastingCalculation.ProductSquarePasting.inner-natural P
```
