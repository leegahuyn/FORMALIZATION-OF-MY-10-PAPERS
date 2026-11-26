import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField

/-! Rational scheme morphisms over a field are determined by their
image point. A rational singleton boundary adds exactly one point. -/

namespace ManuscriptAudit.SchemeRationalPointsOpen

open AlgebraicGeometry CategoryTheory
open IsLocalRing (closedPoint)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {K : Type u} [Field K] {X U : Scheme.{u}}
variable (s : X ⟶ Spec (CommRingCat.of K))

/-- Rational points as actual scheme morphisms over the coefficient field. -/
abbrev PointsOver :=
  {p : Spec (CommRingCat.of K) ⟶ X // p ≫ s = 𝟙 _}

private theorem factors_through_residue (f : Spec (CommRingCat.of K) ⟶ X) :
    ∃ a : X.residueField (f (closedPoint K)) ⟶ CommRingCat.of K,
      Spec.map a ≫ X.fromSpecResidueField (f (closedPoint K)) = f :=
  ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f⟩

/-- A rational morphism is uniquely determined by its image point. -/
theorem imagePoint_injective :
    Function.Injective (fun p : PointsOver s => p.val (closedPoint K)) := by
  intro p q hpq
  let x := p.val (closedPoint K)
  obtain ⟨a, ha⟩ := factors_through_residue p.val
  obtain ⟨b, hb⟩ : ∃ b : X.residueField x ⟶ CommRingCat.of K,
      Spec.map b ≫ X.fromSpecResidueField x = q.val := by
    dsimp [x]
    rw [hpq]
    exact factors_through_residue q.val
  let r := X.fromSpecResidueField x
  let t : CommRingCat.of K ⟶ X.residueField x := (Scheme.Spec.preimage (r ≫ s)).unop
  have ht : Spec.map t = r ≫ s := Scheme.Spec.map_preimage (r ≫ s)
  have hs (c : X.residueField x ⟶ CommRingCat.of K)
      (f : PointsOver s) (hc : Spec.map c ≫ r = f.val) : t ≫ c = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ht, ← Category.assoc, hc, f.property, Spec.map_id]
  have hap : t ≫ a = 𝟙 _ := hs a p ha
  have hbq : t ≫ b = 𝟙 _ := hs b q hb
  have hsurj : Function.Surjective t := by
    intro z
    refine ⟨a z, a.hom.injective ?_⟩
    exact ConcreteCategory.congr_hom hap (a z)
  apply Subtype.ext
  rw [← ha, ← hb]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨v, rfl⟩ := hsurj z
  exact (ConcreteCategory.congr_hom hap v).trans (ConcreteCategory.congr_hom hbq v).symm

variable (j : U ⟶ X) [IsOpenImmersion j]

private def includeOpen (p : PointsOver (j ≫ s)) : PointsOver s :=
  ⟨p.val ≫ j, (Category.assoc _ _ _).trans p.property⟩

/-- If the actual scheme complement consists of one rational point,
the ambient rational scheme morphisms are those of the open and that point. -/
def optionEquiv (p₀ : PointsOver s)
    (hOutside : p₀.val (closedPoint K) ∉ Set.range j)
    (hBoundary : ∀ x : X, x ∉ Set.range j → x = p₀.val (closedPoint K)) :
    Option (PointsOver (j ≫ s)) ≃ PointsOver s := by
  classical
  let f : Option (PointsOver (j ≫ s)) → PointsOver s :=
    fun p => p.elim p₀ (includeOpen s j)
  have hsome (p : PointsOver (j ≫ s)) :
      (f (some p)).val (closedPoint K) ∈ Set.range j :=
    ⟨p.val (closedPoint K), rfl⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some p => exact (hOutside (by simpa only [← h] using hsome p)).elim
    | some p =>
      cases b with
      | none => exact (hOutside (by simpa only [h] using hsome p)).elim
      | some q =>
        apply congrArg some
        apply Subtype.ext
        exact (cancel_mono j).mp (congrArg Subtype.val h)
  · intro p
    by_cases hx : p.val (closedPoint K) ∈ Set.range j
    · have hint : Set.range p.val ⊆ Set.range j := by
        rintro _ ⟨a, rfl⟩
        rw [show a = closedPoint K from Subsingleton.elim _ _]
        exact hx
      let q := IsOpenImmersion.lift j p.val hint
      have hq : q ≫ j = p.val := IsOpenImmersion.lift_fac _ _ _
      refine ⟨some ⟨q, ?_⟩, Subtype.ext hq⟩
      rw [← Category.assoc, hq, p.property]
    · exact ⟨none, imagePoint_injective s (hBoundary _ hx).symm⟩

end
end ManuscriptAudit.SchemeRationalPointsOpen

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SchemeRationalPointsOpen.imagePoint_injective,
      ``ManuscriptAudit.SchemeRationalPointsOpen.optionEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
