import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportProjectiveComparison
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleExtensionHZero

/-! The actual open extension past one separably closed rational boundary point compares all positive cohomology degrees. -/

namespace ManuscriptAudit.OpenComplementRationalPointCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open OpenEtaleExtension SmallEtaleGeometricBaseChange GeometricSkyscraperCohomology

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev A := AddCommGrpCat.{u}

private theorem positiveMap_bijective {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology A.{u})) (hS : S.ShortExact)
    (h₀ : Function.Surjective (Sheaf.H.map S.g 0))
    (hHigher : ∀ n : ℕ, Subsingleton (Sheaf.H S.X₃ (n + 1))) (n : ℕ) :
    Function.Bijective (Sheaf.H.map S.f (n + 1)) := by
  let Z := (constantSheaf X.smallEtaleTopology A.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hδ (a : ℕ) (x : Sheaf.H S.X₃ a) :
      x.comp hS.extClass (show a + 1 = a + 1 from rfl) = 0 := by
    cases a with
    | zero =>
      have hExact : Function.Exact (Sheaf.H.map S.g 0)
          (hS.extClass.postcomp Z (show 0 + 1 = 1 from rfl)) :=
        (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₃' Z hS 0 1 rfl)
      exact (hExact x).mpr (h₀ x)
    | succ a =>
      have hx : x = 0 := (hHigher a).allEq _ _
      rw [hx, Ext.zero_comp]
  constructor
  · intro x y hxy
    have hz : (Sheaf.H.map S.f (n + 1)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS (x - y) hz
      (show n + 1 = n + 1 from rfl)
    exact sub_eq_zero.mp (ht.symm.trans (hδ n t))
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero (n + 1)) = 0 := (hHigher n).allEq _ _
    exact Ext.covariant_sequence_exact₂ (X := Z) hS y hy

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Cohomology of the actual extension by zero of constant coefficients. -/
abbrev extensionH (M : A.{u}) (n : ℕ) :=
  Sheaf.H ((extensionByZero j A.{u}).obj ((constantSheaf U.smallEtaleTopology A.{u}).obj M)) n

variable (K : Type u) [Field K] [IsSepClosed K]
variable (o : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion o]
variable (h : Set.range j = (Set.range o)ᶜ)

private instance closedCompId : IsClosedImmersion (o ≫ 𝟙 X) := by
  simpa only [Category.comp_id] using (inferInstanceAs (IsClosedImmersion o))

private def boundarySequence (M : A.{u}) : ShortComplex (Sheaf X.smallEtaleTopology A.{u}) :=
  nestedOpenRationalOriginSequence j (𝟙 X) M o h

private theorem boundaryCohomology (M : A.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (boundarySequence j K o h M).X₃ (n + 1)) := by
  let Φ := Scheme.pointSmallEtale (o ≫ 𝟙 X)
  let e : (boundarySequence j K o h M).X₃ ≅ Φ.skyscraperSheaf M :=
    rationalPointConstantDirectImageIso K (o ≫ 𝟙 X) M
  let d := ((Sheaf.functorH X.smallEtaleTopology (n + 1)).mapIso e).addCommGroupIsoToAddEquiv
  let hz := geometricSkyscraperH_succ_subsingleton Φ M n
  exact ⟨fun a b ↦ d.injective (hz.elim _ _)⟩

/-- Actual compact support past a single rational boundary point identifies with ordinary
ambient cohomology in every positive degree. -/
def positiveEquiv (M : A.{u}) (n : ℕ) :
    extensionH j M (n + 1) ≃+
      Sheaf.H ((constantSheaf X.smallEtaleTopology A.{u}).obj M) (n + 1) := by
  let S := boundarySequence j K o h M
  let hS : S.ShortExact := nestedOpenRationalOriginSequence_shortExact j (𝟙 X) M o h
  let H := Sheaf.functorH X.smallEtaleTopology (n + 1)
  let F := (constantSheaf U.smallEtaleTopology A.{u}).obj M
  let G := (constantSheaf X.smallEtaleTopology A.{u}).obj M
  let E := extensionByZero j A.{u}
  let e₁ : S.X₁ ≅ E.obj F := ((extensionByZeroCompIso j (𝟙 X)).symm.app F) ≪≫
    (extensionByZeroIdIso X).app (E.obj F)
  let e₂ : S.X₂ ≅ G := (extensionByZeroIdIso X).app G
  let e := AddEquiv.ofBijective (Sheaf.H.map S.f (n + 1))
    (positiveMap_bijective S hS (rationalPointQuotient_HZero_surjective j M o h)
      (boundaryCohomology j K o h M) n)
  exact (H.mapIso e₁).addCommGroupIsoToAddEquiv.symm.trans
    (e.trans (H.mapIso e₂).addCommGroupIsoToAddEquiv)

include h in
/-- Removing that rational point kills the degree-zero compact group on a connected ambient scheme. -/
theorem zero_subsingleton [PreconnectedSpace X] (M : A.{u}) :
    Subsingleton (extensionH j M 0) := by
  apply extensionByZeroConstantHZero_subsingleton j M o
  rintro ⟨t, ht⟩
  let x := IsLocalRing.closedPoint K
  have hx : j (t x) = o x := congrArg (fun f : Spec (CommRingCat.of K) ⟶ X ↦ f x) ht
  have hr : o x ∈ Set.range j := ⟨t x, hx⟩
  rw [h] at hr
  exact hr ⟨x, rfl⟩

end
end ManuscriptAudit.OpenComplementRationalPointCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenComplementRationalPointCohomology.positiveEquiv,
      ``ManuscriptAudit.OpenComplementRationalPointCohomology.zero_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
