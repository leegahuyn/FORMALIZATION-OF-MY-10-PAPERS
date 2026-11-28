import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFreeRepresentableNaturality

/-! Inverse image on actual free pro-étale representables. -/

namespace ManuscriptAudit.ProetaleSchemeFreeRepresentable

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleInverseImage (inverseImage adjunction)
open ProetaleBaseChange (baseChange directImage)
open ProetaleMayerVietorisRepresentable (nativeFree)
open EtaleProetaleFreeRepresentable (proSections proSections_natural)
open EtaleProetaleFreeRepresentableNaturality (proMap proSections_precomp)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{1}
private abbrev P (X : Scheme.{0}) := Sheaf (Scheme.ProEt.topology X) A

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

private abbrev pullFree (W : Y.ProEt) := (inverseImage f).obj (nativeFree W)
private abbrev targetFree (W : Y.ProEt) := nativeFree ((baseChange f).obj W)

/-- The actual inverse image represents evaluation at the base-changed chart. -/
def sectionComparison (W : Y.ProEt) (F : P X) :
    (pullFree f W ⟶ F) ≃ (targetFree f W ⟶ F) :=
  (((adjunction f).homEquiv (nativeFree W) F).trans
    (proSections Y W ((directImage f A).obj F))).trans
    (proSections X ((baseChange f).obj W) F).symm

theorem sectionComparison_natural (W : Y.ProEt) {F G : P X}
    (a : pullFree f W ⟶ F) (b : F ⟶ G) :
    sectionComparison f W G (a ≫ b) = sectionComparison f W F a ≫ b := by
  let W' := (baseChange f).obj W
  let ad := adjunction f
  let Γ (T : P X) := proSections Y W ((directImage f A).obj T)
  let β (T : P X) := proSections X W' T
  let e (T : P X) := ad.homEquiv (nativeFree W) T
  apply (β G).injective
  change β G ((β G).symm (Γ G (e G (a ≫ b)))) =
    β G ((β F).symm (Γ F (e F a)) ≫ b)
  rw [Equiv.apply_symm_apply, proSections_natural, Equiv.apply_symm_apply,
    ad.homEquiv_naturality_right, proSections_natural] <;> rfl

theorem sectionComparison_precomp {U V : Y.ProEt} (g : U ⟶ V) {F : P X}
    (h : pullFree f V ⟶ F) :
    sectionComparison f U F ((inverseImage f).map (proMap Y g) ≫ h) =
      proMap X ((baseChange f).map g) ≫ sectionComparison f V F h := by
  let W := (baseChange f).obj U
  let W' := (baseChange f).obj V
  let a := adjunction f
  let F₀ := (directImage f A).obj F
  apply (proSections X W F).injective
  change proSections X W F
      ((proSections X W F).symm (proSections Y U F₀
        ((a.homEquiv (nativeFree U) F) ((inverseImage f).map (proMap Y g) ≫ h)))) =
    proSections X W F (proMap X ((baseChange f).map g) ≫
      (proSections X W' F).symm (proSections Y V F₀ ((a.homEquiv (nativeFree V) F) h)))
  rw [Equiv.apply_symm_apply, proSections_precomp, Equiv.apply_symm_apply,
    a.homEquiv_naturality_left, proSections_precomp] <;> rfl

/-- Inverse image identifies the free representable with that of the actual base change. -/
def inverseImageIso (W : Y.ProEt) : pullFree f W ≅ targetFree f W := by
  let e := sectionComparison f W
  let h : pullFree f W ⟶ targetFree f W := (e _).symm (𝟙 _)
  let i : targetFree f W ⟶ pullFree f W := e _ (𝟙 _)
  refine ⟨h, i, ?_, ?_⟩
  · apply (e (pullFree f W)).injective
    change e (pullFree f W) (h ≫ i) = i
    rw [sectionComparison_natural]
    change e (targetFree f W) ((e (targetFree f W)).symm (𝟙 _)) ≫ i = i
    simp only [Equiv.apply_symm_apply, Category.id_comp]
  · have q := sectionComparison_natural f W (𝟙 (pullFree f W)) h
    rw [Category.id_comp] at q
    change e (targetFree f W) h = i ≫ h at q
    rw [← q]
    exact (e (targetFree f W)).apply_symm_apply (𝟙 _)

theorem comparison_hom (W : Y.ProEt) :
    sectionComparison f W (targetFree f W) (inverseImageIso f W).hom =
      𝟙 (targetFree f W) := by
  exact Equiv.apply_symm_apply (sectionComparison f W _) _

theorem inverseImageIso_natural {U V : Y.ProEt} (g : U ⟶ V) :
    (inverseImage f).map (proMap Y g) ≫ (inverseImageIso f V).hom =
      (inverseImageIso f U).hom ≫ proMap X ((baseChange f).map g) := by
  apply (sectionComparison f U (targetFree f V)).injective
  rw [sectionComparison_precomp, sectionComparison_natural, comparison_hom f V,
    comparison_hom f U, Category.comp_id, Category.id_comp]

end
end ManuscriptAudit.ProetaleSchemeFreeRepresentable

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleSchemeFreeRepresentable.inverseImageIso,
      ``ManuscriptAudit.ProetaleSchemeFreeRepresentable.inverseImageIso_natural] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
